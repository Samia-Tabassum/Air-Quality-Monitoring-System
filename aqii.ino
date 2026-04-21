#include <WiFi.h>
#include <time.h>
#include <sys/time.h>
#include <math.h>
#include <Firebase_ESP_Client.h>
#include <DHT.h>
#include <Wire.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <LiquidCrystal_I2C.h>
#include "addons/TokenHelper.h"
#include "addons/RTDBHelper.h"

FirebaseData fbdo;
FirebaseAuth auth;
FirebaseConfig config;
bool signupOK = false;
#define WIFI1_SSID "REDMI K80"
#define WIFI1_PASSWORD "87654321"
#define WIFI2_SSID "SALAM"
#define WIFI2_PASSWORD "01827601501"
#define API_KEY "AIzaSyCYVoMPCueysOabUJigpw_UngcbDEeaolA"#define DATABASE_URL "https://mnm-project-99eb5-default-rtdb.asiasoutheast1.firebasedatabase.app/"
#define NTP_SERVER "pool.ntp.org"
#define GMT_OFFSET_SEC (6 * 3600)
#define DST_OFFSET_SEC 0
#define MQ135_PIN 34
#define DHT_PIN 4
#define DHT_TYPE DHT11
#define I2C_SDA 21
#define I2C_SCL 22
#define SCREEN_WIDTH 128
#define SCREEN_HEIGHT 64
#define OLED_ADDR 0x3C

Adafruit_SSD1306 display(SCREEN_WIDTH, SCREEN_HEIGHT, &Wire, -1);
LiquidCrystal_I2C lcd(0x27, 16, 2);
DHT dht(DHT_PIN, DHT_TYPE);
const uint32_t SAMPLE_MS = 2000;
const int MAX_SAMPLES = 1000;
const int HISTORY_POINTS = 20;
const float MQ_EMA_ALPHA = 0.20f;
const uint32_t CALIBRATION_MS = 60000;
bool historyLoaded = false;
float aqiBuf[MAX_SAMPLES];
int bufCount = 0;
int bufIndex = 0;
float mqRawEma = 0;
bool mqRawEmaInit = false;
float mqBaselineSum = 0;
uint32_t baselineCount = 0;
float mqBaselineFinal = 0;
bool calibrationDone = false;
uint32_t bootMs = 0;
uint32_t lastSample = 0;

float clampFloat(float v, float lo, float hi)
{
    if (v < lo) return lo;
    if (v > hi) return hi;
    return v;
}

float mapFloat(float x, float in_min, float in_max, float out_min, float out_max)
{
    if (fabs(in_max - in_min) < 0.00001f) return out_min;
    return (x - in_min) * (out_max - out_min) / (in_max - in_min) + out_min;
}

String classifyAQI(int aqiLike)
{
    if (aqiLike <= 50) return "GOOD";
    if (aqiLike <= 100) return "MODERATE";
    if (aqiLike <= 150) return "USG";
    if (aqiLike <= 200) return "UNHEALTHY";
    if (aqiLike <= 300) return "V BAD";
    return "TOXIC";
}

bool ensureTimeReady()
{
    time_t now = time(nullptr);
    return (now > 1700000000);
}

uint64_t epochMs()
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return ((uint64_t)tv.tv_sec * 1000ULL) + (tv.tv_usec / 1000ULL);
}

int ratioToAqi(float ratio)
{
    float aqi = 0;
    if (ratio <= 0.90f)
    {
        aqi = mapFloat(ratio, 0.50f, 0.90f, 0.0f, 40.0f);
    }
    else if (ratio <= 1.00f)
    {
        aqi = mapFloat(ratio, 0.90f, 1.00f, 40.0f, 60.0f);
    }
    else if (ratio <= 1.10f)
    {
        aqi = mapFloat(ratio, 1.00f, 1.10f, 60.0f, 100.0f);
    }
    else if (ratio <= 1.25f)
    {
        aqi = mapFloat(ratio, 1.10f, 1.25f, 100.0f, 150.0f);
    }
    else if (ratio <= 1.40f)
    {
        aqi = mapFloat(ratio, 1.25f, 1.40f, 150.0f, 200.0f);
    }
    else if (ratio <= 1.70f)
    {
        aqi = mapFloat(ratio, 1.40f, 1.70f, 200.0f, 300.0f);
    }
    else
    {
        aqi = mapFloat(ratio, 1.70f, 2.20f, 300.0f, 500.0f);
    }
    return (int)clampFloat(aqi, 0.0f, 500.0f);
}

float predictNext(const float *y, int n)
{
    if (n < 2) return y[0];
    double sumX = 0, sumY = 0, sumXY = 0, sumX2 = 0;
    for (int i = 0; i < n; i++)
    {
        double x = (double)i;
        double yy = (double)y[i];
        sumX += x;
        sumY += yy;
        sumXY += x * yy;
        sumX2 += x * x;
    }
    double denom = (n * sumX2 - sumX * sumX);
    if (denom == 0) return y[n - 1];
    double slope = (n * sumXY - sumX * sumY) / denom;
    double intercept = (sumY - slope * sumX) / n;
    double nextX = (double)n;
    return (float)(slope * nextX + intercept);
}

void pushSample(float v)
{
    aqiBuf[bufIndex] = v;
    bufIndex = (bufIndex + 1) % MAX_SAMPLES;
    if (bufCount < MAX_SAMPLES) bufCount++;
}

bool firebaseReadyNow()
{
    return WiFi.status() == WL_CONNECTED && Firebase.ready() && signupOK;
}

bool loadHistoryFromFirebase()
{
    if (!firebaseReadyNow())
    {
        Serial.println("Cannot load history: Firebase not ready");
        return false;
    }
    int lastSlot = -1;
    int storedCount = 0;
    if (Firebase.RTDB.getInt(&fbdo, "/meta/last_slot"))
    {
        lastSlot = fbdo.intData();
    }
    else
    {
        Serial.print("Could not read /meta/last_slot: ");
        Serial.println(fbdo.errorReason());
        return false;
    }
    if (Firebase.RTDB.getInt(&fbdo, "/meta/valid_count"))
    {
        storedCount = fbdo.intData();
    }
    else
    {
        Serial.print("Could not read /meta/valid_count: ");
        Serial.println(fbdo.errorReason());
        return false;
    }
    storedCount = min(storedCount, MAX_SAMPLES);
    int countToLoad = min(storedCount, HISTORY_POINTS);
    if (countToLoad <= 0)
    {
        Serial.println("No old AQI history found in Firebase");
        return false;
    }
    bufCount = 0;
    bufIndex = 0;
    int startSlot = (lastSlot - countToLoad + 1 + MAX_SAMPLES) % MAX_SAMPLES;
    for (int i = 0; i < countToLoad; i++)
    {
        int slot = (startSlot + i) % MAX_SAMPLES;
        char path[64];
        snprintf(path, sizeof(path), "/readings/slot_%03d/aqi_like", slot);
        if (Firebase.RTDB.getInt(&fbdo, path))
        {
            int oldAqi = fbdo.intData();
            pushSample((float)oldAqi);
            Serial.print("Loaded slot ");
            Serial.print(slot);
            Serial.print(" = ");
            Serial.println(oldAqi);
        }
        else
        {
            Serial.print("Failed to read slot ");
            Serial.print(slot);
            Serial.print(": ");
            Serial.println(fbdo.errorReason());
        }
    }
    Serial.print("History restored. Local bufCount = ");
    Serial.println(bufCount);
    return (bufCount > 0);
}

float predictFromBuffer(float fallbackValue)
{
    if (bufCount < 2) return fallbackValue;
    static float ordered[MAX_SAMPLES];
    int startIdx = (bufIndex - bufCount + MAX_SAMPLES) % MAX_SAMPLES;
    for (int i = 0; i < bufCount; i++)
    {
        ordered[i] = aqiBuf[(startIdx + i) % MAX_SAMPLES];
    }
    float p = predictNext(ordered, bufCount);
    return clampFloat(p, 0.0f, 500.0f);
}

void drawOLEDCalibration(int mqRaw, uint32_t secondsLeft, bool wifiOk)
{
    display.clearDisplay();
    display.setTextSize(1);
    display.setTextColor(SSD1306_WHITE);
    display.setCursor(0, 0);
    display.println("MQ135 CALIBRATING");
    display.setCursor(0, 12);
    display.print("Raw: ");
    display.println(mqRaw);
    display.setCursor(0, 24);
    display.print("Wait: ");
    display.print(secondsLeft);
    display.println("s");
    display.setCursor(0, 36);
    display.print("WiFi: ");
    display.println(wifiOk ? "OK" : "LOST");
    display.setCursor(0, 48);
    display.println("AQI paused");
    display.display();
}

void drawOLEDLive(
    int mqRaw,
    float baseline,
    int aqiLike,
    const String &qual,
    float t,
    float h,
    float pred,
    bool timeOk,
    bool wifiOk,
    bool writeOk,
    bool readOk
)
{
    display.clearDisplay();
    display.setTextSize(1);
    display.setTextColor(SSD1306_WHITE);
    display.setCursor(0, 0);
    display.print("AQI:");
    display.print(aqiLike);
    display.print(" ");
    display.println(qual);
    display.setCursor(0, 10);
    display.print("Raw:");
    display.print(mqRaw);
    display.print(" B:");
    display.println((int)baseline);
    display.setCursor(0, 20);
    display.print("T:");
    if (isnan(t)) display.print("--");
    else display.print(t, 1);
    display.print("C H:");
    if (isnan(h)) display.print("--");
    else display.print(h, 0);
    display.println("%");
    display.setCursor(0, 30);
    display.print("Pred:");
    display.println(pred, 1);
    display.setCursor(0, 40);
    display.print("WiFi:");
    display.print(wifiOk ? "OK" : "LOST");
    display.print(" Time:");
    display.println(timeOk ? "OK" : "WAIT");
    display.setCursor(0, 50);
    display.print("FB W:");
    display.print(writeOk ? "OK" : "NO");
    display.print(" R:");
    display.println(readOk ? "OK" : "NO");
    display.display();
}

void showLCDCalibration(int mqRaw, uint32_t secondsLeft)
{
    lcd.clear();
    lcd.setCursor(0, 0);
    lcd.print("CAL MQ135");
    lcd.setCursor(0, 1);
    lcd.print("R:");
    lcd.print(mqRaw);
    lcd.print(" ");
    lcd.print(secondsLeft);
    lcd.print("s");
}

String shortStatus(const String &quality)
{
    if (quality == "GOOD") return "GD";
    if (quality == "MODERATE") return "MD";
    if (quality == "USG") return "US";
    if (quality == "UNHEALTHY") return "UH";
    if (quality == "V BAD") return "VB";
    if (quality == "TOXIC") return "TX";
    return "--";
}

void showLCDLive(int aqiLike, float predicted, float t, float h, const String &quality, bool dhtOk)
{
    lcd.clear();
// Line 1: AQI + Predicted AQI + Status
    lcd.setCursor(0, 0);
    lcd.print("A");
    lcd.print(aqiLike);
    lcd.print(" P");
    lcd.print((int)predicted);
    lcd.print(" ");
    lcd.print(shortStatus(quality));
// Clear leftovers on line 1
    lcd.print(" ");
// Line 2: Temp + Humidity
    lcd.setCursor(0, 1);
    if (dhtOk)
    {
        lcd.print("T");
        lcd.print(t, 1);
        lcd.print(" H");
        lcd.print((int)h);
        lcd.print("%");
    }
    else
    {
        lcd.print("T--.- H--%");
    }// Clear leftovers on line 2
    lcd.print(" ");
}

bool tryWiFi(const char* ssid, const char* password, const char* label)
{
    WiFi.disconnect(true, true);
    delay(500);
    WiFi.mode(WIFI_STA);
    WiFi.begin(ssid, password);
    Serial.print("Connecting to ");
    Serial.print(label);
    Serial.print(" : ");
    uint32_t start = millis();
    while (WiFi.status() != WL_CONNECTED && millis() - start < 20000)
    {
        delay(300);
        Serial.print(".");
    }
    Serial.println();
    if (WiFi.status() == WL_CONNECTED)
    {
        Serial.print("Connected to ");
        Serial.print(label);
        Serial.print(". IP: ");
        Serial.println(WiFi.localIP());
        return true;
    }
    return false;
}

void connectWiFi()
{
    if (tryWiFi(WIFI1_SSID, WIFI1_PASSWORD, "wifi 1"))
    {
        return;
    }
    Serial.println("failed to connect wifi 1");
    if (tryWiFi(WIFI2_SSID, WIFI2_PASSWORD, "wifi 2"))
    {
        return;
    }
    Serial.println("failed to connect wifi 2");
}

void setup()
{
    Serial.begin(115200);
    delay(300);
    bootMs = millis();
    analogReadResolution(12);
    analogSetAttenuation(ADC_11db);
    Wire.begin(I2C_SDA, I2C_SCL);
    lcd.init();
    lcd.backlight();
    lcd.clear();
    lcd.setCursor(0, 0);
    lcd.print("Starting...");
    if (!display.begin(SSD1306_SWITCHCAPVCC, OLED_ADDR))
    {
        Serial.println("SSD1306 failed. Check wiring / address 0x3C or 0x3D.");
        while (true) delay(1000);
    }
    display.clearDisplay();
    display.setTextSize(1);
    display.setTextColor(SSD1306_WHITE);
    display.setCursor(0, 0);
    display.println("Booting...");
    display.display();
    dht.begin();
    connectWiFi();
    configTime(GMT_OFFSET_SEC, DST_OFFSET_SEC, NTP_SERVER);
    config.api_key = API_KEY;
    config.database_url = DATABASE_URL;
    config.token_status_callback = tokenStatusCallback;
// Requires Firebase Console -> Authentication -> Sign-in method -> Anonymous enabled
    if (Firebase.signUp(&config, &auth, "", ""))
    {
        Serial.println("Firebase signup OK");
        signupOK = true;
    }
    else
    {
        Serial.print("Firebase signup failed: ");
        Serial.println(config.signer.signupError.message.c_str());
    }
    Firebase.begin(&config, &auth);
    Firebase.reconnectWiFi(true);
    display.clearDisplay();
    display.setCursor(0, 0);
    display.println("Setup done");
    display.display();
    lcd.clear();
    lcd.setCursor(0, 0);
    lcd.print("Setup done");
    delay(1000);
}

void loop()
{
    if (millis() - lastSample < SAMPLE_MS) return;
    lastSample = millis();
    if (WiFi.status() != WL_CONNECTED)
    {
        Serial.println("WiFi lost, reconnecting...");
        connectWiFi();
    }
    bool wifiOk = (WiFi.status() == WL_CONNECTED);
    int mqRaw = analogRead(MQ135_PIN);
    float t = dht.readTemperature();
    float h = dht.readHumidity();
    bool dhtOk = !(isnan(t) || isnan(h));
    if (!mqRawEmaInit)
    {
        mqRawEma = mqRaw;
        mqRawEmaInit = true;
    }
    else
    {
        mqRawEma = MQ_EMA_ALPHA * mqRaw + (1.0f - MQ_EMA_ALPHA) * mqRawEma;
    }
    if (!calibrationDone)
    {
        mqBaselineSum += mqRawEma;
        baselineCount++;
        uint32_t elapsed = millis() - bootMs;
        if (elapsed >= CALIBRATION_MS)
        {
            mqBaselineFinal = (baselineCount > 0) ? (mqBaselineSum / baselineCount) : mqRawEma;
            calibrationDone = true;
            Serial.println("Calibration complete.");
            Serial.print("Baseline = ");
            Serial.println(mqBaselineFinal, 2);
        }
        else
        {
            uint32_t secondsLeft = (CALIBRATION_MS - elapsed) / 1000UL;
            Serial.print("Calibrating... raw=");
            Serial.print(mqRaw);
            Serial.print(" ema=");
            Serial.print(mqRawEma, 1);
            Serial.print(" left=");
            Serial.print(secondsLeft);
            Serial.println("s");
            drawOLEDCalibration(mqRaw, secondsLeft, wifiOk);
            showLCDCalibration(mqRaw, secondsLeft);
            if (firebaseReadyNow())
            {
                FirebaseJson statusJson;
                statusJson.set("state", "calibrating");
                statusJson.set("raw", mqRaw);
                statusJson.set("raw_ema", mqRawEma);
                statusJson.set("seconds_left", (int)secondsLeft);
                statusJson.set("wifi_connected", wifiOk);
                statusJson.set("ip", WiFi.localIP().toString());
                if (Firebase.RTDB.setJSON(&fbdo, "/device_status", &statusJson))
                {
                    Serial.println("Firebase status write OK (calibrating)");
                }
                else
                {
                    Serial.print("Firebase status write FAIL: ");
                    Serial.println(fbdo.errorReason());
                }
            }
            return;
        }
    }
    float baselineForRatio = (mqBaselineFinal > 1.0f) ? mqBaselineFinal : 1.0f;
    float ratio = mqRawEma / baselineForRatio;
    int aqiLike = ratioToAqi(ratio);
    String quality = classifyAQI(aqiLike);
    if (!historyLoaded && firebaseReadyNow())
    {
        if (loadHistoryFromFirebase())
        {
            Serial.println("Firebase history loaded successfully");
        }
        else
        {
            Serial.println("No previous Firebase history loaded");
        }
        historyLoaded = true;
    }
    pushSample((float)aqiLike);
    float predicted = predictFromBuffer((float)aqiLike);
    bool timeOk = ensureTimeReady();
    uint64_t ts = timeOk ? epochMs() : (uint64_t)millis();
    bool writeOk = false;
    bool readOk = false;
    if (firebaseReadyNow())
    {
        int slot = (bufIndex - 1 + MAX_SAMPLES) % MAX_SAMPLES;
        char slotPath[64];
        snprintf(slotPath, sizeof(slotPath), "/readings/slot_%03d", slot);
        FirebaseJson rec;
        rec.set("ts", (double)ts);
        rec.set("aqi_like", aqiLike);
        rec.set("quality", quality);
        rec.set("pred", predicted);
        rec.set("mq_raw", mqRaw);
        rec.set("mq_raw_ema", mqRawEma);
        rec.set("mq_baseline", mqBaselineFinal);
        rec.set("ratio", ratio);
        rec.set("wifi_connected", wifiOk);
        rec.set("ip", WiFi.localIP().toString());
        if (dhtOk)
        {
            rec.set("temp", t);
            rec.set("hum", h);
        }
        FirebaseJson latest;
        latest.set("ts", (double)ts);
        latest.set("aqi_like", aqiLike);
        latest.set("quality", quality);
        latest.set("pred", predicted);
        latest.set("mq_raw", mqRaw);
        latest.set("mq_raw_ema", mqRawEma);
        latest.set("mq_baseline", mqBaselineFinal);
        latest.set("ratio", ratio);
        latest.set("wifi_connected", wifiOk);
        latest.set("ip", WiFi.localIP().toString());
        if (dhtOk)
        {
            latest.set("temp", t);
            latest.set("hum", h);
        }
        bool slotWriteOk = Firebase.RTDB.setJSON(&fbdo, slotPath, &rec);
        if (!slotWriteOk)
        {
            Serial.print("Firebase slot write FAIL: ");
            Serial.println(fbdo.errorReason());
        }
        bool latestWriteOk = Firebase.RTDB.setJSON(&fbdo, "/latest", &latest);
        if (!latestWriteOk)
        {
            Serial.print("Firebase latest write FAIL: ");
            Serial.println(fbdo.errorReason());
        }
        bool lastSlotOk = Firebase.RTDB.setInt(&fbdo, "/meta/last_slot", slot);
        if (!lastSlotOk)
        {
            Serial.print("Firebase meta last_slot FAIL: ");
            Serial.println(fbdo.errorReason());
        }
        bool countOk = Firebase.RTDB.setInt(&fbdo, "/meta/valid_count", bufCount);
        if (!countOk)
        {
            Serial.print("Firebase meta valid_count FAIL: ");
            Serial.println(fbdo.errorReason());
        }
        FirebaseJson statusJson;
        statusJson.set("state", "running");
        statusJson.set("last_ts", (double)ts);
        statusJson.set("wifi_connected", wifiOk);
        statusJson.set("ip", WiFi.localIP().toString());
        statusJson.set("last_aqi_like", aqiLike);
        statusJson.set("last_quality", quality);
        bool statusWriteOk = Firebase.RTDB.setJSON(&fbdo, "/device_status", &statusJson);
        if (!statusWriteOk)
        {
            Serial.print("Firebase status write FAIL: ");
            Serial.println(fbdo.errorReason());
        }
        writeOk = slotWriteOk && latestWriteOk && lastSlotOk && countOk && statusWriteOk;
        if (Firebase.RTDB.getJSON(&fbdo, "/latest"))
        {
            readOk = true;
            Serial.println("Firebase READ /latest OK");
            Serial.println("Read payload:");
            Serial.println(fbdo.payload());
        }
        else
        {
            Serial.print("Firebase READ /latest FAIL: ");
            Serial.println(fbdo.errorReason());
        }
    }
    else
    {
        Serial.println("Firebase not ready, skipping write/read");
    }
    Serial.println("--------------------------------------------------");
    Serial.print("WiFi: ");
    Serial.println(wifiOk ? "CONNECTED" : "DISCONNECTED");
    Serial.print("MQ raw: ");
    Serial.println(mqRaw);
    Serial.print("MQ raw EMA: ");
    Serial.println(mqRawEma, 2);
    Serial.print("Baseline: ");
    Serial.println(mqBaselineFinal, 2);
    Serial.print("Ratio raw/baseline: ");
    Serial.println(ratio, 3);
    Serial.print("AQI-like: ");
    Serial.print(aqiLike);
    Serial.print(" ");
    Serial.println(quality);
    if (dhtOk)
    {
        Serial.print("Temp: ");
        Serial.print(t, 1);
        Serial.print(" C, Hum: ");
        Serial.print(h, 1);
        Serial.println(" %");
    }
    else
    {
        Serial.println("DHT read failed");
    }
    Serial.print("Predicted next AQI-like: ");
    Serial.println(predicted, 1);
    Serial.print("Firebase WRITE status: ");
    Serial.println(writeOk ? "OK" : "FAIL");
    Serial.print("Firebase READ status: ");
    Serial.println(readOk ? "OK" : "FAIL");
    drawOLEDLive(
        mqRaw,
        mqBaselineFinal,
        aqiLike,
        quality,
        t,
        h,
        predicted,timeOk,
        wifiOk,
        writeOk,
        readOk
    );
    showLCDLive(aqiLike, predicted, t, h, quality, dhtOk);
}
