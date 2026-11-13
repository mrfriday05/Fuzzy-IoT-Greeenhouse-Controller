/**
 * Smart Garden Controller - ESP32
 * Implements fuzzy-logic based environment control, diurnal habitat simulation,
 * UI for plant selection, Wi-Fi data logging, and comprehensive hardware safety.
 */

#include <WiFi.h>
#include <Wire.h>
#include <LiquidCrystal_I2C.h>
#include <RTClib.h>
#include <DHT.h>
#include <math.h>

// ==========================================
// 1. PIN DEFINITIONS (Matching Appendix Tables)
// ==========================================
// Analog Sensors
#define PIN_SOIL          32 // Capacitive Soil Sensor
#define PIN_TDS           33 // TDS Sensor
#define PIN_LDR_OUT1      35 // Outside Light 1
#define PIN_LDR_OUT2      34 // Outside Light 2
#define PIN_LDR_IN1       39 // Inside Light 1
#define PIN_LDR_IN2       36 // Inside Light 2

// Digital Inputs
#define PIN_DHT           4  // DHT11 Temp & Humidity
#define PIN_BTN_UP        16 // UI Button Up
#define PIN_BTN_DOWN      17 // UI Button Down
#define PIN_BTN_SELECT    18 // UI Button Select

// PWM / Analog Outputs
#define PIN_LED_PWM       25 // N-Channel MOSFET for LED Strip
#define PIN_SHADE_ENA     27 // L298N ENA (Shade Speed)
#define PIN_FAN_ENB       13 // L298N ENB (Fan Speed)

// Digital Outputs (Relays & Motor Directions)
#define PIN_RELAY_HEATER  19 // Relay CH1 (Active LOW)
#define PIN_RELAY_WATER   23 // Relay CH2 (Active LOW)
#define PIN_RELAY_FERT    5  // Relay CH3 (Active LOW)
#define PIN_RELAY_MIST    12 // Relay CH4 (Active LOW)
#define PIN_SHADE_IN1     14 // Motor Driver IN1
#define PIN_SHADE_IN2     15 // Motor Driver IN2
#define PIN_FAN_IN3       2  // Motor Driver IN3
#define PIN_FAN_IN4       0  // Motor Driver IN4

// ==========================================
// 2. CONSTANTS & TIMEOUTS
// ==========================================
#define DHTTYPE DHT11
DHT dht(PIN_DHT, DHTTYPE);
LiquidCrystal_I2C lcd(0x27, 20, 4); // 20x4 I2C LCD
RTC_DS1307 rtc;

const char* ssid = "YOUR_WIFI_SSID";
const char* password = "YOUR_WIFI_PASSWORD";

// System Delays (in milliseconds)
const unsigned long LOG_INTERVAL = 600000; 
const unsigned long WATER_ABSORB_DELAY = 15 * 60 * 1000; // 15 mins for physical absorption
const unsigned long WATER_RAMP_DELAY = 30 * 60 * 1000;   // 30 mins before belief ramps down
const unsigned long FERT_ABSORB_DELAY = 30 * 60 * 1000;  // 30 mins for physical absorption
const unsigned long FERT_RAMP_DELAY = 60 * 60 * 1000;    // 1 hour before belief ramps down

// Error Timeouts
const unsigned long HEATER_TIMEOUT = 30 * 60 * 1000; // 30 mins max continuous run
const unsigned long FAN_TIMEOUT = 30 * 60 * 1000;    // 30 mins max continuous run
const unsigned long MIST_TIMEOUT = 20 * 60 * 1000;   // 20 mins max continuous run
const unsigned long SHADE_TIMEOUT = 60 * 1000;       // 60 secs max motor travel time
const unsigned long LED_TIMEOUT = 10 * 1000;         // 10 secs to detect brightness

// ==========================================
// 3. STATE & ERROR TRACKING VARIABLES
// ==========================================
bool err[10] = {false}; // Array to hold ERR-01 to ERR-10 states

// Action Timers & Pre-action states for validation
unsigned long lastWaterTime = 0, lastFertTime = 0;
unsigned long heaterStartTime = 0, fanStartTime = 0;
unsigned long mistStartTime = 0, shadeStartTime = 0, ledStartTime = 0;
unsigned long lastLogTime = 0;

float preWaterMoisture = 0.0, preFertTDS = 0.0;
float preHeatTemp = 0.0, preFanTemp = 0.0, preFanHum = 0.0;
float preMistHum = 0.0;
int preShadeLight = 0;

// Active state flags
bool isWaitingWaterAbsorb = false, isWaitingFertAbsorb = false;
bool isHeating = false, isFanning = false, isMisting = false;
bool isShadeMoving = false, isLedOn = false;

int uiScreen = 0; // 0=Stats, 1=Errors, 2=Plant Selection
int selectedPlantIndex = 0;

// ==========================================
// 4. PLANT LIBRARY (Preloaded Profiles)
// ==========================================
struct PlantProfile {
    String name;
    float temp_avg, temp_var;     // Temperature target & variation
    float hum_avg, hum_var;       // Humidity target & variation
    float max_sunshine;           // Peak daylight requirement
    float ideal_moist, ideal_tds; // Soil targets
};

const int NUM_PLANTS = 3;
PlantProfile plantLibrary[NUM_PLANTS] = {
    {"Tomato", 22.0, 5.0, 60.0, 15.0, 800.0, 60.0, 1200.0},
    {"Orchid", 24.0, 3.0, 75.0, 10.0, 400.0, 50.0, 400.0},
    {"Lettuce",18.0, 4.0, 65.0, 10.0, 600.0, 70.0, 800.0}
};
PlantProfile activePlant = plantLibrary[0];

// ==========================================
// 5. MATH & FUZZY LOGIC HELPERS
// ==========================================

// Calculate weighted average for defuzzification
float defuzzify(float mu[], float P[], int n) {
    float num = 0, den = 0;
    for (int i = 0; i < n; i++) { num += (mu[i] * P[i]); den += P[i]; }
    return (den == 0) ? 0 : (num / den);
}

// Simulates a sinusoidal day-night curve for target illumination
float calculateRequiredIllumination(float currentHour, float max_sunshine) {
    float h_start = 12.0 - 6.0, h_end = 12.0 + 6.0; // Assume 12hr photoperiod around solar noon
    if (currentHour > h_start && currentHour < h_end) {
        return max_sunshine * sin(PI * (currentHour - h_start) / (h_end - h_start));
    }
    return 0.0;
}

// Modulates target Temp/Hum based on time of day (cosine shifted by 2 hours)
float calculateTargetValue(float avg, float var, float currentHour, bool isTemp) {
    float sign = isTemp ? 1.0 : -1.0; // Temp peaks at day, Hum peaks at night
    return avg + (sign * var * cos((2.0 * PI * (currentHour - 14.0)) / 24.0));
}

// Calculates Triangular Belief Probability
float getBeliefProbability(float value, float peak, float width) {
    float dist = abs(value - peak);
    return (dist > width) ? 0.0 : 1.0 - (dist / width);
}

// ==========================================
// 6. SETUP ROUTINE
// ==========================================
void setup() {
    Serial.begin(115200);

    // Init UI Buttons
    pinMode(PIN_BTN_UP, INPUT_PULLUP); 
    pinMode(PIN_BTN_DOWN, INPUT_PULLUP); 
    pinMode(PIN_BTN_SELECT, INPUT_PULLUP);

    // Init Outputs
    pinMode(PIN_LED_PWM, OUTPUT); 
    pinMode(PIN_SHADE_ENA, OUTPUT); 
    pinMode(PIN_FAN_ENB, OUTPUT);
    pinMode(PIN_RELAY_HEATER, OUTPUT); 
    pinMode(PIN_RELAY_WATER, OUTPUT); 
    pinMode(PIN_RELAY_FERT, OUTPUT); 
    pinMode(PIN_RELAY_MIST, OUTPUT);
    pinMode(PIN_SHADE_IN1, OUTPUT); pinMode(PIN_SHADE_IN2, OUTPUT); 
    pinMode(PIN_FAN_IN3, OUTPUT); pinMode(PIN_FAN_IN4, OUTPUT);

    // Set default Relays to OFF (Active LOW hardware)
    digitalWrite(PIN_RELAY_HEATER, HIGH); digitalWrite(PIN_RELAY_WATER, HIGH);
    digitalWrite(PIN_RELAY_FERT, HIGH); digitalWrite(PIN_RELAY_MIST, HIGH);

    // Initialize I2C, Sensors, and LCD
    dht.begin(); 
    Wire.begin(21, 22); 
    lcd.init(); 
    lcd.backlight();
    
    // Check RTC
    if (!rtc.begin() || !rtc.isrunning()) err[2] = true; // ERR-03

    // Connect WiFi
    WiFi.begin(ssid, password);
}

// ==========================================
// 7. MAIN LOOP
// ==========================================
void loop() {
    unsigned long currentMillis = millis();
    float currentHour = err[2] ? 12.0 : (rtc.now().hour() + (rtc.now().minute() / 60.0));

    // --- A. READ & PROCESS SENSORS ---
    float temp = dht.readTemperature();
    float hum = dht.readHumidity();
    
    // Average LDRs for robustness
    int lightOutside = (analogRead(PIN_LDR_OUT1) + analogRead(PIN_LDR_OUT2)) / 2;
    int lightInside = (analogRead(PIN_LDR_IN1) + analogRead(PIN_LDR_IN2)) / 2;
    
    // Map raw capacitive reading to percentage (Calibrated bounds)
    float soilMoist = map(analogRead(PIN_SOIL), 3500, 1000, 0, 100); 
    if (soilMoist < 0) soilMoist = 0; if (soilMoist > 100) soilMoist = 100;

    // Process TDS based on new logic: Divide by soil moisture to normalize EC
    float rawTds = analogRead(PIN_TDS);
    float soilFraction = max(5.0f, soilMoist) / 100.0f; // Guard against division by zero
    float adjustedTDS = rawTds / soilFraction; 

    // --- B. HARDWARE ERROR VALIDATION ---
    // ERR-01: DHT11 fault
    err[0] = (isnan(temp) || isnan(hum) || temp < -10.0 || temp > 60.0);
    // ERR-02: Soil Sensor fault
    err[1] = (analogRead(PIN_SOIL) <= 10 || analogRead(PIN_SOIL) >= 4090);

    // ERR-04: Water Pump Reaction
    if (isWaitingWaterAbsorb && (currentMillis - lastWaterTime > WATER_ABSORB_DELAY)) {
        if (soilMoist < preWaterMoisture + 2.0) err[3] = true; 
        isWaitingWaterAbsorb = false; 
    }
    // ERR-06: Fertilizer Pump Reaction
    if (isWaitingFertAbsorb && (currentMillis - lastFertTime > FERT_ABSORB_DELAY)) {
        if (adjustedTDS < preFertTDS + 20.0) err[5] = true;
        isWaitingFertAbsorb = false;
    }
    // ERR-05: Heater Reaction
    if (isHeating && (currentMillis - heaterStartTime > HEATER_TIMEOUT)) {
        if (temp < preHeatTemp + 1.0) err[4] = true;
        isHeating = false; 
    }
    // ERR-07: Fan/Ventilation Reaction
    if (isFanning && (currentMillis - fanStartTime > FAN_TIMEOUT)) {
        if (temp >= preFanTemp && hum >= preFanHum) err[6] = true;
        isFanning = false;
    }
    // ERR-08: Mist Maker Reaction
    if (isMisting && (currentMillis - mistStartTime > MIST_TIMEOUT)) {
        if (hum < preMistHum + 2.0) err[7] = true;
        isMisting = false;
    }
    // ERR-09: Shade Motor Jam
    if (isShadeMoving && (currentMillis - shadeStartTime > SHADE_TIMEOUT)) {
        if (abs(lightInside - preShadeLight) < 10) err[8] = true;
        isShadeMoving = false;
    }
    // ERR-10: LED Light Failure
    if (isLedOn && (currentMillis - ledStartTime > LED_TIMEOUT)) {
        if (lightInside < 50) err[9] = true; 
        isLedOn = false;
    }

    // Refresh LCD Interface
    handleUI(temp, hum, soilMoist, adjustedTDS);

    // --- C. ILLUMINATION CONTROL ---
    float targetIllumination = calculateRequiredIllumination(currentHour, activePlant.max_sunshine);
    float probTooDark = (lightInside < targetIllumination - 50) ? min(1.0f, (targetIllumination - 50 - lightInside) / 200.0f) : 0;
    float probTooBright = (lightInside > targetIllumination + 50) ? min(1.0f, (lightInside - (targetIllumination + 50)) / 200.0f) : 0;
    
    bool isDarkOutside = (lightOutside < 100);
    bool shouldShadeMove = false;
    bool shouldLedBeOn = false;

    // Logic: Shade down if too bright. Shade up if too dark. LED on if too dark and shade is fully up.
    if (probTooBright > 0 && !isDarkOutside && !err[8]) {
        digitalWrite(PIN_SHADE_IN1, HIGH); digitalWrite(PIN_SHADE_IN2, LOW);
        analogWrite(PIN_SHADE_ENA, probTooBright * 255); 
        analogWrite(PIN_LED_PWM, 0); 
        shouldShadeMove = true;
    } else if (probTooDark > 0) {
        if (!err[8]) {
            digitalWrite(PIN_SHADE_IN1, LOW); digitalWrite(PIN_SHADE_IN2, HIGH);
            analogWrite(PIN_SHADE_ENA, 255); // Max speed to open shade
            shouldShadeMove = true;
        }
        if (!err[9]) {
            // Apply minimum threshold to avoid flicker (e.g., min PWM 50)
            int ledPwm = max(50.0f, probTooDark * 255); 
            analogWrite(PIN_LED_PWM, ledPwm);
            shouldLedBeOn = true;
        }
    } else {
        analogWrite(PIN_SHADE_ENA, 0); 
        analogWrite(PIN_LED_PWM, 0);
    }

    // Update Shade/LED tracking for error detection
    if (shouldShadeMove && !isShadeMoving) { isShadeMoving = true; shadeStartTime = currentMillis; preShadeLight = lightInside; } 
    else if (!shouldShadeMove) { isShadeMoving = false; }
    
    if (shouldLedBeOn && !isLedOn) { isLedOn = true; ledStartTime = currentMillis; } 
    else if (!shouldLedBeOn) { isLedOn = false; }


    // --- D. TEMPERATURE & HUMIDITY CONTROL ---
    float targetTemp = calculateTargetValue(activePlant.temp_avg, activePlant.temp_var, currentHour, true);
    float targetHum = calculateTargetValue(activePlant.hum_avg, activePlant.hum_var, currentHour, false);

    float probTempLow = getBeliefProbability(temp, targetTemp - 5, 5);
    float probTempHigh = getBeliefProbability(temp, targetTemp + 5, 5);
    float probHumLow = getBeliefProbability(hum, targetHum - 10, 10);
    float probHumHigh = getBeliefProbability(hum, targetHum + 10, 10);

    // Defuzzify Fan: High temp/hum applies positive weight (+1), Low temp/hum applies negative weight (-1)
    float fanMu[4] = {1.0, 1.0, -1.0, -1.0}; 
    float fanP[4] = {probTempHigh, probHumHigh, probTempLow, probHumLow};
    float fanAction = defuzzify(fanMu, fanP, 4);
    
    if (err[0]) { // ERR-01: DHT Fail -> Lockout air actuators
        analogWrite(PIN_FAN_ENB, 0);
        digitalWrite(PIN_RELAY_HEATER, HIGH); digitalWrite(PIN_RELAY_MIST, HIGH);
        isHeating = false; isFanning = false; isMisting = false;
    } else {
        // VENTILATOR
        bool needFan = (fanAction > 0.3) && !err[6];
        if (needFan) {
            digitalWrite(PIN_FAN_IN3, HIGH); digitalWrite(PIN_FAN_IN4, LOW);
            analogWrite(PIN_FAN_ENB, fanAction * 255);
            if (!isFanning) { isFanning = true; fanStartTime = currentMillis; preFanTemp = temp; preFanHum = hum; }
        } else {
            analogWrite(PIN_FAN_ENB, 0); isFanning = false;
        }

        // HEATER
        bool needHeat = (probTempLow > 0.3) && !err[4];
        if (needHeat && !isHeating) { isHeating = true; heaterStartTime = currentMillis; preHeatTemp = temp; }
        else if (!needHeat) { isHeating = false; }
        digitalWrite(PIN_RELAY_HEATER, needHeat ? LOW : HIGH);

        // MIST MAKER
        bool needMist = (probHumLow > 0.3) && !err[7];
        if (needMist && !isMisting) { isMisting = true; mistStartTime = currentMillis; preMistHum = hum; }
        else if (!needMist) { isMisting = false; }
        digitalWrite(PIN_RELAY_MIST, needMist ? LOW : HIGH);
    }

    // --- E. IRRIGATION & FERTILIZATION ---
    unsigned long timeSinceWater = currentMillis - lastWaterTime;
    float waterAction = defuzzify((float[]){-1,1,1}, (float[]){
        (timeSinceWater < WATER_RAMP_DELAY) ? 1.0f : 0.0f,
        (timeSinceWater > WATER_RAMP_DELAY) ? min(1.0f, (float)(timeSinceWater - WATER_RAMP_DELAY) / (12 * 3600000.0f)) : 0.0f,
        (soilMoist < activePlant.ideal_moist) ? (activePlant.ideal_moist - soilMoist) / activePlant.ideal_moist : 0.0f
    }, 3);

    // Fire water pump if output is positive, delays have passed, and no hardware faults exist
    if (waterAction > 0.5 && timeSinceWater > WATER_ABSORB_DELAY && !err[3] && !err[1]) {
        preWaterMoisture = soilMoist;
        digitalWrite(PIN_RELAY_WATER, LOW); delay(10000); digitalWrite(PIN_RELAY_WATER, HIGH); // 10s pulse
        lastWaterTime = millis(); isWaitingWaterAbsorb = true;
    }

    unsigned long timeSinceFert = currentMillis - lastFertTime;
    float fertAction = defuzzify((float[]){-1,1,1}, (float[]){
        (timeSinceFert < FERT_RAMP_DELAY) ? 1.0f : 0.0f,
        (timeSinceFert > FERT_RAMP_DELAY) ? 0.5f : 0.0f,
        (adjustedTDS < activePlant.ideal_tds) ? 1.0f : 0.0f
    }, 3);

    if (fertAction > 0.5 && timeSinceFert > FERT_ABSORB_DELAY && !err[5] && !err[1]) {
        preFertTDS = adjustedTDS; 
        digitalWrite(PIN_RELAY_FERT, LOW); delay(5000); digitalWrite(PIN_RELAY_FERT, HIGH); // 5s pulse
        lastFertTime = millis(); isWaitingFertAbsorb = true;
    }
    
    // WiFi Telemetry Stub
    if (currentMillis - lastLogTime > LOG_INTERVAL && WiFi.status() == WL_CONNECTED) {
        // Send telemetry payload to remote server here
        lastLogTime = currentMillis;
    }
}

// ==========================================
// 8. USER INTERFACE
// ==========================================
void handleUI(float temp, float hum, float soil, float tds) {
    if (digitalRead(PIN_BTN_UP) == LOW || digitalRead(PIN_BTN_DOWN) == LOW || digitalRead(PIN_BTN_SELECT) == LOW) delay(150); // Debounce
    
    if (digitalRead(PIN_BTN_SELECT) == LOW) { uiScreen = (uiScreen + 1) % 3; lcd.clear(); }

    if (uiScreen == 0) {
        // Screen 0: Live Statistics
        lcd.setCursor(0, 0); lcd.print(activePlant.name);
        lcd.setCursor(0, 1); lcd.print("T:"); lcd.print(temp, 1); lcd.print("C H:"); lcd.print(hum, 1); lcd.print("%");
        lcd.setCursor(0, 2); lcd.print("Soil:"); lcd.print(soil, 0); lcd.print("% EC:"); lcd.print(tds, 0);
        
        bool anyErr = false; for(int i=0; i<10; i++){ if(err[i]) anyErr = true; }
        if (anyErr) {
            lcd.setCursor(0, 3); lcd.print("! CHECK DIAGNOSTICS !");
        } else {
            lcd.setCursor(0, 3); lcd.print("System Status: OK    ");
        }
    } 
    else if (uiScreen == 1) {
        // Screen 1: Diagnostics & Error Reporting
        lcd.setCursor(0, 0); lcd.print("--- DIAGNOSTICS --- ");
        
        if (err[0]) { lcd.setCursor(0, 1); lcd.print("E01: DHT FAULT      "); }
        else if (err[1]) { lcd.setCursor(0, 1); lcd.print("E02: SOIL SENS FAULT"); }
        else if (err[2]) { lcd.setCursor(0, 1); lcd.print("E03: RTC FAILURE    "); }
        else { lcd.setCursor(0, 1); lcd.print("SENSORS: OK         "); }
        
        if (err[3]) { lcd.setCursor(0, 2); lcd.print("E04: WATER PUMP DRY "); }
        else if (err[4]) { lcd.setCursor(0, 2); lcd.print("E05: HEATER FAIL    "); }
        else if (err[5]) { lcd.setCursor(0, 2); lcd.print("E06: FERT PUMP DRY  "); }
        else { lcd.setCursor(0, 2); lcd.print("PUMPS/HEAT: OK      "); }

        if (err[6]) { lcd.setCursor(0, 3); lcd.print("E07: FAN JAM/FAIL   "); }
        else if (err[7]) { lcd.setCursor(0, 3); lcd.print("E08: MIST FAIL      "); }
        else if (err[8]) { lcd.setCursor(0, 3); lcd.print("E09: SHADE MOTOR JAM"); }
        else if (err[9]) { lcd.setCursor(0, 3); lcd.print("E10: LED LIGHT FAIL "); }
        else { lcd.setCursor(0, 3); lcd.print("AIR/LIGHT ACT: OK   "); }
    }
    else if (uiScreen == 2) {
        // Screen 2: Plant Selection
        if (digitalRead(PIN_BTN_UP) == LOW) selectedPlantIndex = (selectedPlantIndex + 1) % NUM_PLANTS;
        if (digitalRead(PIN_BTN_DOWN) == LOW) selectedPlantIndex = (selectedPlantIndex - 1 + NUM_PLANTS) % NUM_PLANTS;
        activePlant = plantLibrary[selectedPlantIndex];
        
        lcd.setCursor(0, 0); lcd.print("Select Plant Species:");
        lcd.setCursor(0, 1); lcd.print("> "); lcd.print(activePlant.name); lcd.print("       "); 
        lcd.setCursor(0, 2); lcd.print("Set T:"); lcd.print(activePlant.temp_avg, 1);
        lcd.setCursor(0, 3); lcd.print("Set H:"); lcd.print(activePlant.hum_avg, 1);
    }
}
