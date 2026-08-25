#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <inttypes.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/timers.h"
#include "driver/uart.h"
#include "driver/i2c.h"
#include "driver/i2s_std.h"
#include "nvs_flash.h"          // NVS 初始化，藍牙需要存配對資訊
#include "esp_bt.h"             // 藍牙控制器設定 (Classic + BLE)
#include "esp_bt_main.h"        // Bluedroid 初始化/啟用
#include "esp_bt_device.h"      // 設定裝置名稱
#include "esp_gap_bt_api.h"     // Classic BT GAP (搜尋/配對)
#include "esp_gap_ble_api.h"    // BLE GAP (掃描廣播)
#include "esp_gatt_common_api.h"// BLE GATT 共用定義
#include "esp_gattc_api.h"      // BLE GATT Client
#include "esp_gatts_api.h"      // BLE GATT Server (如果要跟 App 溝通)
#include "esp_a2dp_api.h"       // A2DP Sink/Source
#include "esp_hf_client_api.h"  // HFP Hands-Free Client (接聽電話)
#include "esp_spp_api.h"        // SPP Serial Port Profile (跟 App 傳資料)
#include "esp_log.h"            // Log 輸出
#include "esp_avrc_api.h"
#include "driver/i2s_std.h"
#include <math.h>
#include "hal/i2s_ll.h"
#include "soc/i2s_struct.h"
#include "freertos/ringbuf.h"
#include <inttypes.h>
#include "esp_adc/adc_oneshot.h"
#include "esp_dsp.h"
#include "esp_random.h"
#include "esp_timer.h"
#include "esp_http_server.h"
#include "esp_ota_ops.h"
#include "esp_partition.h"
#include "esp_system.h"
#include "esp_wifi.h"    // 解決 wifi_config_t 找不到的錯誤
#include "esp_netif.h"   // 解決 esp_netif_init 找不到的錯誤
#include "esp_event.h"
#include <sys/param.h>
#include "lwip/ip4_addr.h"
#include "esp_heap_caps.h"
RingbufHandle_t mic_ringbuf = NULL;
RingbufHandle_t music_ringbuf = NULL;
RingbufHandle_t fft_ringbuf = NULL;
RingbufHandle_t hfp_ringbuf = NULL;
RingbufHandle_t hfp_tx_ringbuf = NULL;
#define SAMPLE_RATE     48000
#define TONE_FREQ       1000
#define PI              3.14159265
#define BUF_LEN         480   // 10 cycles buffer
adc_oneshot_unit_handle_t adc_handle;
extern esp_err_t es8311_config_sample(uint32_t sample_rate);
#define TAG "SHELL"
#define ES8311_ADDR 0x18
#define ES7243E_ADDR 0x10
#define UART_NUM UART_NUM_0
#define BUF_SIZE 128
#define BOARD_PA_EN_PIN 21
#define BOARD_SY_LED1 22
#define BOARD_SY_LED2 27
#define I2C_SDA 18
#define I2C_SCL 23
#define ES8311_ADDR 0x18
void es8311_i2s_config_debug(void);
void bt_app_avrc_ct_cb(esp_avrc_ct_cb_event_t event, esp_avrc_ct_cb_param_t *param);
void bt_app_avrc_tg_cb(esp_avrc_tg_cb_event_t event, esp_avrc_tg_cb_param_t *param);
static volatile float current_freq = 200.0;
volatile int16_t g_noise_gate_threshold = 800;
volatile int16_t g_hard_limit = 10000;
volatile float g_anc_gain = 0.5f;       // 降噪增益 (0.0 ~ 1.0)，先從 0.5 開始測試
volatile int g_phase_delay_samples = 0;  // 軟體微調延遲點數 (0 ~ 64 點)，用來對齊相位
volatile bool g_hfp_reconfig_lock = false;
// 在檔案頂部全域宣告區
static uint16_t gl_conn_id = 0xFFFF; // 儲存目前的連線 ID
static esp_gatt_if_t gl_gatts_if = 0xFF; // 儲存目前的 GATT 介面

static uint16_t gl_web_conn_id = 0xFFFF;
static bool g_web_is_connected = false;


extern uint16_t handle_table[]; // 如果 handle_table 在其他檔案，請用 extern
#define IDX_CHAR_VAL_A 1        // 請確認這個值是否為你的 Characteristic Handle Index
// ==========================================================
// 🎛️ 數位混音台比例設定 (可由 UART 動態調整)
// ==========================================================
volatile float g_master_volume = 0.2;   // 總音量 (Master)
volatile float g_sidetone_ratio = 0.5f;  // 麥克風側音比例 (Mic)
volatile float g_hfp_rx_ratio = 0.8f;    // 對方通話比例 (HFP)
volatile float g_agc_target_level = 3000.0f; // 目標舒適音量 (預設 3000)
volatile float g_agc_max_gain = 5.0f;        // 最大允許放大倍數 (預設 5.0 倍)
TaskHandle_t fft_task_handle = NULL;
TaskHandle_t sys_ctrl_task_handle = NULL;
esp_event_loop_handle_t g_custom_event_loop = NULL;
// 宣告靜態任務所需的控制結構與陣列（放到外部記憶體中）
static StaticTask_t *s_sys_evt_task_tcb = NULL;
static StackType_t  *s_sys_evt_task_stack = NULL;
#define SYS_EVT_STACK_SIZE 2048 // 給予充足的 2KB 空間
RTC_NOINIT_ATTR uint32_t g_ota_mode_flag; 
#define OTA_MAGIC_NUM 0x5AA55AA5
typedef enum {
    PATIENT_SNHL = 0,  // 感音神經性 (老人)
    PATIENT_CHL = 1    // 傳導性 (IEEE論文患者)
} patient_mode_t;

typedef enum {
    AUDIO_A2DP_48K = 0, // 聽音樂 / 日常輔聽
    AUDIO_HFP_16K = 1   // 講電話
} audio_state_t;
typedef enum {
    AUDIO_STATE_IDLE = 0,
    AUDIO_STATE_A2DP_48K = 1, // 聽音樂中
    AUDIO_STATE_HFP_16K = 2   // 講電話中 (SCO 通道)
} system_audio_state_t;
typedef struct {
    float b0, b1, b2, a1, a2;
} biquad_coeffs_t;
uint16_t handle_table[IDX_CHAR_VAL_A + 1];

// ==========================================================
// 雙機協同架構 (Master / Device) 全域狀態
// ==========================================================
volatile int g_system_role = 0; // 0 = MASTER, 1 = DEVICE
volatile bool g_is_device_connected = false; // 備援機制連線旗標
// ==========================================================
// 藍牙裝置名稱設定
// ==========================================================
char g_bt_name[32] = "ESP32_ANC";        // 傳統藍牙預設名稱
char g_ble_name[32] = "ESP32_ANC_BLE";    // BLE 預設名稱

typedef struct {
    float x1, x2, y1, y2;
} biquad_state_t;
volatile uint32_t current_a2dp_sample_rate = 48000;
extern volatile bool g_i2s_is_reconfiguring; 
volatile bool g_i2s_is_reconfiguring = false;
volatile bool g_is_audiometry_mode = false;
httpd_handle_t start_webserver(void);
void update_8band_eq(uint32_t sample_rate);
void process_cmd(char *line);
static const char *WEBTAG = "WEB_OTA";
// ==========================================
// 提前宣告 HFP Callback 函式 (防止編譯器找不到)
// ==========================================
void bt_app_hf_client_cb(esp_hf_client_cb_event_t event, esp_hf_client_cb_param_t *param);
void bt_app_hf_client_incoming_data_cb(const uint8_t *buf, uint32_t sz);
void play_pure_tone(float freq_hz, float target_db_hl, int duration_ms);
uint32_t bt_app_hf_client_outgoing_data_cb(uint8_t *buf, uint32_t sz);
volatile system_audio_state_t g_current_audio_state = AUDIO_STATE_IDLE;
volatile bool g_flag_need_i2s_reconfig_16k = false;
volatile bool g_flag_need_i2s_reconfig_44p1k = false;
volatile bool g_play_bt_conn_sound = false;
volatile bool g_play_bt_disc_sound = false;
// ==========================================================
// 🎛️ 物理聲壓校正參數 (Calibration Parameters)
// ==========================================================
// 🎤 1. 麥克風校正值 (你剛剛用 iPhone 算出來的 99！)
volatile float g_mic_calib_offset = 99.0f;

// 🔊 2. 喇叭校正值 (預設為 0，等你用 iPhone 測量耳機推力後更新)
volatile float g_spk_calib_offset = 0.0f;
static uint16_t gl_gatts_client_if = 0xFF;
void gattc_event_handler(esp_gattc_cb_event_t event, esp_gatt_if_t gattc_if, esp_ble_gattc_cb_param_t *param);
// ==========================================================
// 🏥 聽力驗配系統專用通訊旗標
// ==========================================================
volatile bool g_run_audiometry = false; // 控制是否開始測聽
volatile bool g_user_heard_it = false;  // 病患是否按下按鈕
// ==========================================
// 📞 HFP 狀態機：全面監聽版 (絕對防禦版)
// ==========================================
// ==========================================
// 📞 準備一個全域變數，記住手機的 MAC 地址
// ==========================================
esp_bd_addr_t g_connected_phone_bda = {0};
// ==========================================
// ⏱️ 延遲索求音訊任務 (專治 iOS CallKit 延遲)
// ==========================================
// ==========================================
// 🌟 突擊隊任務與大腦記憶體
// ==========================================
bool g_is_incoming_call = false; // 大腦：記住這通電話是打來的還是打去的
// ==========================================
// 宣告由 CMake 自動產生的 HTML 記憶體指標
// (注意：變數名稱是根據檔名 index.html 自動推導出來的)
// ==========================================
extern const uint8_t index_html_start[] asm("_binary_index_html_start");
extern const uint8_t index_html_end[]   asm("_binary_index_html_end");
esp_err_t ota_update_handler(httpd_req_t *req) {
    esp_err_t err;
    esp_ota_handle_t update_handle = 0;
    const esp_partition_t *update_partition = NULL;

    ESP_LOGI(WEBTAG, "開始接收 OTA 更新檔...");

    // 1. 尋找下一個可用的 OTA 分區
    update_partition = esp_ota_get_next_update_partition(NULL);
    if (update_partition == NULL) {
        ESP_LOGE(WEBTAG, "找不到可用的 OTA 分區！");
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Partition error");
        return ESP_FAIL;
    }
    ESP_LOGI(WEBTAG, "寫入目標分區: %s", update_partition->label);

    // 2. 初始化 OTA 寫入任務
    err = esp_ota_begin(update_partition, OTA_WITH_SEQUENTIAL_WRITES, &update_handle);
    if (err != ESP_OK) {
        ESP_LOGE(WEBTAG, "esp_ota_begin 失敗 (%s)", esp_err_to_name(err));
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "OTA Begin failed");
        return ESP_FAIL;
    }

    // 3. 準備接收緩衝區 (8KB)
    char *ota_write_data = (char *)malloc(8192); 
    if (!ota_write_data) {
        ESP_LOGE(WEBTAG, "記憶體分配失敗");
        return ESP_FAIL;
    }

    int remaining = req->content_len;
    int received = 0;

    // 4. 迴圈分塊讀取 HTTP 封包，並寫入 Flash
    while (remaining > 0) {
        int recv_len = httpd_req_recv(req, ota_write_data, MIN(remaining, 8192));
        if (recv_len < 0) {
            if (recv_len == HTTPD_SOCK_ERR_TIMEOUT) {
                continue; // 超時重試
            }
            ESP_LOGE(WEBTAG, "接收資料錯誤");
            free(ota_write_data);
            esp_ota_abort(update_handle);
            return ESP_FAIL;
        }

        // 寫入 Flash 分區
        err = esp_ota_write(update_handle, (const void *)ota_write_data, recv_len);
        if (err != ESP_OK) {
            ESP_LOGE(WEBTAG, "寫入 Flash 失敗 (%s)", esp_err_to_name(err));
            free(ota_write_data);
            esp_ota_abort(update_handle);
            return ESP_FAIL;
        }

        remaining -= recv_len;
        received += recv_len;
        // 若需要監看進度可把這行註解打開：
        // ESP_LOGI(WEBTAG, "已接收: %d / %d bytes", received, req->content_len);
    }

    free(ota_write_data);

    // 5. 結束 OTA 寫入，校驗檔案完整性
    err = esp_ota_end(update_handle);
    if (err != ESP_OK) {
        if (err == ESP_ERR_OTA_VALIDATE_FAILED) {
            ESP_LOGE(WEBTAG, "韌體校驗失敗！請確認上傳的是正確的 .bin 檔");
        } else {
            ESP_LOGE(WEBTAG, "esp_ota_end 失敗 (%s)", esp_err_to_name(err));
        }
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "OTA End failed");
        return ESP_FAIL;
    }

    // 6. 設定下次開機的分區
    err = esp_ota_set_boot_partition(update_partition);
    if (err != ESP_OK) {
        ESP_LOGE(WEBTAG, "esp_ota_set_boot_partition 失敗 (%s)", esp_err_to_name(err));
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Set boot partition failed");
        return ESP_FAIL;
    }

    // 7. 回傳成功訊息給前端網頁
    ESP_LOGI(WEBTAG, "OTA 更新成功！準備重啟...");
    httpd_resp_sendstr(req, "Update Success! Rebooting...");

    // 延遲 1 秒後重啟，確保 HTTP 回應有送出給手機
    vTaskDelay(pdMS_TO_TICKS(1000));
    esp_restart();

    return ESP_OK;
}

void safe_i2s_disable(i2s_chan_handle_t handle) {
    if (handle != NULL) {
        // 先嘗試 disable，但如果它報錯，我們也無所謂，繼續執行 del
        esp_err_t err = i2s_channel_disable(handle);
        if (err != ESP_OK) {
            ESP_LOGW("SYS", "通道已處於關閉狀態，直接刪除...");
        }
        i2s_del_channel(handle);
    }
}

// ==========================================================
// 🚀 專屬 OTA 模式的 Wi-Fi 啟動函數 (記憶體極度充裕)
// ==========================================================
void wifi_init_softap(void) {
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default()); // 回歸最穩定原生的事件系統
    
    esp_netif_t *ap_netif = esp_netif_create_default_wifi_ap();

    // 自訂熱點 IP 位址 (10.10.10.1) 讓 OTA 網頁看起來更專業
    esp_netif_ip_info_t ip_info;
    esp_netif_dhcps_stop(ap_netif); 
    IP4_ADDR(&ip_info.ip, 10, 10, 10, 1);       
    IP4_ADDR(&ip_info.gw, 10, 10, 10, 1);       
    IP4_ADDR(&ip_info.netmask, 255, 255, 255, 0); 
    esp_netif_set_ip_info(ap_netif, &ip_info);
    esp_netif_dhcps_start(ap_netif);

    // 使用預設配置，不需再做極限瘦身
    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));

    // 設定開放式 OTA 熱點
    wifi_config_t wifi_config = {
        .ap = {
            .ssid = "HearingAid_Update",
            .ssid_len = strlen("HearingAid_Update"),
            .channel = 1,
            .max_connection = 4,
            .authmode = WIFI_AUTH_OPEN
        },
    };

    ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_AP));
    ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &wifi_config));
    ESP_ERROR_CHECK(esp_wifi_start());

    ESP_LOGI("OTA", "📡 OTA 專屬 Wi-Fi 啟動成功！請連線至 HearingAid_Update (IP: 10.10.10.1)");
}



// 🌟 3. 改寫原本的函數 (讓長按 OTA 開機時可以無縫沿用)

// --- 首頁 HTML 處理 (維持你的原樣) ---
esp_err_t index_get_handler(httpd_req_t *req) {
    ESP_LOGI(WEBTAG, "患者/工程師 已連上網頁...");
    const size_t html_size = (index_html_end - index_html_start);
    httpd_resp_set_type(req, "text/html; charset=utf-8");
    httpd_resp_send(req, (const char *)index_html_start, html_size);
    return ESP_OK;
}

// 🌟 4. 安全版本的切換開關 (給按鍵短按專用)
bool g_is_tuning_mode = false;
httpd_handle_t g_web_server_handle = NULL;



esp_err_t tuning_ws_handler(httpd_req_t *req)
{
    // 如果是剛建立連線的握手請求，直接放行
    if (req->method == HTTP_GET) {
        ESP_LOGI("WS", "網頁端已成功連上 WebSocket！");
        return ESP_OK;
    }

    // 準備接收網頁傳來的即時數據
    httpd_ws_frame_t ws_pkt;
    uint8_t buf[128] = {0};
    memset(&ws_pkt, 0, sizeof(httpd_ws_frame_t));
    ws_pkt.payload = buf;
    ws_pkt.type = HTTPD_WS_TYPE_TEXT;
    
    // 讀取 WebSocket 封包
    esp_err_t ret = httpd_ws_recv_frame(req, &ws_pkt, 127);
    if (ret != ESP_OK) {
        return ret;
    }

    if (ws_pkt.type == HTTPD_WS_TYPE_TEXT) {
        // 這裡就是網頁滑桿即時傳來的字串！
        // 例如網頁傳來: "SET_VOL 80" 或 "SET_EQ_1 5.5"
        ESP_LOGI("WS", "收到網頁指令: %s", ws_pkt.payload);

        // 💡 在這裡把收到的字串，丟給我們之前寫好的 process_cmd() 
        // 這樣你原本用 UART 敲的指令，就能直接從網頁無縫觸發了！
        process_cmd((char*)ws_pkt.payload);
    }

    return ESP_OK;
}
httpd_handle_t start_webserver(void) {
    httpd_handle_t server = NULL;
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    
    config.max_uri_handlers = 8;
    config.recv_wait_timeout = 10;
    config.send_wait_timeout = 10;

    ESP_LOGI(WEBTAG, "啟動 Web Server...");
    if (httpd_start(&server, &config) == ESP_OK) {
        
        // 1. 原本的 OTA 接收端 (維持不變)
        httpd_uri_t ota_update_uri = {
            .uri       = "/update",
            .method    = HTTP_POST,
            .handler   = ota_update_handler,
            .user_ctx  = NULL
        };
        httpd_register_uri_handler(server, &ota_update_uri);

        // 2. 原本的首頁 HTML (維持不變，稍後網頁裡面再寫 JS)
        httpd_uri_t index_html_uri = {
            .uri       = "/",
            .method    = HTTP_GET,
            .handler   = index_get_handler,
            .user_ctx  = NULL
        };
        httpd_register_uri_handler(server, &index_html_uri);
        
        // ⭐ 3. 新增：註冊 WebSocket 即時通訊通道
        httpd_uri_t ws_tuning_uri = {
            .uri        = "/ws",
            .method     = HTTP_GET,
            .handler    = tuning_ws_handler, // 我們等一下要寫的函數
            .user_ctx   = NULL,
            .is_websocket = true             // 關鍵！告訴系統這是 WebSocket
        };
        httpd_register_uri_handler(server, &ws_tuning_uri);
        
        return server;
    }
    ESP_LOGE(WEBTAG, "啟動伺服器失敗");
    return NULL;
}

// ==========================================================
// 🏭 產線量產專用：從 Flash 讀寫校正參數 (NVS)
// ==========================================================
void ringbuf_flush(RingbufHandle_t xRingbuffer) {
    size_t received_bytes = 0;
    void* item = NULL;
    // 不斷嘗試接收，直到沒有資料為止
    while (xRingbufferReceive(xRingbuffer, &received_bytes, 0) != NULL) {
        // 這裡不需要做任何事，只是把空間釋放掉
        vRingbufferReturnItem(xRingbuffer, item);
    }
}
void load_calibration_from_flash(void) {
    nvs_handle_t my_handle;
    esp_err_t err = nvs_open("storage", NVS_READWRITE, &my_handle);
    if (err == ESP_OK) {
        int32_t mic_val = 990; // 預設值 99.0 * 10
        int32_t spk_val = 0;   // 預設值 0.0 * 10

        // 嘗試讀取，如果有存過就會覆蓋預設值
        nvs_get_i32(my_handle, "mic_calib", &mic_val);
        nvs_get_i32(my_handle, "spk_calib", &spk_val);

        g_mic_calib_offset = (float)mic_val / 10.0f;
        g_spk_calib_offset = (float)spk_val / 10.0f;
		nvs_get_i32(my_handle, "mic_calib", &mic_val);
        nvs_get_i32(my_handle, "spk_calib", &spk_val);

        // ⭐ 新增：讀取系統角色 (0: Master, 1: Device)
        int32_t role_val = 0;
        if (nvs_get_i32(my_handle, "sys_role", &role_val) == ESP_OK) {
            g_system_role = role_val;
        }
		size_t len = sizeof(g_bt_name);
        if (nvs_get_str(my_handle, "bt_name", g_bt_name, &len) == ESP_OK) {
            ESP_LOGI("NVS", "✅ 讀取客製化 BT 名稱: %s", g_bt_name);
        }
        
        len = sizeof(g_ble_name);
        if (nvs_get_str(my_handle, "ble_name", g_ble_name, &len) == ESP_OK) {
            ESP_LOGI("NVS", "✅ 讀取客製化 BLE 名稱: %s", g_ble_name);
        }
        g_mic_calib_offset = (float)mic_val / 10.0f;
        g_spk_calib_offset = (float)spk_val / 10.0f;

        ESP_LOGI("NVS", "✅ 成功載入產線校正資料 - MIC: %.1f, SPK: %.1f", g_mic_calib_offset, g_spk_calib_offset);
        ESP_LOGI("NVS", "👑 當前系統角色設定為: %s", g_system_role == 0 ? "MASTER (主機端)" : "DEVICE (發射端)");
        nvs_close(my_handle);
    }
}
void save_audio_tuning_to_nvs(void)
{
    nvs_handle_t my_handle;
    if (nvs_open("storage", NVS_READWRITE, &my_handle) == ESP_OK) {
        extern volatile float g_master_volume;
        extern volatile float g_sidetone_ratio;
        extern volatile float g_hfp_rx_ratio;
        extern volatile float g_user_eq[8]; // ⭐ 改成儲存基準層

        nvs_set_i32(my_handle, "vol_master", (int32_t)(g_master_volume * 100.0f));
        nvs_set_i32(my_handle, "vol_side",   (int32_t)(g_sidetone_ratio * 100.0f));
        nvs_set_i32(my_handle, "vol_hfp",    (int32_t)(g_hfp_rx_ratio * 100.0f));

        for (int i = 0; i < 8; i++) {
            char key[15];
            sprintf(key, "eq_band_%d", i); 
            nvs_set_i32(my_handle, key, (int32_t)(g_user_eq[i] * 10.0f)); // ⭐ 儲存基準層
        }
        nvs_commit(my_handle);
        nvs_close(my_handle);
        ESP_LOGI("NVS", "💾 參數已成功寫入 Flash 永久儲存！");
    }
}
void save_bt_name_to_flash(const char* key, const char* name) {
    nvs_handle_t my_handle;
    if (nvs_open("storage", NVS_READWRITE, &my_handle) == ESP_OK) {
        nvs_set_str(my_handle, key, name);
        nvs_commit(my_handle);
        nvs_close(my_handle);
    }
}
void load_audio_tuning_from_nvs(void) {
    nvs_handle_t my_handle;
    extern volatile float g_user_eq[8];
    extern volatile float g_auto_offset[8];
    extern volatile float g_target_gains_db[8];

    if (nvs_open("storage", NVS_READONLY, &my_handle) == ESP_OK) {
        int32_t val;
        if (nvs_get_i32(my_handle, "vol_master", &val) == ESP_OK) g_master_volume = val / 100.0f;
        if (nvs_get_i32(my_handle, "vol_side", &val) == ESP_OK) g_sidetone_ratio = val / 100.0f;
        if (nvs_get_i32(my_handle, "vol_hfp", &val) == ESP_OK) g_hfp_rx_ratio = val / 100.0f;

        for (int i = 0; i < 8; i++) {
            char key[15];
            sprintf(key, "eq_band_%d", i);
            if (nvs_get_i32(my_handle, key, &val) == ESP_OK) {
                g_user_eq[i] = val / 10.0f; // ⭐ 讀取進基準層
            }
            // 每次開機，確保目標值 = 基準值 + 防護值(0)
            g_target_gains_db[i] = g_user_eq[i] + g_auto_offset[i]; 
        }
        nvs_close(my_handle);
        extern volatile uint32_t current_a2dp_sample_rate;
        update_8band_eq(current_a2dp_sample_rate);
    }
}

void load_audio_tuning_defaults(void)
{
    extern volatile float g_master_volume, g_sidetone_ratio, g_hfp_rx_ratio;
    g_master_volume = 0.2f; g_sidetone_ratio = 0.5f; g_hfp_rx_ratio = 0.8f;

    extern volatile float g_agc_target_level, g_agc_max_gain;
    extern volatile int16_t g_noise_gate_threshold, g_hard_limit;
    g_agc_target_level = 3000.0f; g_agc_max_gain = 5.0f;
    g_noise_gate_threshold = 800; g_hard_limit = 10000;

    extern volatile float g_anc_gain;
    extern volatile int g_phase_delay_samples;
    g_anc_gain = 0.5f; g_phase_delay_samples = 0;

    extern volatile float g_user_eq[8];
    extern volatile float g_auto_offset[8];
    extern volatile float g_target_gains_db[8];
    const float default_eq[8] = {0.0f, -2.0f, 3.0f, 4.0f, 2.0f, 0.0f, -3.0f, -6.0f};
    
    for (int i = 0; i < 8; i++) {
        g_user_eq[i] = default_eq[i];
        g_auto_offset[i] = 0.0f; // 預設無防護
        g_target_gains_db[i] = g_user_eq[i] + g_auto_offset[i];
    }
    extern volatile uint32_t current_a2dp_sample_rate;
    update_8band_eq(current_a2dp_sample_rate);
    ESP_LOGW("TUNING", "🔄 所有調音參數已恢復為系統預設值！");
}
void save_calibration_to_flash(const char* key, float value) {
    nvs_handle_t my_handle;
    if (nvs_open("storage", NVS_READWRITE, &my_handle) == ESP_OK) {
        int32_t int_val = (int32_t)(value * 10.0f);
        nvs_set_i32(my_handle, key, int_val);
        nvs_commit(my_handle); // 確保寫入 Flash
        nvs_close(my_handle);
    }
}
void delay_ask_audio_task(void *pvParameters) {
    ESP_LOGW("HFP", "⏱️ 等待 iOS CallKit 準備通道 (1.5秒)...");
    vTaskDelay(pdMS_TO_TICKS(1500)); 
    
    ESP_LOGW("HFP", "🔥 強制發送音訊連結請求...");
    // 這是唯一真正需要的 API，確保它編譯通過即可
    esp_hf_client_connect_audio(g_connected_phone_bda); 
    
    vTaskDelete(NULL);
}
void upsample_16k_to_48k_fast(const int16_t *in_buf, int16_t *out_buf, uint32_t sz) {
    for (uint32_t i = 0; i < sz; i++) {
        int16_t sample = in_buf[i];
        out_buf[i * 3]     = sample;
        out_buf[i * 3 + 1] = sample;
        out_buf[i * 3 + 2] = sample;
    }
}
// ==========================================
// 🌟 HFP 狀態機 (終極完全體)
// ==========================================
void bt_app_hf_client_cb(esp_hf_client_cb_event_t event, esp_hf_client_cb_param_t *param)
{
    ESP_LOGI("HFP_RAW", "👉 收到 HFP 底層 Event ID: %d", event);

    switch (event) {
        // ------------------------------------------------
        // 1. 連線狀態事件
        // ------------------------------------------------
        case ESP_HF_CLIENT_CONNECTION_STATE_EVT:
            if (param->conn_stat.state == ESP_HF_CLIENT_CONNECTION_STATE_CONNECTED) {
                ESP_LOGI("HFP", "✅ HFP 控制通道已連線！");
                memcpy(g_connected_phone_bda, param->conn_stat.remote_bda, sizeof(esp_bd_addr_t));
            } else if (param->conn_stat.state == ESP_HF_CLIENT_CONNECTION_STATE_DISCONNECTED) {
                ESP_LOGI("HFP", "❌ HFP 控制通道已斷開！");
            }
            break;
            
        // ------------------------------------------------
        // 2. 音訊通道狀態事件 (Event 1)
        // ------------------------------------------------
        case ESP_HF_CLIENT_AUDIO_STATE_EVT:
            if (param->audio_stat.state == ESP_HF_CLIENT_AUDIO_STATE_DISCONNECTED) {
                ESP_LOGW("HFP", "🛑 狀態 0: SCO 通道已斷開！切回 A2DP");
                g_current_audio_state = AUDIO_STATE_IDLE;
				vTaskDelay(pdMS_TO_TICKS(50));				
                g_flag_need_i2s_reconfig_44p1k = true;
				esp_a2d_sink_connect(g_connected_phone_bda);
                
            } else if (param->audio_stat.state == ESP_HF_CLIENT_AUDIO_STATE_CONNECTING) {
                ESP_LOGI("HFP", "⏳ 狀態 1: SCO 通道握手中 (Connecting)...");
                esp_a2d_sink_disconnect(g_connected_phone_bda); 
				break;
            } else if (param->audio_stat.state == ESP_HF_CLIENT_AUDIO_STATE_CONNECTED) {
                ESP_LOGW("HFP", "🚨 狀態 2: 傳統 8kHz 音訊通道已建立！");
                g_current_audio_state = AUDIO_STATE_HFP_16K; // 🧠 大腦記住已連線
                g_flag_need_i2s_reconfig_16k = true;
                
            } else if (param->audio_stat.state == ESP_HF_CLIENT_AUDIO_STATE_CONNECTED_MSBC) {
                ESP_LOGW("HFP", "🚨 狀態 3: 高音質 16kHz 音訊通道已建立！");
                g_current_audio_state = AUDIO_STATE_HFP_16K; // 🧠 大腦記住已連線
                g_flag_need_i2s_reconfig_16k = true;
            }
            break;

        // ------------------------------------------------
        // 4. 來電準備/響鈴狀態事件 (Event 4)
        // ------------------------------------------------
        case ESP_HF_CLIENT_CIND_CALL_SETUP_EVT:
            ESP_LOGI("HFP", "🛎️ Call Setup 狀態改變！真實數值: %d", param->call_setup.status);
            
            if (param->call_setup.status == 1) { 
                // 路線 A：別人打進來
                ESP_LOGW("HFP", "☎️ [來電 (Call In)] 發射代客接聽...");
                g_is_incoming_call = true;   // 🧠 大腦記住是來電
                //esp_hf_client_answer_call(); 
                
            } else if (param->call_setup.status == 2 || param->call_setup.status == 3) {
                // 路線 B：我們打出去
                ESP_LOGW("HFP", "☎️ [撥出 (Call Out)] 遵守 iOS 規定，保持被動...");
                g_is_incoming_call = false;  // 🧠 大腦記住是撥出
            }
            break;

        // ------------------------------------------------
        // 3. 通話狀態改變事件 (Event 3)
        // ------------------------------------------------
        case ESP_HF_CLIENT_CIND_CALL_EVT:
            ESP_LOGI("HFP", "📞 Call 狀態改變！真實數值: %d", param->call.status);
            
            if (param->call.status == 1) { // 通話已接通
                // ... (維持你原本的程式碼) ...
                
            } else if (param->call.status == 0) { // 通話結束
                ESP_LOGW("HFP", "📞 通話結束，重置狀態。");
                g_is_incoming_call = false; 

                // ⭐⭐⭐ 終極防線：應付 LINE 這種不按牌理出牌的 App
                // 不管手機有沒有發送音訊斷開事件，只要通話一結束，我們強制舉起 44.1k 切換旗標！
                if (g_current_audio_state == AUDIO_STATE_HFP_16K) {
                    ESP_LOGW("SYS_CTRL", "🚨 偵測到通話結束！強制啟動 44.1kHz 硬體重配流程...");
                    g_current_audio_state = AUDIO_STATE_IDLE; 
                    g_flag_need_i2s_reconfig_44p1k = true; // 觸發主迴圈去切換硬體
                }
            }
            break;
		// ------------------------------------------------
        // 5. 音量同步事件 (手機講電話時按下音量鍵)
        // ------------------------------------------------
        case ESP_HF_CLIENT_VOLUME_CONTROL_EVT:
            if (param->volume_control.type == ESP_HF_VOLUME_CONTROL_TARGET_SPK) {
                int vol = param->volume_control.volume; // 手機傳來範圍 0~15
                
                extern volatile float g_master_volume;
                
                // 🌟 HFP 通話音量也改成平方曲線！
                float linear_ratio = (float)vol / 15.0f; 
                g_master_volume = linear_ratio * linear_ratio; 
                
                ESP_LOGI("HFP", "📱 通話音量鍵調整總音量: %d/15 -> %.4f", vol, g_master_volume);
            }
            break;
        default:
            break;
    }
}


// ==========================================
// 📡 MASTER 專用：解析 SLAVE 傳來的環境封包
// ==========================================
extern volatile bool g_is_slave_online; // 斷線容錯旗標









static uint32_t g_hfp_packet_count = 0;
static uint32_t g_hfp_total_bytes = 0;
biquad_coeffs_t g_notch_coeffs_shadow;
volatile bool g_notch_update_pending = false;
void bt_app_hf_client_incoming_data_cb(const uint8_t *buf, uint32_t sz)
{
    if (buf != NULL && sz > 0) {
        // 現在我們知道它是完美的 16kHz 單聲道了，絕對不要複製它！直接直通！
        xRingbufferSend(hfp_ringbuf, buf, sz, 0); 
    }
}

// ==========================================
// 🎤 HFP 音訊資料流：你要傳給手機的麥克風聲音
// ==========================================
uint32_t bt_app_hf_client_outgoing_data_cb(uint8_t *buf, uint32_t sz)
{
    size_t bytes_read_total = 0;

    // 🕵️‍♂️ 郵差探針：確認藍牙底層真的有來要資料！(每 50 次印一次)
    static int fetch_cnt = 0;
    if (++fetch_cnt % 50 == 0) {
        ESP_LOGI("HFP_TX", "📮 藍牙郵差來收信了！手機索取了 %lu Bytes 的麥克風聲音", (unsigned long)sz);
    }

    // 🔄 迴圈讀取
    while (bytes_read_total < sz) {
        size_t bytes_to_read = sz - bytes_read_total;
        size_t received_bytes = 0;
        
        uint8_t *data = (uint8_t *)xRingbufferReceiveUpTo(hfp_tx_ringbuf, &received_bytes, 0, bytes_to_read);

        if (data != NULL && received_bytes > 0) {
            memcpy(buf + bytes_read_total, data, received_bytes);
            vRingbufferReturnItem(hfp_tx_ringbuf, data);
            bytes_read_total += received_bytes;
        } else {
            break; 
        }
    }

    if (bytes_read_total < sz) {
        memset(buf + bytes_read_total, 0, sz - bytes_read_total);
    }

    return sz; 
}

// ==========================================================
// 🎛️ 動態 8 頻段 EQ 系統與動態陷波器 (RBJ Filter Generator)
// ==========================================================
// ==========================================================
// 🎛️ 物理聲壓校正參數 (Calibration Offset)
// ==========================================================
// 假設分貝計顯示真實噪音是 80 dB，但系統原本印出 -45 dB
// 差值就是 80 - (-45) = 125。請根據實際測量結果微調此數值！
const float HARDWARE_CALIBRATION_OFFSET = 125.0f;
volatile float g_target_noise_freq = 0.0f; // 狙擊槍鎖定的噪音目標頻率

// 8 個頻段的中心頻率 (符合臨床聽力學倍頻程)
const float EQ_FREQS[8] = {250.0f, 500.0f, 1000.0f, 2000.0f, 3000.0f, 4000.0f, 6000.0f, 8000.0f};
biquad_coeffs_t g_eq_coeffs[8];
biquad_state_t  g_eq_states[8] = {0};       // 這是原本給麥克風用的
biquad_state_t  g_eq_states_music[8] = {0}; // ⭐ 新增這行：這是專門給藍牙音樂用的記憶體


// 窄頻陷波器 (狙擊槍)
biquad_coeffs_t g_notch_coeffs;
biquad_state_t  g_notch_state = {0};

// 1. 生成 Peaking EQ (散彈槍：輔聽增強用)
void calculate_peaking_eq(float f0, float Fs, float gain_db, float Q, biquad_coeffs_t *coeffs) {
    if (f0 >= Fs / 2.0f) {
        coeffs->b0 = 1.0f; coeffs->b1 = 0.0f; coeffs->b2 = 0.0f; coeffs->a1 = 0.0f; coeffs->a2 = 0.0f; return;
    }
    float A = powf(10.0f, gain_db / 40.0f);
    float w0 = 2.0f * (float)M_PI * f0 / Fs;
    float alpha = sinf(w0) / (2.0f * Q);
    float a0 = 1.0f + alpha / A;
    
    coeffs->b0 = (1.0f + alpha * A) / a0;
    coeffs->b1 = (-2.0f * cosf(w0)) / a0;
    coeffs->b2 = (1.0f - alpha * A) / a0;
    coeffs->a1 = (-2.0f * cosf(w0)) / a0;
    coeffs->a2 = (1.0f - alpha / A) / a0;
}

// 2. 生成 Notch Filter (狙擊槍：精準降噪用)
void calculate_notch_filter(float f0, float Fs, float Q, biquad_coeffs_t *coeffs) {
    if (f0 <= 20.0f || f0 >= Fs / 2.0f) { 
        coeffs->b0 = 1.0f; coeffs->b1 = 0.0f; coeffs->b2 = 0.0f; coeffs->a1 = 0.0f; coeffs->a2 = 0.0f; return;
    }
    float w0 = 2.0f * (float)M_PI * f0 / Fs;
    float alpha = sinf(w0) / (2.0f * Q);
    float a0 = 1.0f + alpha;

    coeffs->b0 = 1.0f / a0; 
    coeffs->b1 = (-2.0f * cosf(w0)) / a0; 
    coeffs->b2 = 1.0f / a0;
    coeffs->a1 = (-2.0f * cosf(w0)) / a0; 
    coeffs->a2 = (1.0f - alpha) / a0;
}


// ==========================================================
// 🎛️ 動態 8 頻段 EQ 系統全域變數
// ==========================================================
// 這就是我們新的「動態大腦」
volatile float g_user_eq[8] = {0.0f, -2.0f, 3.0f, 4.0f, 2.0f, 0.0f, -3.0f, -6.0f}; 

// 2. 自動防護層 (FFT 動態計算的衰減值，平時為 0)
volatile float g_auto_offset[8] = {0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f};

// 3. 最終輸出層 (送給 DSP 濾波器的真實目標 = g_user_eq + g_auto_offset)
volatile float g_target_gains_db[8] = {0.0f, -2.0f, 3.0f, 4.0f, 2.0f, 0.0f, -3.0f, -6.0f}; 

biquad_coeffs_t g_eq_coeffs_shadow[8]; 
volatile bool g_eq_update_pending = false;

typedef enum {
    SCENE_QUIET,          // 🟢 安靜場景
    SCENE_NOISY_NO_VOICE, // 🟡 吵雜(無人聲)
    SCENE_SPEECH          // 🔴 語音溝通中
} SceneMode;

volatile SceneMode g_current_scene = SCENE_QUIET;
volatile float g_scene_offset[8] = {0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f}; // 場景專屬 EQ 偏移層
volatile float g_env_rms = 0.0f;    // 環境總能量
volatile bool  g_vad_active = false;// 全域語音活動偵測 (VAD)


// 3. 自動更新 8 段 EQ 的大腦總管
void update_8band_eq(uint32_t sample_rate) {
    ESP_LOGW("DSP", "⚙️ 根據取樣率 %luHz 重新計算 8 段 EQ...", (unsigned long)sample_rate);
    
    for (int i = 0; i < 8; i++) {
        // ⭐ 論文核心：實時結算三大參數層！
        // 最終輸出 = (患者基礎) + (FFT 硬體防護) + (動態場景增益)
        g_target_gains_db[i] = g_user_eq[i] + g_auto_offset[i] + g_scene_offset[i];
        
        calculate_peaking_eq(EQ_FREQS[i], (float)sample_rate, g_target_gains_db[i], 1.414f, &g_eq_coeffs[i]);
    }
    ESP_LOGW("DSP", "✅ 8 段 EQ 係數更新完成！");
}





audio_state_t  g_current_audio   = AUDIO_A2DP_48K;
float process_biquad(float input, const biquad_coeffs_t *coeffs, biquad_state_t *state) 
{
    // 1. 套用標準 RBJ 公式 (注意 a1, a2 是用減的！)
    float output = (coeffs->b0 * input) + (coeffs->b1 * state->x1) + (coeffs->b2 * state->x2) 
                 - (coeffs->a1 * state->y1) - (coeffs->a2 * state->y2);

    // 2. 更新歷史軌跡 (把現在的聲音變成過去的聲音)
    state->x2 = state->x1;
    state->x1 = input;
    state->y2 = state->y1;
    state->y1 = output;

    return output;
}
typedef struct _coeff_div {
    uint32_t mclk;
    uint32_t rate;
    uint8_t pre_div;
    uint8_t pre_multi;
    uint8_t adc_div;
    uint8_t dac_div;
    uint8_t fs_mode;
    uint8_t lrck_h;
    uint8_t lrck_l;
    uint8_t bclk_div;
    uint8_t adc_osr;
    uint8_t dac_osr;
} coeff_div_t; // 確保名稱與你後續使用一致
static const struct _coeff_div coeff_div[] = {
    //mclk     rate   pre_div  mult  adc_div dac_div fs_mode lrch  lrcl  bckdiv osr
    /* 8k */
    {12288000, 8000 , 0x06, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {18432000, 8000 , 0x03, 0x02, 0x03, 0x03, 0x00, 0x05, 0xff, 0x18, 0x10, 0x20},
    {16384000, 8000 , 0x08, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {8192000 , 8000 , 0x04, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {6144000 , 8000 , 0x03, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {4096000 , 8000 , 0x02, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {3072000 , 8000 , 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {2048000 , 8000 , 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {1536000 , 8000 , 0x03, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {1024000 , 8000 , 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},

    /* 11.025k */
    {11289600, 11025, 0x04, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {5644800 , 11025, 0x02, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {2822400 , 11025, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {1411200 , 11025, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},

    /* 12k */
    {12288000, 12000, 0x04, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {6144000 , 12000, 0x02, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {3072000 , 12000, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {1536000 , 12000, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},

    /* 16k */
    {12288000, 16000, 0x03, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {18432000, 16000, 0x03, 0x02, 0x03, 0x03, 0x00, 0x02, 0xff, 0x0c, 0x10, 0x20},
    {16384000, 16000, 0x04, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {8192000 , 16000, 0x02, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {6144000 , 16000, 0x03, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {4096000 , 16000, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {3072000 , 16000, 0x03, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {2048000 , 16000, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {1536000 , 16000, 0x03, 0x08, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},
    {1024000 , 16000, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x20},

    /* 22.05k */
    {11289600, 22050, 0x02, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {5644800 , 22050, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {2822400 , 22050, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {1411200 , 22050, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},

    /* 24k */
    {12288000, 24000, 0x02, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {18432000, 24000, 0x03, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {6144000 , 24000, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {3072000 , 24000, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {1536000 , 24000, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},

    /* 32k */
    {12288000, 32000, 0x03, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {18432000, 32000, 0x03, 0x04, 0x03, 0x03, 0x00, 0x02, 0xff, 0x0c, 0x10, 0x10},
    {16384000, 32000, 0x02, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {8192000 , 32000, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {6144000 , 32000, 0x03, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {4096000 , 32000, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {3072000 , 32000, 0x03, 0x08, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {2048000 , 32000, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {1536000 , 32000, 0x03, 0x08, 0x01, 0x01, 0x01, 0x00, 0x7f, 0x02, 0x10, 0x10},
    {1024000 , 32000, 0x01, 0x08, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},

    /* 44.1k */
    {11289600, 44100, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {5644800 , 44100, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {2822400 , 44100, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {1411200 , 44100, 0x01, 0x08, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},

    /* 48k */
    {12288000, 48000, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {18432000, 48000, 0x03, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {6144000 , 48000, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {3072000 , 48000, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {1536000 , 48000, 0x01, 0x08, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},

    /* 64k */
    {12288000, 64000, 0x03, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {18432000, 64000, 0x03, 0x04, 0x03, 0x03, 0x01, 0x01, 0x7f, 0x06, 0x10, 0x10},
    {16384000, 64000, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {8192000 , 64000, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {6144000 , 64000, 0x01, 0x04, 0x03, 0x03, 0x01, 0x01, 0x7f, 0x06, 0x10, 0x10},
    {4096000 , 64000, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {3072000 , 64000, 0x01, 0x08, 0x03, 0x03, 0x01, 0x01, 0x7f, 0x06, 0x10, 0x10},
    {2048000 , 64000, 0x01, 0x08, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {1536000 , 64000, 0x01, 0x08, 0x01, 0x01, 0x01, 0x00, 0xbf, 0x03, 0x18, 0x18},
    {1024000 , 64000, 0x01, 0x08, 0x01, 0x01, 0x01, 0x00, 0x7f, 0x02, 0x10, 0x10},

    /* 88.2k */
    {11289600, 88200, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {5644800 , 88200, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {2822400 , 88200, 0x01, 0x08, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {1411200 , 88200, 0x01, 0x08, 0x01, 0x01, 0x01, 0x00, 0x7f, 0x02, 0x10, 0x10},

    /* 96k */
    {12288000, 96000, 0x01, 0x02, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {18432000, 96000, 0x03, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {6144000 , 96000, 0x01, 0x04, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {3072000 , 96000, 0x01, 0x08, 0x01, 0x01, 0x00, 0x00, 0xff, 0x04, 0x10, 0x10},
    {1536000 , 96000, 0x01, 0x08, 0x01, 0x01, 0x01, 0x00, 0x7f, 0x02, 0x10, 0x10},
};
static i2s_chan_handle_t rx_handle = NULL;
static i2s_chan_handle_t tx_handle = NULL;

uint8_t i2c_read(uint8_t addr, uint8_t reg)
{
    uint8_t val = 0;

    i2c_master_write_read_device(
        I2C_NUM_0,
        addr,
        &reg,
        1,
        &val,
        1,
        1000 / portTICK_PERIOD_MS
    );

    return val;
}

void i2c_write(uint8_t addr, uint8_t reg, uint8_t val)
{
    uint8_t buf[2] = {reg, val};

    i2c_master_write_to_device(
        I2C_NUM_0,
        addr,
        buf,
        2,
        1000 / portTICK_PERIOD_MS
    );
	vTaskDelay(pdMS_TO_TICKS(10));
}


int get_coeff(int mclk, int rate) {
    for (int i = 0; i < sizeof(coeff_div) / sizeof(coeff_div[0]); i++) {
        if (coeff_div[i].rate == rate && coeff_div[i].mclk == mclk) {
            return i;
        }
    }
    return -1;
}
static uint8_t es7243e_read_reg(uint8_t reg) {
    return i2c_read(ES7243E_ADDR, reg);
}

static uint8_t es8311_read_reg(uint8_t reg) {
    return i2c_read(ES8311_ADDR, reg);
}

static void es8311_write_reg(uint8_t reg, uint8_t val) {
    i2c_write(ES8311_ADDR, reg, val);
}

esp_err_t es8311_config_sample(uint32_t sample_rate)
{
    uint8_t datmp, regv;
    uint32_t sample_fre = 0; 
    uint32_t mclk_fre = 0;
    int coeff;

    // 1. 採樣率對照
    switch (sample_rate) {
        case 8000:  sample_fre = 8000;  break;
        case 11025: sample_fre = 11025; break;
        case 16000: sample_fre = 16000; break;
        case 22050: sample_fre = 22050; break;
        case 24000: sample_fre = 24000; break;
        case 32000: sample_fre = 32000; break;
        case 44100: sample_fre = 44100; break;
        case 48000: sample_fre = 48000; break;
        default:
            sample_fre = sample_rate; // 嘗試直接使用傳入的值
            break;
    }

    // 2. 計算 MCLK (假設固定 256 倍)
    mclk_fre = sample_fre * 256; 
    
    // 3. 查表拿到係數索引
    coeff = get_coeff(mclk_fre, sample_fre);
    if (coeff < 0) {
        ESP_LOGE("ES8311", "無法配置採樣率 %luHz", (unsigned long)sample_fre);
        return ESP_FAIL;
    }

    /* 開始設定時鐘暫存器 */
    
    // REG 02: 預分頻與倍頻
    regv = es8311_read_reg(0x02) & 0x07;
    regv |= (coeff_div[coeff].pre_div - 1) << 5;
    
    datmp = 0; // 根據 pre_multi 設定
    switch (coeff_div[coeff].pre_multi) {
        case 1: datmp = 0; break;
        case 2: datmp = 1; break;
        case 4: datmp = 2; break;
        case 8: datmp = 3; break;
        default: break;
    }
    
    // 如果是從 SCLK (BCLK) 當來源的特殊邏輯 (通常 R&D 測試用 MCLK 可略過，但保留原始邏輯)
    // if (get_es8311_mclk_src() == FROM_SCLK_PIN) { ... } 

    regv |= (datmp) << 3;
    es8311_write_reg(0x02, regv);

    // REG 05: ADC/DAC 分頻
    regv = 0; // 原始代碼 & 0x00 等於全部重寫
    regv |= (coeff_div[coeff].adc_div - 1) << 4;
    regv |= (coeff_div[coeff].dac_div - 1) << 0;
    es8311_write_reg(0x05, regv);

    // REG 03: ADC OSR 與模式
    regv = es8311_read_reg(0x03) & 0x80;
    regv |= coeff_div[coeff].fs_mode << 6;
    regv |= coeff_div[coeff].adc_osr << 0;
    es8311_write_reg(0x03, regv);

    // REG 04: DAC OSR
    regv = es8311_read_reg(0x04) & 0x80;
    regv |= coeff_div[coeff].dac_osr << 0;
    es8311_write_reg(0x04, regv);

    // REG 07 & 08: LRCK 分頻比 (High & Low Byte)
    regv = es8311_read_reg(0x07) & 0xC0;
    regv |= coeff_div[coeff].lrck_h << 0;
    es8311_write_reg(0x07, regv);

    regv = coeff_div[coeff].lrck_l;
    es8311_write_reg(0x08, regv);

    // REG 06: BCLK 分頻比
    regv = es8311_read_reg(0x06) & 0xE0;
    if (coeff_div[coeff].bclk_div < 19) {
        regv |= (coeff_div[coeff].bclk_div - 1) << 0;
    } else {
        regv |= (coeff_div[coeff].bclk_div) << 0;
    }
    es8311_write_reg(0x06, regv);

    return ESP_OK;
}

typedef enum {
    AUDIO_HAL_08K_SAMPLES = 8000,
    AUDIO_HAL_11K_SAMPLES = 11025,
    AUDIO_HAL_16K_SAMPLES = 16000,
    AUDIO_HAL_22K_SAMPLES = 22050,
    AUDIO_HAL_24K_SAMPLES = 24000,
    AUDIO_HAL_32K_SAMPLES = 32000,
    AUDIO_HAL_44K_SAMPLES = 44100,
    AUDIO_HAL_48K_SAMPLES = 48000,
} audio_hal_iface_samples_t;


static uint16_t service_handle;
static uint16_t char_handle;
static int last_state = -1;
static esp_ble_adv_params_t adv_params = {
    .adv_int_min        = 0x20,
    .adv_int_max        = 0x40,
    .adv_type           = ADV_TYPE_IND,
    .own_addr_type      = BLE_ADDR_TYPE_PUBLIC,
    .channel_map        = ADV_CHNL_ALL,
    .adv_filter_policy  = ADV_FILTER_ALLOW_SCAN_ANY_CON_ANY,
};

uint8_t current_volume = 0xC0;
const uint8_t MAX_VOLUME = 0xFF; // 最大值
#define GATTS_SERVICE_UUID   0x00FF
#define GATTS_CHAR_UUID      0xFF01
#define GATTS_NUM_HANDLE     4
static const char *HP_TAG = "HP_DET";
void i2c_scan(void);
void check_gpio(int gpio_num);
void i2c_write(uint8_t addr, uint8_t reg, uint8_t val);
void process_cmd(char *line);
/* =========================
   ADC mapping
   ========================= */
const char* get_button(int adc)
{
    if (adc > 3500) return NULL;   // release / idle

    if (adc >= 250 && adc <= 420)  return "BTN1";
    if (adc >= 780 && adc <= 980)  return "BTN2";
    if (adc >= 1250 && adc <= 1450) return "BTN3";
    if (adc >= 1750 && adc <= 1950) return "BTN4";
    if (adc >= 2220 && adc <= 2450) return "BTN5";
    if (adc >= 2700 && adc <= 2900) return "BTN6";

    return NULL;
}
/* =========================
   ADC init
   ========================= */
void adc_init(void)
{
    adc_oneshot_unit_init_cfg_t init_config = {
        .unit_id = ADC_UNIT_1,
    };
    adc_oneshot_new_unit(&init_config, &adc_handle);

    adc_oneshot_chan_cfg_t config = {
        .bitwidth = ADC_BITWIDTH_DEFAULT,
        .atten = ADC_ATTEN_DB_12,
    };

    adc_oneshot_config_channel(adc_handle, ADC_CHANNEL_3, &config);
}

volatile int g_audio_mode = 0;             

// 語音增強專用參數
   

/* =========================
   Button task
   ========================= */
void button_task(void* arg)
{
    int adc_raw = 0;
    const char* stable_btn = NULL;
    int stable_count = 0;
    bool pressed = false;   // ⭐控制「一次觸發」

    // ==========================================
    // 專門給 BTN6 使用的長按計時與狀態變數
    // ==========================================
    TickType_t btn6_press_start = 0; 
    bool btn6_was_pressed = false;   // 記錄上一次是否正在按 BTN6
    bool ota_has_triggered = false;  // 確保長按只會觸發一次 OTA

    while (1)
    {
        adc_oneshot_read(adc_handle, ADC_CHANNEL_3, &adc_raw);
		//printf("[ADC_DEBUG] Current ADC Value: %d\n", adc_raw);
		const char* btn = get_button(adc_raw);

        /* ==================================================
           區塊 1: RELEASE / IDLE (放開按鍵的瞬間與閒置狀態)
           ================================================== */
        if (btn == NULL)
        {
            // ⭐ BTN6 放開時的邏輯：
            if (btn6_was_pressed) {
                TickType_t press_duration = xTaskGetTickCount() - btn6_press_start;
                
                // 如果是短按 (沒有觸發 5 秒 OTA)
                if (!ota_has_triggered && press_duration > pdMS_TO_TICKS(50)) {
                    // 🚨 這裡已經不需要啟動 Wi-Fi 了，BLE 會在背景隨時待命！
                    ESP_LOGI(TAG, "💡 BTN6 短按！(目前網頁調音已改走 BLE，隨時可用手機連線)");
                }
                
                btn6_was_pressed = false;
                ota_has_triggered = false;
                btn6_press_start = 0;
            }

            stable_btn = NULL;
            stable_count = 0;
            pressed = false;   // ⭐關鍵：允許下一次按鍵觸發
            vTaskDelay(pdMS_TO_TICKS(30));
            continue;
        }

        /* ==================================================
           區塊 2: DEBOUNCE (硬體防彈跳)
           ================================================== */
        if (stable_btn != NULL && strcmp(btn, stable_btn) == 0)
        {
            stable_count++;
        }
        else
        {
            stable_btn = btn;
            stable_count = 0;
        }

        /* ==================================================
           區塊 3: PRESS EVENT (剛按下的第一瞬間，只執行一次)
           ================================================== */
        if (stable_count >= 3 && !pressed)
        {
            pressed = true;   // ⭐防止連發
            ESP_LOGI(TAG, "Button: %s | ADC: %d", btn, adc_raw);

            if (strcmp(btn, "BTN6") == 0)
            {
                // BTN6 剛按下：開始計時，不要馬上做動作！
                btn6_was_pressed = true;
                ota_has_triggered = false;
                btn6_press_start = xTaskGetTickCount();
                ESP_LOGI(TAG, "BTN6 按下，開始計算長按時間...");
            }
            else if (strcmp(btn, "BTN1") == 0)
            {
                ESP_LOGI(TAG, "Action: VOL+");
                if (current_volume <= (0xFF - 10)) current_volume += 10;
                else current_volume = 0xFF;
                i2c_write(0x10, 0x0E, current_volume);
                ESP_LOGI(TAG, "Volume set to: 0x%02X", current_volume);
            }
            else if (strcmp(btn, "BTN2") == 0)
            {
                ESP_LOGI(TAG, "Action: VOL-");
                if (current_volume >= 10) current_volume -= 10;
                else current_volume = 0x00;
                i2c_write(0x10, 0x0E, current_volume);
                ESP_LOGI(TAG, "Volume set to: 0x%02X", current_volume);
            }
            else if (strcmp(btn, "BTN3") == 0)
            {
                ESP_LOGI(TAG, "Action: START AUDIOMETRY");
                g_run_audiometry = true; 
            }
            else if (strcmp(btn, "BTN4") == 0)
            {
                ESP_LOGI(TAG, "Action: PATIENT HEARD TONE");
                g_user_heard_it = true;  
            }
            else if (strcmp(btn, "BTN5") == 0)
            {
                g_audio_mode = (g_audio_mode + 1) % 3; 
                ESP_LOGI("MODE", "=============================");
                switch (g_audio_mode) {
                    case 0: ESP_LOGI("MODE", "🎧 切換至：【一般模式 (通透)】"); break;
                    case 1: ESP_LOGI("MODE", "🔇 切換至：【完整降噪模式 (ANC)】"); break;
                    case 2: ESP_LOGI("MODE", "🗣️ 切換至：【語音增強模式 (Noise Gate)】"); break;
                }
                ESP_LOGI("MODE", "=============================");
            }
        }
        
        /* ==================================================
           區塊 4: HOLD CHECK (按著不放的持續偵測區)
           ================================================== */
        else if (stable_count >= 3 && pressed)
        {
            if (strcmp(btn, "BTN6") == 0)
            {
                if (!ota_has_triggered && btn6_press_start > 0 && 
                   (xTaskGetTickCount() - btn6_press_start) >= pdMS_TO_TICKS(5000)) 
                {
                    ESP_LOGI("BUTTON", "🔥 長按 5 秒達成！準備重啟進入 OTA 更新模式...");
                    ota_has_triggered = true; 
                    g_ota_mode_flag = OTA_MAGIC_NUM; // 寫入魔法數字
                    vTaskDelay(pdMS_TO_TICKS(500));
                    esp_restart(); 
                }
            }
        }

        vTaskDelay(pdMS_TO_TICKS(30));
    }
}

void force_reset_i2s_clocks(void) {
    // 1. 徹底關閉 I2S 通道
    if (tx_handle) {
        i2s_channel_disable(tx_handle);
        i2s_del_channel(tx_handle);
        tx_handle = NULL;
    }
    if (rx_handle) {
        i2s_channel_disable(rx_handle);
        i2s_del_channel(rx_handle);
        rx_handle = NULL;
    }
    // 2. 最關鍵的步驟：給硬體一點時間去清空內部的時脈暫存器
    vTaskDelay(pdMS_TO_TICKS(100)); 
}
void i2s_init_tx(uint32_t sample_rate) {
    ESP_LOGI("I2S", "初始化 TX 通道，目標頻率: %lu Hz", sample_rate);
    
    if (tx_handle != NULL) {
        i2s_channel_disable(tx_handle);
        i2s_del_channel(tx_handle);
        tx_handle = NULL;
    }

    i2s_chan_config_t chan_cfg = I2S_CHANNEL_DEFAULT_CONFIG(I2S_NUM_0, I2S_ROLE_MASTER);
    chan_cfg.auto_clear = true; 

    // 💡 根據頻率動態調整 DMA 緩衝區
    if (sample_rate >= 44100) {
        // 音樂模式：緩衝區要大，防止卡頓
        chan_cfg.dma_desc_num = 8;       
        chan_cfg.dma_frame_num = 128;
    } else {
        // 通話模式 (8k/16k)：緩衝區要小，降低語音延遲
        chan_cfg.dma_desc_num = 6;       
        chan_cfg.dma_frame_num = 120;
    }
    ESP_ERROR_CHECK(i2s_new_channel(&chan_cfg, &tx_handle, NULL));
    
    // 💡 決定時鐘源 (這就是防當機的核心)
    i2s_clock_src_t clock_source;
    if (sample_rate == 44100) {
        clock_source = I2S_CLK_SRC_APLL;    // 音樂用 APLL
    } else {
        clock_source = I2S_CLK_SRC_DEFAULT; // 通話用系統時鐘
    }

    i2s_std_config_t std_cfg = {
        .clk_cfg = {
            .sample_rate_hz = sample_rate, 
            .clk_src = clock_source, 
            .mclk_multiple = I2S_MCLK_MULTIPLE_256, 
        },
        .slot_cfg = {
            .data_bit_width = I2S_DATA_BIT_WIDTH_16BIT, 
            .slot_bit_width = I2S_SLOT_BIT_WIDTH_16BIT, 
            .slot_mode = I2S_SLOT_MODE_STEREO,
            .slot_mask = I2S_STD_SLOT_BOTH,
            .ws_width = I2S_SLOT_BIT_WIDTH_16BIT,
            .ws_pol = false,
            .bit_shift = true,  
            .msb_right = false,
        },
        .gpio_cfg = {
            .mclk = GPIO_NUM_0,  
            .bclk = GPIO_NUM_5,
            .ws   = GPIO_NUM_25,
            .dout = GPIO_NUM_26, 
            .din  = I2S_GPIO_UNUSED,
        },
    };

    ESP_ERROR_CHECK(i2s_channel_init_std_mode(tx_handle, &std_cfg));
    ESP_ERROR_CHECK(i2s_channel_enable(tx_handle));
}
void i2s_init_rx(uint32_t sample_rate) {
    ESP_LOGI("I2S", "初始化 RX 通道，目標頻率: %lu Hz", sample_rate);

    // 1. 如果通道已經存在，先徹底刪除 (砍掉重練，確保時脈與資源完全釋放)
    if (rx_handle != NULL) {
        i2s_channel_disable(rx_handle);
        i2s_del_channel(rx_handle);
        rx_handle = NULL;
    }

    i2s_chan_config_t chan_cfg = I2S_CHANNEL_DEFAULT_CONFIG(I2S_NUM_1, I2S_ROLE_MASTER);
    
    // 2. 根據頻率動態調整 DMA 緩衝區
    if (sample_rate >= 44100) {
        // 音樂/高音質模式
        chan_cfg.dma_desc_num = 6;      
        chan_cfg.dma_frame_num = 128;
    } else {
        // 通話模式 (8k/16k)：水桶縮小，降低麥克風收音延遲
        chan_cfg.dma_desc_num = 6;      
        chan_cfg.dma_frame_num = 120;
    }
    ESP_ERROR_CHECK(i2s_new_channel(&chan_cfg, NULL, &rx_handle));

    // 3. 決定時鐘源 (避開 APLL 佔用衝突的核心)
    i2s_clock_src_t clock_source;
    if (sample_rate == 44100) {
        clock_source = I2S_CLK_SRC_APLL;    // 配合 TX，音樂使用高精度 APLL
    } else {
        clock_source = I2S_CLK_SRC_DEFAULT; // 配合 TX，通話使用系統主時鐘
    }

    i2s_std_config_t std_cfg = {
        .clk_cfg = {
            .sample_rate_hz = sample_rate, 
            .clk_src = clock_source, 
            .mclk_multiple = I2S_MCLK_MULTIPLE_256, 
        },
        .slot_cfg = {
            // ⭐ 錄音端也徹底統一為 16-bit
            .data_bit_width = I2S_DATA_BIT_WIDTH_16BIT,
            .slot_bit_width = I2S_SLOT_BIT_WIDTH_16BIT,
            .slot_mode = I2S_SLOT_MODE_STEREO,
            .slot_mask = I2S_STD_SLOT_BOTH,
            .ws_width = I2S_SLOT_BIT_WIDTH_16BIT,
            .ws_pol = false,
            .bit_shift = true,  // Philips I2S 標準 (必開)
            .msb_right = false,
        },
        .gpio_cfg = {
            .mclk = I2S_GPIO_UNUSED, // MCLK 已經由 I2S0 輸出，這裡設 UNUSED 避免衝突
            .bclk = GPIO_NUM_32,
            .ws   = GPIO_NUM_33,
            .din  = GPIO_NUM_36,     // 接收來自 ES7243E 的聲音
            .dout = I2S_GPIO_UNUSED,
        },
    };

    ESP_ERROR_CHECK(i2s_channel_init_std_mode(rx_handle, &std_cfg));
    ESP_ERROR_CHECK(i2s_channel_enable(rx_handle));
}

/*
void i2s_init_tx(void) {
    i2s_chan_config_t chan_cfg = I2S_CHANNEL_DEFAULT_CONFIG(I2S_NUM_0, I2S_ROLE_MASTER);
	chan_cfg.dma_desc_num = 8;       // 預設是 6。增加 DMA 區塊數量，加長緩衝跑道
	chan_cfg.dma_frame_num = 128;   // 預設是 240。大幅增加每個區塊的容量
	chan_cfg.auto_clear = true;      // ⭐ 最關鍵的一行！發生斷糧時自動補 0 (靜音)
	ESP_ERROR_CHECK(i2s_new_channel(&chan_cfg, &tx_handle, NULL));
    i2s_std_config_t std_cfg = {
        .clk_cfg = {
            .sample_rate_hz = 48000, // 請確保這裡與你 A2DP 目標頻率一致 (44100 或 48000)
            .clk_src = I2S_CLK_SRC_APLL, // 放音強烈建議用 APLL 確保無 Jitter 高音質
            .mclk_multiple = I2S_MCLK_MULTIPLE_256, // ES8311 官方推薦 256 倍 MCLK
        },
        .slot_cfg = {
            // ⭐ 這裡徹底統一為 16-bit
            .data_bit_width = I2S_DATA_BIT_WIDTH_16BIT, 
            .slot_bit_width = I2S_SLOT_BIT_WIDTH_16BIT, 
            .slot_mode = I2S_SLOT_MODE_STEREO,
            .slot_mask = I2S_STD_SLOT_BOTH,
            .ws_width = I2S_SLOT_BIT_WIDTH_16BIT,
            .ws_pol = false,
            .bit_shift = true,  // Philips I2S 標準 (必開)
            .msb_right = false,
        },
        .gpio_cfg = {
            .mclk = GPIO_NUM_0,  // 給 ES8311 的系統時鐘
            .bclk = GPIO_NUM_5,
            .ws   = GPIO_NUM_25,
            .dout = GPIO_NUM_26, // 聲音送到 ES8311
            .din  = I2S_GPIO_UNUSED,
        },
    };

    ESP_ERROR_CHECK(i2s_channel_init_std_mode(tx_handle, &std_cfg));
    ESP_ERROR_CHECK(i2s_channel_enable(tx_handle));
}
*/
// =======================================================
// RX 初始化: I2S_NUM_1 <- ES7243E (ADC 錄音)
// =======================================================
/*
void i2s_init_rx(void) {
    i2s_chan_config_t chan_cfg = I2S_CHANNEL_DEFAULT_CONFIG(I2S_NUM_1, I2S_ROLE_MASTER);
    chan_cfg.dma_desc_num = 6;      // 維持 6 個水桶 (跑道短)
    chan_cfg.dma_frame_num = 128;
	ESP_ERROR_CHECK(i2s_new_channel(&chan_cfg, NULL, &rx_handle));

    i2s_std_config_t std_cfg = {
        .clk_cfg = {
            .sample_rate_hz = 48000, // 務必與 TX 保持一致！
            .clk_src = I2S_CLK_SRC_APLL, 
            .mclk_multiple = I2S_MCLK_MULTIPLE_256, 
        },
        .slot_cfg = {
            // ⭐ 錄音端也徹底統一為 16-bit
            .data_bit_width = I2S_DATA_BIT_WIDTH_16BIT,
            .slot_bit_width = I2S_SLOT_BIT_WIDTH_16BIT,
            .slot_mode = I2S_SLOT_MODE_STEREO,
            .slot_mask = I2S_STD_SLOT_BOTH,
            .ws_width = I2S_SLOT_BIT_WIDTH_16BIT,
            .ws_pol = false,
            .bit_shift = true,  // Philips I2S 標準 (必開)
            .msb_right = false,
        },
        .gpio_cfg = {
            .mclk = I2S_GPIO_UNUSED, // MCLK 已經由 I2S0 在 GPIO0 輸出，這裡設 UNUSED 避免衝突
            .bclk = GPIO_NUM_32,
            .ws   = GPIO_NUM_33,
            .din  = GPIO_NUM_36,     // 接收來自 ES7243E 的聲音
            .dout = I2S_GPIO_UNUSED,
        },
    };

    ESP_ERROR_CHECK(i2s_channel_init_std_mode(rx_handle, &std_cfg));
    ESP_ERROR_CHECK(i2s_channel_enable(rx_handle));
}

*/
// ================= I2C =================
void i2c_init()
{
    i2c_config_t conf = {
        .mode = I2C_MODE_MASTER,
        .sda_io_num = I2C_SDA,
        .scl_io_num = I2C_SCL,
        .sda_pullup_en = GPIO_PULLUP_ENABLE,
        .scl_pullup_en = GPIO_PULLUP_ENABLE,
        .master.clk_speed = 100000,
    };

    i2c_param_config(I2C_NUM_0, &conf);
    i2c_driver_install(I2C_NUM_0, I2C_MODE_MASTER, 0, 0, 0);

    ESP_LOGI(TAG, "I2C READY");
}


uint8_t i2c_read_reg(uint8_t addr, uint8_t reg)
{
    uint8_t val = 0;

    i2c_master_write_read_device(
        I2C_NUM_0,
        addr,
        &reg,
        1,
        &val,
        1,
        1000 / portTICK_PERIOD_MS
    );

    return val;
}

void i2c_scan()
{
    for (int addr = 1; addr < 127; addr++)
    {
        i2c_cmd_handle_t cmd = i2c_cmd_link_create();

        i2c_master_start(cmd);
        i2c_master_write_byte(cmd, (addr << 1) | I2C_MASTER_WRITE, true);
        i2c_master_stop(cmd);

        esp_err_t ret = i2c_master_cmd_begin(I2C_NUM_0, cmd, 100 / portTICK_PERIOD_MS);
        i2c_cmd_link_delete(cmd);

        if (ret == ESP_OK)
        {
            printf("FOUND: 0x%02X\n", addr);
        }
    }
}
uint8_t es7243e_read(uint8_t reg)
{
    uint8_t val = 0;

    i2c_master_write_read_device(
        I2C_NUM_0,
        ES7243E_ADDR,
        &reg,
        1,
        &val,
        1,
        1000 / portTICK_PERIOD_MS
    );

    return val;
}

void es7243e_init(void)
{	
	ESP_LOGI("ES7243E", "INIT START");
	i2c_write(0x10, 0x01, 0x3A);
    i2c_write(0x10, 0x00, 0x80);
    i2c_write(0x10, 0xF9, 0x00);
    i2c_write(0x10, 0x04, 0x02);
    i2c_write(0x10, 0x04, 0x01);
    i2c_write(0x10, 0xF9, 0x01);
    i2c_write(0x10, 0x00, 0x1E);
    i2c_write(0x10, 0x01, 0x00);

    // --- 2. 時鐘與格式設定 ---
    i2c_write(0x10, 0x02, 0x00);
    i2c_write(0x10, 0x03, 0x20);
    i2c_write(0x10, 0x04, 0x01);
    i2c_write(0x10, 0x0D, 0x00);
    i2c_write(0x10, 0x05, 0x00);
    
    // ⭐ 修改 1：將 BCLK 分頻從預設的 MCLK/4 (0x03) 改為 MCLK/8 (0x07)
    i2c_write(0x10, 0x06, 0x07); 
    
    // LRCK 維持 MCLK/256 不變
    i2c_write(0x10, 0x07, 0x00); 
    i2c_write(0x10, 0x08, 0xFF); 

    // --- 3. 原廠濾波器參數與偏壓 ---
    i2c_write(0x10, 0x09, 0xCA);
    i2c_write(0x10, 0x0A, 0x85);
    
    // ⭐ 修改 2：將音訊格式從預設的 24-bit (0x00) 改為 16-bit (0x0C)
    i2c_write(0x10, 0x0B, 0x0C); 
    
    i2c_write(0x10, 0x0E, 0xBF);
    i2c_write(0x10, 0x0F, 0x80);
    i2c_write(0x10, 0x14, 0x0C);
    i2c_write(0x10, 0x15, 0x0C);
    i2c_write(0x10, 0x17, 0x02);
    i2c_write(0x10, 0x18, 0x26);
    i2c_write(0x10, 0x19, 0x77);
    i2c_write(0x10, 0x1A, 0xF4);
    i2c_write(0x10, 0x1B, 0x66);
    i2c_write(0x10, 0x1C, 0x44);
    i2c_write(0x10, 0x1E, 0x00);
    i2c_write(0x10, 0x1F, 0x0C);
    
    i2c_write(0x10, 0xF9, 0x00);
    i2c_write(0x10, 0x04, 0x01);
    i2c_write(0x10, 0x17, 0x01);
    i2c_write(0x10, 0x20, 0x1c);
    i2c_write(0x10, 0x21, 0x1c);
    i2c_write(0x10, 0x00, 0x80);
    i2c_write(0x10, 0x01, 0x3A);
    i2c_write(0x10, 0x16, 0x3F);
    i2c_write(0x10, 0x16, 0x00);
	
	
	ESP_LOGI("ES7243E", "INIT DONE");
}





void es7243e_dump_telemetry(void)
{
    ESP_LOGI(TAG, "========= ES7243E R&D TELEMETRY (DATASHEET ACCURATE) =========");

    // --- 1. 讀取所有關鍵暫存器 ---
    uint8_t reg00 = es7243e_read_reg(0x00); // 系統與主從模式
    uint8_t reg06 = es7243e_read_reg(0x06); // BCLK 分頻比
    uint8_t reg07 = es7243e_read_reg(0x07); // LRCK 分頻比 High
    uint8_t reg08 = es7243e_read_reg(0x08); // LRCK 分頻比 Low
    uint8_t reg0B = es7243e_read_reg(0x0B); // I2S/SDP 格式、位元長度與靜音
    uint8_t reg16 = es7243e_read_reg(0x16); // 類比電源管理 (PDN_ANA)
    uint8_t reg20 = es7243e_read_reg(0x20); // CH1 (L) PGA 與麥克風選擇
    uint8_t reg21 = es7243e_read_reg(0x21); // CH2 (R) PGA 與麥克風選擇

    // --- [輔助解析巨集] ---
    const char* fmt_str[] = {"I2S", "Left-J", "RSV", "DSP/PCM"};
    const char* wl_str[] = {"24-bit", "20-bit", "18-bit", "16-bit", "32-bit"};
    
    // 建立 PGA 增益轉換表 (Reg0x20/0x21 Bit3:0)
    const float pga_db[] = {0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 34.5, 36, 37.5};

    // --- [Block A: 系統與通訊角色 (System & Role)] ---
    ESP_LOGI(TAG, "[A. System & Mode]");
    ESP_LOGI(TAG, " - FSM State     : %s (Reg 0x00 Bit7)", (reg00 & 0x80) ? "RUNNING (Power Up)" : "STANDBY (Power Down)");
    ESP_LOGI(TAG, " - I2S Role      : %s (Reg 0x00 Bit6)", (reg00 & 0x40) ? "MASTER (Codec gives Clock)" : "SLAVE (ESP32 gives Clock)");

    // --- [Block B: I2S 音訊格式 (Format & Mute)] ---
    ESP_LOGI(TAG, "[B. I2S Format (SDP)]");
    uint8_t fmt_idx = reg0B & 0x03;
    uint8_t wl_idx = (reg0B >> 2) & 0x07;
    uint8_t mute_st = (reg0B >> 6) & 0x03;
    
    ESP_LOGI(TAG, " - Data Format   : %s (Reg 0x0B Bit1:0)", (fmt_idx <= 3) ? fmt_str[fmt_idx] : "ERR");
    ESP_LOGI(TAG, " - Word Length   : %s (Reg 0x0B Bit4:2)", (wl_idx <= 4) ? wl_str[wl_idx] : "24-bit (Default)");
    ESP_LOGI(TAG, " - SDP Mute      : %s (Reg 0x0B Bit7:6)", (mute_st == 3) ? "MUTED (L/R Silent)" : (mute_st == 0) ? "UNMUTED (Audio Flowing)" : "PARTIAL MUTE");

    // --- [Block C: 時鐘分頻 (Clock Dividers)] ---
    ESP_LOGI(TAG, "[C. Clock Dividers]");
    ESP_LOGI(TAG, " - BCLK Div      : MCLK / %d (Reg 0x06)", (reg06 & 0x7F) + 1);
    uint16_t lrck_div = ((reg07 & 0x0F) << 8) | reg08;
    ESP_LOGI(TAG, " - LRCK Div      : MCLK / %d (Reg 0x07/0x08)", lrck_div + 1);

    // --- [Block D: 類比前端與麥克風放大 (Analog & PGA)] ---
    ESP_LOGI(TAG, "[D. Analog Path]");
    ESP_LOGI(TAG, " - Analog Power  : %s (Reg 0x16=0x%02X)", (reg16 == 0x00) ? "ALL ON" : "PARTIALLY POWERED DOWN", reg16);
    
    uint8_t pga1_idx = reg20 & 0x0F;
    uint8_t pga2_idx = reg21 & 0x0F;
    ESP_LOGI(TAG, " - CH1(L) Input  : %s, Gain: +%.1f dB", (reg20 & 0x10) ? "MIC1" : "Default", (pga1_idx <= 14) ? pga_db[pga1_idx] : 0);
    ESP_LOGI(TAG, " - CH2(R) Input  : %s, Gain: +%.1f dB", (reg21 & 0x10) ? "MIC2" : "Default", (pga2_idx <= 14) ? pga_db[pga2_idx] : 0);

    ESP_LOGI(TAG, "===============================================================");
}
	

void es8311_init(void)
{
	i2c_write(0x18, 0x44, 0x08);
	/* Due to occasional failures during the first I2C write with the ES8311 chip, a second write is performed to ensure reliability */
	i2c_write(0x18, 0x44, 0x08);
	
    i2c_write(0x18, 0x01, 0x30);
    vTaskDelay(pdMS_TO_TICKS(50)); // 給它時間醒過來
	i2c_write(0x18, 0x02, 0x00);
	i2c_write(0x18, 0x16, 0x24);
	i2c_write(0x18, 0x05, 0x00);
	i2c_write(0x10, 0x04, 0x40);
	i2c_write(0x18, 0x0B, 0x00);
	i2c_write(0x18, 0x0C, 0x00);
	i2c_write(0x18, 0x10, 0x1F);
	i2c_write(0x18, 0x11, 0x7C);
	i2c_write(0x18, 0x00, 0x80);

	i2c_write(0x18, 0x12, 0x00); // 打開 DAC (PDN_DAC=0, ENREFR=1)
	i2c_write(0x18, 0x13, 0x10); // 打開 HP driver (HPSW=1)

	i2c_write(0x18, 0x10, 0x1F); // DAC 數位音量

	i2c_write(0x18, 0x33, 0x3F); //
	i2c_write(0x18, 0x0c, 0x10);
	i2c_write(0x18, 0x31, 0x80);
	i2c_write(0x18, 0x33, 0x20);

	i2c_write(0x18, 0x01, 0x3F);
	i2c_write(0x18, 0x09, 0x0c);
	i2c_write(0x18, 0x0a, 0x0c);
	i2c_write(0x18, 0x37, 0x08);

	i2c_write(0x18, 0x32, 0xB0);
	i2c_write(0x18, 0x12, 0x01); // 打開 DAC (PDN_DAC=0, ENREFR=1)
}


void dump_7243e(void)
{
    ESP_LOGI("DUMP", "===== ES7243E REGISTER DUMP =====");

    for (int reg = 0x00; reg <= 0xFF; reg++)
    {
        uint8_t val = i2c_read_reg(0x10, reg);
        printf("7243E[0x%02X] = 0x%02X\n", reg, val);
        vTaskDelay(pdMS_TO_TICKS(2)); // avoid I2C overload
    }

    ESP_LOGI("DUMP", "===== DONE =====");
}
void dump_8311(void)
{
    ESP_LOGI("DUMP", "===== ES8311 REGISTER DUMP =====");

    for (int reg = 0x00; reg <= 0x7E; reg++)
    {
        uint8_t val = i2c_read_reg(0x18, reg);
        printf("8311[0x%02X] = 0x%02X\n", reg, val);
        vTaskDelay(pdMS_TO_TICKS(2));
    }

    ESP_LOGI("DUMP", "===== DONE =====");
}

//I2S_VALUE//
int get_mic_samples(int16_t *out_buf, int max_samples)
{
    size_t bytes = 0;

    esp_err_t ret = i2s_channel_read(
        rx_handle,
        out_buf,
        max_samples * sizeof(int16_t),
        &bytes,
        pdMS_TO_TICKS(1000)
    );

    if (ret != ESP_OK)
    {
        ESP_LOGE("I2S", "read failed");
        return 0;
    }

    return bytes / sizeof(int16_t);
}
void test_mic(void) {
    int32_t samples[256];
    size_t bytes_read = 0;
    i2s_channel_read(rx_handle, samples, sizeof(samples), &bytes_read, portMAX_DELAY);

    for (int i = 0; i < 10; i += 2) {
        // 取得高位的 16-bit
        int16_t left = (int16_t)(samples[i] >> 16);
        int16_t right = (int16_t)(samples[i + 1] >> 16);

        // 同時印出十六進位觀察 MSB 是否正確
        printf("L=%d, R=%d (Raw: 0x%08X)\n", left, right, (unsigned int)samples[i]);
    }
}


//I2S_VALUE//
// ================= UART SHELL =================
const char* CMD_LIST[] = {
    // ==========================================
    // 1. 系統模式與調音台 (Mixer & Mode)
    // ==========================================
    "mode=",
    "set_master_vol",
    "set_sidetone",
    "set_callvol",
    "status_hp_vol",
    "save_all",
    "load_default",

    // ==========================================
    // 2. ANC 降噪與語音增強 (ANC & VAD)
    // ==========================================
    "set_delay",
    "set_gain",
    "statusfft",
    "freq=",
    "set_gate",
    "read_gate",
    "set_limit_bigsound",
    "read_limit_bigsound",

    // ==========================================
    // 3. EQ 等化器與硬體校正 (EQ & Calibration)
    // ==========================================
    "eq",
    "show_eq",
    "set_mic",
    "set_spk",
    "spk_test",

    // ==========================================
    // 4. 硬體周邊與狀態測試 (Hardware Test)
    // ==========================================
    "PA=1",
    "PA=0",
    "SL1=1",
    "SL1=0",
    "SL2=1",
    "SL2=0",
    "check_HP",
    "mic",
    "i2sset",
    "changeto16k",
    "changeto48k",
    "changeto44p1k",

    // ==========================================
    // 5. I2C 暫存器操作 (Codec Debug)
    // ==========================================
    "scan",
    "init7243",
    "init8311",
    "status7243",
    "status8311",
    "r7243e",
    "r8311",
    "w7243e",
    "w8311",

    // ==========================================
    // 6. 系統幫助
    // ==========================================
    "help",
    "?"
};

// 小提醒：你可以用這個常數來自動取得陣列長度，以後加指令就不用手動改數字了！
const int CMD_LIST_SIZE = sizeof(CMD_LIST) / sizeof(CMD_LIST[0]);
const int CMD_COUNT = sizeof(CMD_LIST) / sizeof(CMD_LIST[0]);
void uart_shell_task(void *arg)
{
    uint8_t ch;
    char buf[128];
    int idx = 0;

    // 印出一個命令提示字元
    const char* prompt = "\r\nESP_Debug ";
    uart_write_bytes(UART_NUM, prompt, strlen(prompt));

    while (1)
    {
        int len = uart_read_bytes(UART_NUM, &ch, 1, portMAX_DELAY);

        if (len > 0)
        {
            // [處理 1] Backspace 或 Delete 鍵
            if (ch == '\b' || ch == 0x7F) 
            {
                if (idx > 0) 
                {
                    idx--;
                    buf[idx] = '\0';
                    // 終端機魔法：退格 -> 印空白蓋掉 -> 再退格
                    uart_write_bytes(UART_NUM, "\b \b", 3);
                }
            }
            // [處理 2] Tab 鍵自動補齊
            else if (ch == '\t')
            {
                if (idx > 0) 
                {
                    int match_idx = -1;
                    int match_count = 0;

                    // 尋找符合前綴的指令
                    for (int i = 0; i < CMD_COUNT; i++) {
                        if (strncmp(buf, CMD_LIST[i], idx) == 0) {
                            match_idx = i;
                            match_count++;
                        }
                    }

                    // 如果只有一個完美匹配，就自動補齊！
                    if (match_count == 1) {
                        const char* target = CMD_LIST[match_idx];
                        int remain_len = strlen(target) - idx;
                        
                        // 印出剩下的字
                        uart_write_bytes(UART_NUM, &target[idx], remain_len);
                        
                        // 把完整的指令塞進 buf
                        strcpy(buf, target);
                        idx = strlen(buf);
                    }
                    // (進階) 如果有多個匹配，可以把符合的指令印出來提示使用者，這裡先保持簡單
                }
            }
            // [處理 3] Enter 鍵 (執行指令)
            else if (ch == '\n' || ch == '\r')
            {
                uart_write_bytes(UART_NUM, "\r\n", 2); // 換行
                buf[idx] = '\0';

                if (strlen(buf) > 0)
                {
                    process_cmd(buf); // 執行你的指令
                }
                
                idx = 0; // 重置 buffer
                buf[0] = '\0';
                uart_write_bytes(UART_NUM, prompt, strlen(prompt)); // 再次印出提示字元 "> "
            }
            // [處理 4] 一般輸入字元
            else
            {
                // 確保是可印出的 ASCII 字元 (防呆，避免方向鍵等奇怪控制碼搞亂畫面)
                if (ch >= 0x20 && ch <= 0x7E && idx < sizeof(buf) - 1)
                {
                    buf[idx++] = ch;
                    uart_write_bytes(UART_NUM, (const char*)&ch, 1); // 回顯 (Echo)
                }
            }
        }
    }
}
#define BUFFER_SIZE 512
void mic_task(void *arg)
{
    uint8_t *audio_buffer = (uint8_t *)malloc(BUFFER_SIZE);
    if (audio_buffer == NULL) {
        ESP_LOGE("LOOPBACK", "記憶體分配失敗!");
        vTaskDelete(NULL);
        return;
    }

    size_t bytes_read = 0;
    size_t bytes_written = 0;
    
    ESP_LOGI("LOOPBACK", "--- 雙聲道直通任務啟動 ---");
    ESP_LOGI("LOOPBACK", "請戴上耳機，對著麥克風講話！");

    while (1)
    {
        // 1. 讀取 ES7243E 的雙聲道資料 (L, R, L, R...)
        esp_err_t rx_res = i2s_channel_read(rx_handle, audio_buffer, BUFFER_SIZE, &bytes_read, portMAX_DELAY);
        
        if (rx_res == ESP_OK && bytes_read > 0)
        {
            // 2. 直接將這包雙聲道資料，原封不動寫給 ES8311 播放
            i2s_channel_write(tx_handle, audio_buffer, bytes_read, &bytes_written, portMAX_DELAY);
        }
        else
        {
            ESP_LOGE("LOOPBACK", "讀取 RX 失敗: 0x%x", rx_res);
            vTaskDelay(pdMS_TO_TICKS(100)); // 避免出錯時狂洗畫面
        }
    }
}


void print_i2s_status_reading(void) {
    

    printf("\n========================================================\n");
    printf(">>>>>> ESP32 I2S HARDWARE TELEMETRY (TX & RX) <<<<<<\n");
    printf(" - A2DP Target Rate : %lu Hz\n", (unsigned long)current_a2dp_sample_rate);
    printf("--------------------------------------------------------\n");

    // --- [ 1. 讀取 I2S_NUM_0 (負責 TX 放音 / DAC) ] ---
    i2s_dev_t *i2s0_hw = &I2S0; 
    
    uint32_t tx_hw_bits = i2s0_hw->sample_rate_conf.tx_bits_mod;
    uint32_t tx_msb_shift = i2s0_hw->conf.tx_msb_shift;
    uint32_t tx_bclk_div = i2s0_hw->clkm_conf.clkm_div_num;

    printf("[I2S_NUM_0 -> TX Playback]\n");
    printf(" - HW Bit Width : %lu-bit\n", tx_hw_bits);
    printf(" - I2S Format   : %s\n", tx_msb_shift ? "Philips (Standard)" : "Left-Justified");
    printf(" - BCLK Divider : %lu\n", tx_bclk_div);
    printf("--------------------------------------------------------\n");

    // --- [ 2. 讀取 I2S_NUM_1 (負責 RX 錄音 / ADC) ] ---
    i2s_dev_t *i2s1_hw = &I2S1; 
    
    // 注意：這裡是讀取 rx_bits_mod 和 rx_msb_shift
    uint32_t rx_hw_bits = i2s1_hw->sample_rate_conf.rx_bits_mod;
    uint32_t rx_msb_shift = i2s1_hw->conf.rx_msb_shift;
    uint32_t rx_bclk_div = i2s1_hw->clkm_conf.clkm_div_num;

    printf("[I2S_NUM_1 <- RX Record]\n");
    printf(" - HW Bit Width : %lu-bit\n", rx_hw_bits);
    printf(" - I2S Format   : %s\n", rx_msb_shift ? "Philips (Standard)" : "Left-Justified");
    printf(" - BCLK Divider : %lu\n", rx_bclk_div);
    printf("========================================================\n");
}


// ================= COMMAND PARSER =================
void process_cmd(char *line)
{
    ESP_LOGI(TAG, "CMD: %s", line);

    int reg, val;

    // -------- scan --------
    if (strcmp(line, "scan") == 0)
    {
        i2c_scan();
    }
	// dump r7243e//
	else if (strcmp(line, "r7243e") == 0)
    {
        dump_7243e();
    }
	// dump 8311//
    else if (strcmp(line, "r8311") == 0)
    {
        dump_8311();
    }
    // -------- es8311 read --------
    else if (strncmp(line, "r8311", 5) == 0)
    {
        sscanf(line + 6, "%x", &reg);
        val = i2c_read(0x18, reg);
        ESP_LOGI(TAG, "ES8311[0x%02X]=0x%02X", reg, val);
    }

    // -------- es7243e read --------
    else if (strncmp(line, "r7243e", 5) == 0)
    {
        sscanf(line + 6, "%x", &reg);
        val = i2c_read(0x10, reg);
        ESP_LOGI(TAG, "ES7243E[0x%02X]=0x%02X", reg, val);
    }
	else if (strncmp(line, "status7243", 10) == 0)
    {
        es7243e_dump_telemetry();
    }
	else if (strncmp(line, "status8311", 10) == 0)
    {
        es8311_i2s_config_debug();
    }
    // -------- write es8311 --------
    else if (strncmp(line, "w8311", 5) == 0)
    {
        sscanf(line + 6, "%x %x", &reg, &val);
        i2c_write(0x18, reg, val);
		i2c_read(0x18,reg);
		es8311_i2s_config_debug();
    }
	else if (strncmp(line, "init7243", 8) == 0)
    {
        es7243e_init();
    }
	else if (strncmp(line, "init8311", 8) == 0)
    {
        es8311_init();
    }
	else if (strncmp(line, "set_gain ", 9) == 0)
    {
        float val = 0;
		if (sscanf(line + 9, "%f", &val) == 1) {
			if (val >= 0.0f && val <= 1.0f) {
				g_anc_gain = val;
				printf("\r\n[SHELL] ⚡ 降噪增益已變更為: %.2f\r\n", g_anc_gain);
			} else {
				printf("\r\n[SHELL] ❌ 錯誤：增益範圍必須在 0.0 到 1.0 之間！\r\n");
			}
		}
    }
	else if (strncmp(line, "set_delay ", 10) == 0)
    {
        int val = 0;
		if (sscanf(line + 10, "%d", &val) == 1) {
			if (val >= 0 && val <= 64) {
				g_phase_delay_samples = val;
				printf("\r\n[SHELL] ⚡ 相位延遲已變更為: %d samples (大約 %.1f 微秒)\r\n", 
					   g_phase_delay_samples, g_phase_delay_samples * (1000000.0 / 48000.0));
			} else {
				printf("\r\n[SHELL] ❌ 錯誤：延遲點數必須在 0 到 64 之間！\r\n");
			}
		}
    }
	else if (strcmp(line, "statusfft") == 0)
    {
        printf("\r\n=== 🎛️ 當前 ANC 調音面板狀態 ===\r\n");
        printf(" - 降噪增益 (g_anc_gain)           : %.2f\r\n", g_anc_gain);
        printf(" - 相位延遲 (g_phase_delay_samples): %d 點\r\n", g_phase_delay_samples);
        printf("=================================\r\n");
    }
    // -------- write es7243e --------
    else if (strncmp(line, "w7243e", 5) == 0)
    {
        sscanf(line + 6, "%x %x", &reg, &val);
        i2c_write(0x10, reg, val);
    }
	else if (strcmp(line, "mic") == 0)
	{
		test_mic();
	}
	else if (strcmp(line, "PA=0") == 0)
	{
		gpio_set_level(GPIO_NUM_21, 0);
		ESP_LOGI(TAG, "PA_GPIO21 = 0");
	}
	else if (strcmp(line, "PA=1") == 0)
	{
		gpio_set_level(GPIO_NUM_21, 1);
		ESP_LOGI(TAG, "PA_GPIO21 = 1");
	}
	else if (strcmp(line, "SL1=1") == 0)
	{
		gpio_set_level(BOARD_SY_LED1, 1);
		ESP_LOGI(TAG, "BOARD_SY_LED1 = 1");
	}
	else if (strcmp(line, "SL1=0") == 0)
	{
		gpio_set_level(BOARD_SY_LED1, 0);
		ESP_LOGI(TAG, "BOARD_SY_LED1 = 0");
	}
	else if (strcmp(line, "SL2=1") == 0)
	{
		gpio_set_level(BOARD_SY_LED2, 1);
		ESP_LOGI(TAG, "BOARD_SY_LED2 = 1");
	}
	else if (strcmp(line, "SL2=0") == 0)
	{
		gpio_set_level(BOARD_SY_LED2, 0);
		ESP_LOGI(TAG, "BOARD_SY_LED2 = 0");
	}
	
	else if (strcmp(line, "i2sset") == 0)
	{
		if (tx_handle != NULL) 
		{
			print_i2s_status_reading();
		} 
		else 
		{
			printf("I2S handle is NULL, please init I2S first.\n");
		}
	}
	else if (strcmp(line, "check_HP") == 0)
	{
		int state = gpio_get_level(GPIO_NUM_19);

		if (state == 0) 
		{
			ESP_LOGI(HP_TAG, "耳機插入 (Low)");
		} 
		else 
		{
			ESP_LOGI(HP_TAG, "耳機拔出 (High)");
		}
		last_state = state;
		
	}
	else if (strncmp(line, "freq=", 5) == 0)
    {
        float new_freq;
        // 從字串第 5 個字元開始讀取數值
        if (sscanf(line + 5, "%f", &new_freq) == 1) {
            if (new_freq > 0 && new_freq < 8000.0) {
                current_freq = new_freq;
                printf("Frequency updated to: %.2f Hz\n", current_freq);
            } else {
                printf("Invalid frequency range (0-8000Hz)\n");
            }
        } else {
            printf("Error: Invalid format. Use 'freq=100'\n");
        }
    }
	else if (strncmp(line, "mode=", 5) == 0)
    {
        int new_mode;
        // 從字串第 5 個字元開始讀取整數數值
        if (sscanf(line + 5, "%d", &new_mode) == 1) {
            // 檢查是否在合法範圍 (0 到 2)
            if (new_mode >= 0 && new_mode <= 2) {
                g_audio_mode = new_mode; // 更新全域模式變數
                
                // 印出超有儀式感的狀態 Log
                ESP_LOGI("MODE", "=============================");
                switch (g_audio_mode) {
                    case 0:
                        ESP_LOGI("MODE", "🎧 UART 指令切換：【一般模式 (通透)】");
                        break;
                    case 1:
                        ESP_LOGI("MODE", "🔇 UART 指令切換：【完整降噪模式 (ANC)】");
                        break;
                    case 2:
                        ESP_LOGI("MODE", "🗣️ UART 指令切換：【語音增強模式 (Noise Gate)】");
                        break;
                }
                ESP_LOGI("MODE", "=============================");
            } else {
                printf("Error: 模式超出範圍！請輸入 0(通透), 1(降噪) 或 2(語音增強)\n");
            }
        } else {
            printf("Error: 格式錯誤。請使用 'mode=0', 'mode=1' 或 'mode=2'\n");
        }
    }
	else if (strncmp(line, "set_gate ", 9) == 0)
    {
        int val = 0;
        if (sscanf(line + 9, "%d", &val) == 1) {
            // 麥克風數值最大極限是 32767
            if (val >= 0 && val <= 32767) {
                g_noise_gate_threshold = (int16_t)val;
                printf("\r\n[SHELL] 🗣️ 噪音閘門閥值已變更為: %d\r\n", g_noise_gate_threshold);
            } else {
                printf("\r\n[SHELL] ❌ 錯誤：閥值範圍必須在 0 到 32767 之間！\r\n");
            }
        }
    }
	else if (strcmp(line, "read_gate") == 0)
    {
        printf("\r\n[SHELL] 🗣️ 當前噪音閘門閥值 (Gate Threshold): %d\r\n", g_noise_gate_threshold);
    }
	else if (strcmp(line, "changeto16k") == 0)
	{
		printf("測試16KHz 設定");
		g_i2s_is_reconfiguring=true;
		i2s_init_tx(16000);
		i2s_init_rx(16000);
		current_a2dp_sample_rate=16000;
		vTaskDelay(pdMS_TO_TICKS(100));
		printf("測試16KHz 設定__Re-config 16kHz complete");
		es8311_config_sample(16000);
		i2c_write(0x18,0x12,0x00);//////DAC ON
		update_8band_eq(16000);
		print_i2s_status_reading();
		es8311_i2s_config_debug();
		g_i2s_is_reconfiguring=false;
	}
	else if (strcmp(line, "changeto48k") == 0)
	{
		printf("測試48KHz 設定");
		g_i2s_is_reconfiguring=true;
		i2s_init_tx(48000);
		i2s_init_rx(48000);
		current_a2dp_sample_rate=48000;
		vTaskDelay(pdMS_TO_TICKS(100));
		printf("測試16KHz 設定__Re-config 48kHz complete");
		es8311_init();
		es7243e_init();
		es8311_config_sample(48000);
		i2c_write(0x18,0x12,0x00);//////DAC ON
		update_8band_eq(48000);
		print_i2s_status_reading();
		es8311_i2s_config_debug();
		g_i2s_is_reconfiguring=false;
	}
	else if (strcmp(line, "changeto44p1k") == 0)
	{
		printf("測試44.1KHz 設定");
		g_i2s_is_reconfiguring=true;
		i2s_init_tx(44100);
		i2s_init_rx(44100);
		current_a2dp_sample_rate=44100;
		vTaskDelay(pdMS_TO_TICKS(100));
		printf("測試16KHz 設定__Re-config 44.1kHz complete");
		es8311_init();
		es7243e_init();
		es8311_config_sample(44100);
		update_8band_eq(44100);
		i2c_write(0x18,0x12,0x00);//////DAC ON
		print_i2s_status_reading();
		es8311_i2s_config_debug();
		g_i2s_is_reconfiguring=false;
	}
	
	else if (strncmp(line, "eq ", 3) == 0) 
    {
        int band_idx; float gain_val;
        if (sscanf(line, "eq %d %f", &band_idx, &gain_val) == 2) {
            if (band_idx >= 0 && band_idx < 8) {
                extern volatile float g_user_eq[8];
                extern volatile float g_auto_offset[8];
                extern volatile float g_target_gains_db[8];
                
                // 1. 更新使用者基準值
                g_user_eq[band_idx] = gain_val;
                
                // 2. 重新計算最終目標值 (基準 + 防護)
                g_target_gains_db[band_idx] = g_user_eq[band_idx] + g_auto_offset[band_idx];
                
                update_8band_eq(current_a2dp_sample_rate);
                ESP_LOGW("TUNING", "✅ Band %d 基準已變更為 %.1f dB (實際輸出: %.1f dB)", band_idx, g_user_eq[band_idx], g_target_gains_db[band_idx]);
            }
        }
    }
        
        // 📝 2. 查看當前 EQ 狀態指令
    else if (strcmp(line, "show_eq") == 0) {
        ESP_LOGI("TUNING", "當前 EQ 設定: [0]:%.1f  [1]:%.1f  [2]:%.1f  [3]:%.1f  [4]:%.1f  [5]:%.1f  [6]:%.1f  [7]:%.1f",
                 g_target_gains_db[0], g_target_gains_db[1], g_target_gains_db[2], g_target_gains_db[3],
                 g_target_gains_db[4], g_target_gains_db[5], g_target_gains_db[6], g_target_gains_db[7]);
    }
    // ✅ 貼上這三個新的校正指令
    // 🎤 1. 即時修改麥克風校正值 (用 iPhone 測完環境音後輸入，例如: set_mic 99)
    // 🎤 1. 產線寫入麥克風校正值 (例如: set_mic 99.5)
    else if (strncmp(line, "set_mic ", 8) == 0)
    {
        float val = 0;
        if (sscanf(line + 8, "%f", &val) == 1) {
            g_mic_calib_offset = val;
            save_calibration_to_flash("mic_calib", g_mic_calib_offset); // 寫入 Flash
            printf("\r\n[SHELL] 🎤 麥克風校正已永久寫入 NVS: %.1f\r\n", g_mic_calib_offset);
        }
    }
        // 🔊 2. 產線測試喇叭指令 (讓產線電腦測量推力誤差)
    else if (strcmp(line, "spk_test") == 0)
    {
        printf("\r\n[SHELL] 🔊 產線測試：播放 1000Hz, 數位目標 65 dB (持續 5 秒)...\r\n");
        play_pure_tone(1000.0f, 80.0f, 5000);
    }
        // 🎛️ 3. 產線寫入喇叭校正值 (例如: set_spk -12.5)
    else if (strncmp(line, "set_spk ", 8) == 0)
    {
        float val = 0;
        if (sscanf(line + 8, "%f", &val) == 1) {
            g_spk_calib_offset = val;
            save_calibration_to_flash("spk_calib", g_spk_calib_offset); // 寫入 Flash
            printf("\r\n[SHELL] 🔊 喇叭校正已永久寫入 NVS: %.1f\r\n", g_spk_calib_offset);
        }
    }
	else if (strncmp(line, "set_limit_bigsound ", 10) == 0)
    {
        int val = 0;
        if (sscanf(line + 10, "%d", &val) == 1) {
            // 限制最大不可超過 16-bit 極限 (32767)
            if (val >= 100 && val <= 32767) {
                g_hard_limit = (int16_t)val;
                printf("\r\n[SHELL] 🛡️ 絕對防禦(磚牆限制)已變更為: %d\r\n", g_hard_limit);
            } else {
                printf("\r\n[SHELL] ❌ 錯誤：限制值必須在 100 到 32767 之間！\r\n");
            }
        }
    }
	else if (strcmp(line, "read_limit_bigsound") == 0)
    {
        printf("\r\n[SHELL] 🛡️ 當前絕對防禦限制值 (Hard Limit): %d\r\n", g_hard_limit);
    }
	// ==========================================================
    // 🎛️ 混音台三大推桿 UART 控制指令
    // ==========================================================
    // 1. 設定藍牙總音量 (例: set_master_vol 0.8)
    else if (strncmp(line, "set_master_vol ", 15) == 0) {
        float val = 0;
        if (sscanf(line + 15, "%f", &val) == 1 && val >= 0.0f && val <= 1.0f) {
            extern volatile float g_master_volume;
            g_master_volume = val;
            printf("\r\n[SHELL] 🎚️ 總音量(Master)已強制設為: %.2f\r\n", g_master_volume);
        } else {
            printf("\r\n[SHELL] ❌ 錯誤：總音量範圍必須在 0.0 到 1.0 之間！\r\n");
        }
    }
    // 2. 設定側音/環境音比例 (例: set_sidetone 1.0)
    else if (strncmp(line, "set_sidetone ", 13) == 0) {
        float val = 0;
        if (sscanf(line + 13, "%f", &val) == 1 && val >= 0.0f && val <= 2.0f) {
            extern volatile float g_sidetone_ratio;
            g_sidetone_ratio = val;
            printf("\r\n[SHELL] 🎤 側音比例(Sidetone)已設為: %.2f\r\n", g_sidetone_ratio);
        } else {
            printf("\r\n[SHELL] ❌ 錯誤：側音比例必須在 0.0 到 2.0 之間！\r\n");
        }
    }
    // 3. 設定對方通話比例 (例: set_callvol 0.5)
    else if (strncmp(line, "set_callvol ", 12) == 0) {
        float val = 0;
        if (sscanf(line + 12, "%f", &val) == 1 && val >= 0.0f && val <= 2.0f) {
            extern volatile float g_hfp_rx_ratio;
            g_hfp_rx_ratio = val;
            printf("\r\n[SHELL] 📞 通話比例(HFP RX)已設為: %.2f\r\n", g_hfp_rx_ratio);
        } else {
            printf("\r\n[SHELL] ❌ 錯誤：通話比例必須在 0.0 到 2.0 之間！\r\n");
        }
    }
	
	else if (strcmp(line, "status_hp_vol") == 0) {
        extern volatile float g_master_volume;
        extern volatile float g_sidetone_ratio;
        extern volatile float g_hfp_rx_ratio;
        
        printf("\r\n=== 🎚️ 當前數位混音台狀態 ===\r\n");
        // 貼心地幫你換算成百分比顯示，更直覺！
        printf(" - 總音量 (Master)      : %.2f (%d%%)\r\n", g_master_volume, (int)(g_master_volume * 100));
        printf(" - 側音比例 (Sidetone)  : %.2f (%d%%)\r\n", g_sidetone_ratio, (int)(g_sidetone_ratio * 100));
        printf(" - 通話比例 (HFP RX)    : %.2f (%d%%)\r\n", g_hfp_rx_ratio, (int)(g_hfp_rx_ratio * 100));
        printf("===============================\r\n");
    }
	else if (strcmp(line, "save_all") == 0) {
        save_audio_tuning_to_nvs();
        printf("\r\n[SHELL] 💾 收到網頁儲存請求，調音參數已永久鎖定！\r\n");
    }
	// 🔄 攔截來自網頁或 UART 的恢復預設指令
    else if (strcmp(line, "load_default") == 0) {
        load_audio_tuning_defaults();
        printf("\r\n[SHELL] 🔄 參數已瞬間恢復出廠預設值！\r\n");
    }
	else if (strcmp(line, "iammaster") == 0)
    {
        g_system_role = 0;
        nvs_handle_t my_handle;
        if (nvs_open("storage", NVS_READWRITE, &my_handle) == ESP_OK) {
            nvs_set_i32(my_handle, "sys_role", 0);
            nvs_commit(my_handle);
            nvs_close(my_handle);
        }
        printf("\r\n[SHELL] 👑 系統已永久設定為: MASTER (主機端)！重啟後生效 (套用新藍牙配置)。\r\n");
    }
    else if (strcmp(line, "iamdevice") == 0)
    {
        g_system_role = 1;
        nvs_handle_t my_handle;
        if (nvs_open("storage", NVS_READWRITE, &my_handle) == ESP_OK) {
            nvs_set_i32(my_handle, "sys_role", 1);
            nvs_commit(my_handle);
            nvs_close(my_handle);
        }
        printf("\r\n[SHELL] 📡 系統已永久設定為: DEVICE (發射端)！重啟後生效 (套用新藍牙配置)。\r\n");
    }
	else if (strcmp(line, "whoami") == 0)
    {
        if (g_system_role == 0) {
            printf("\r\n[SHELL] 👑 當前系統角色: MASTER (主機端)\r\n");
        } else if (g_system_role == 1) {
            printf("\r\n[SHELL] 📡 當前系統角色: DEVICE (發射端)\r\n");
        } else {
            printf("\r\n[SHELL] ❓ 未知的系統角色: %d\r\n", g_system_role);
        }
    }
	else if (strncmp(line, "set_bt_name=", 12) == 0)
    {
        char* new_name = line + 12; // 擷取等號後面的字串
        if (strlen(new_name) > 0 && strlen(new_name) < 32) {
            strcpy(g_bt_name, new_name);
            save_bt_name_to_flash("bt_name", g_bt_name);
            esp_bt_gap_set_device_name(g_bt_name); // 即時更新底層名稱
            printf("\r\n[SHELL] 📲 傳統藍牙(BT)名稱已更改並儲存為: %s\r\n", g_bt_name);
        } else {
            printf("\r\n[SHELL] ❌ 錯誤：名稱長度必須在 1~31 個字元之間！\r\n");
        }
    }
    else if (strncmp(line, "set_ble_name=", 13) == 0)
    {
        char* new_name = line + 13; // 擷取等號後面的字串
        if (strlen(new_name) > 0 && strlen(new_name) < 32) {
            strcpy(g_ble_name, new_name);
            save_bt_name_to_flash("ble_name", g_ble_name);
            esp_ble_gap_set_device_name(g_ble_name); // 即時更新底層名稱
            
            // ⭐ BLE 需要更新廣播封包才會在手機上看到新名字
            // (你原本的 adv_data 宣告在迴圈內，我們可以直接強制停止再重啟廣播來套用)
            esp_ble_gap_stop_advertising();
            vTaskDelay(pdMS_TO_TICKS(100));
            esp_ble_gap_start_advertising(&adv_params);
            
            printf("\r\n[SHELL] 📡 低功耗藍牙(BLE)名稱已更改並儲存為: %s\r\n", g_ble_name);
        } else {
            printf("\r\n[SHELL] ❌ 錯誤：名稱長度必須在 1~31 個字元之間！\r\n");
        }
    }
	
	else if (strcmp(line, "read_bt_name") == 0)
    {
        printf("\r\n[SHELL] 📲 當前傳統藍牙 (BT) 名稱: %s\r\n", g_bt_name);
    }
    else if (strcmp(line, "read_ble_name") == 0)
    {
        printf("\r\n[SHELL] 📡 當前低功耗藍牙 (BLE) 名稱: %s\r\n", g_ble_name);
    }
	else if (strcmp(line, "help") == 0 || strcmp(line, "?") == 0)
    {
        printf("\r\n=========================================================\r\n");
        printf("      🎧 ESP32 助聽器 / 動態降噪 終極開發控制台        \r\n");
        printf("=========================================================\r\n\n");

        printf("【1. 系統模式與調音台 (Mixer & Mode)】\r\n");
        printf("  mode=<0~2>         : 切換模式 (0=通透, 1=降噪, 2=語音增強)\r\n");
        printf("  set_master_vol <f> : 設定總音量 (0.0 ~ 1.0)\r\n");
        printf("  set_sidetone <f>   : 設定側音與環境音比例 (0.0 ~ 2.0)\r\n");
        printf("  set_callvol <f>    : 設定對方通話聲音比例 (0.0 ~ 2.0)\r\n");
        printf("  status_hp_vol      : 顯示當前數位混音台音量比例\r\n");
        printf("  save_all           : 將當前參數永久寫入 Flash\r\n");
        printf("  load_default       : 恢復出廠預設值\r\n\r\n");

        printf("【2. ANC 降噪與語音增強 (ANC & VAD)】\r\n");
        printf("  set_delay <n>      : 設定相位延遲點數 (0 ~ 64)\r\n");
        printf("  set_gain <f>       : 設定反相波增益 (0.0 ~ 1.0)\r\n");
        printf("  statusfft          : 顯示當前 ANC 參數狀態\r\n");
        printf("  freq=<hz>          : 設定 FFT 目標鎖定頻率 (0 ~ 8000)\r\n");
        printf("  set_gate <n>       : 設定噪音閘門閥值 (範圍 0 ~ 32767, 預設 800)\r\n");
        printf("  read_gate          : 讀取當前噪音閘門閥值\r\n");
        printf("  set_limit_bigsound : 設定絕對防禦磚牆限制 (100 ~ 32767)\r\n");
        printf("  read_limit_bigsound: 讀取當前磚牆限制值\r\n\r\n");

        printf("【3. EQ 等化器與硬體校正 (EQ & Calibration)】\r\n");
        printf("  eq <b> <g>         : 設定單頻段 EQ 增益 (例: eq 0 5.5)\r\n");
        printf("  show_eq            : 顯示當前 8 段 EQ 設定\r\n");
        printf("  set_mic <f>        : 設定麥克風物理校正值 (dB)\r\n");
        printf("  set_spk <f>        : 設定喇叭物理校正值 (dB)\r\n");
        printf("  spk_test           : 播放產線測試純音 (1000Hz 5秒)\r\n\r\n");

        printf("【4. 硬體周邊與狀態測試 (Hardware Test)】\r\n");
        printf("  PA=1 / PA=0        : 開啟 / 關閉 喇叭功放 (GPIO 21)\r\n");
        printf("  SL1=1/0, SL2=1/0   : 開啟 / 關閉 狀態指示燈\r\n");
        printf("  check_HP           : 偵測耳機孔插入狀態 (GPIO 19)\r\n");
        printf("  mic                : 執行麥克風原始數據採樣測試\r\n");
        printf("  i2sset             : 印出 I2S 底層配置與 DMA 狀態\r\n");
        printf("  changeto16k/44p1k/48k : 強制切換並測試取樣率\r\n\r\n");

        printf("【5. I2C 暫存器操作 (Codec Debug)】\r\n");
        printf("  scan               : 掃描 I2C 總線設備\r\n");
        printf("  init7243 / init8311: 重新初始化 ADC / DAC\r\n");
        printf("  status7243 / 8311  : 印出 ADC/DAC 詳細遙測與時鐘狀態\r\n");
        printf("  r7243e / r8311     : Dump 全部暫存器\r\n");
        printf("  r7243e <hex>       : 讀取單一暫存器 (例: r7243e 01)\r\n");
        printf("  w7243e <r> <v>     : 寫入單一暫存器 (例: w7243e 01 FF)\r\n");
        printf("  (ES8311 寫入格式同上: w8311 <r> <v>)\r\n\r\n");

        printf("  help 或 ?          : 顯示此說明選單\r\n");
        printf("=========================================================\r\n\n");
    }
    else
    {
        ESP_LOGW(TAG, "unknown cmd");
    }
}
// ==========================================
// 1. GAP 事件處理 (負責發射廣播與主動掃描)
// ==========================================
void gap_event_handler(esp_gap_ble_cb_event_t event, esp_ble_gap_cb_param_t *param) {
    //ESP_LOGI("BLE_GAP", "👉 收到 GAP 事件 ID: %d", event);
    if (event != ESP_GAP_BLE_SCAN_RESULT_EVT) {
        ESP_LOGI("BLE_GAP", "👉 收到 GAP 事件 ID: %d", event);
    }
    switch (event) {
        // ------------------------------------------------
        // 📡 Server (發射端) 相關事件
        // ------------------------------------------------
        case ESP_GAP_BLE_ADV_DATA_SET_COMPLETE_EVT:
            ESP_LOGI("BLE_GAP", "✅ 廣播資料設定完成，正式發射廣播！");
            esp_ble_gap_start_advertising(&adv_params);
            break;
            
        case ESP_GAP_BLE_ADV_START_COMPLETE_EVT:
            if (param->adv_start_cmpl.status == ESP_BT_STATUS_SUCCESS) {
                ESP_LOGI("BLE_GAP", "📡 BLE 廣播已成功啟動！(等待連線中)");
            } else {
                ESP_LOGE("BLE_GAP", "❌ 廣播啟動失敗, 錯誤碼: %d", param->adv_start_cmpl.status);
            }
            break;
            
        case ESP_GAP_BLE_UPDATE_CONN_PARAMS_EVT:
        {
            ESP_LOGI("BLE_GAP", "🔄 心跳參數更新: status=%d, int=%d, latency=%d, timeout=%d",
                     param->update_conn_params.status,
                     param->update_conn_params.conn_int,
                     param->update_conn_params.latency,
                     param->update_conn_params.timeout);
            
            if (param->update_conn_params.status != ESP_OK) {
                ESP_LOGE("BLE_GAP", "❌ 心跳參數更新失敗! 這通常是導致斷線的主因");
            }
            break;
        }   

        // ------------------------------------------------
        // 👑 Client (MASTER 主機掃描端) 專屬事件
        // ------------------------------------------------
        case ESP_GAP_BLE_SCAN_PARAM_SET_COMPLETE_EVT:
            // 掃描參數設定完畢，MASTER 正式啟動掃描
            if (g_system_role == 0) {
                esp_ble_gap_start_scanning(0); // 0 = 永不停止掃描
                ESP_LOGI("BLE_GAP", "📡 MASTER 開始雷達掃描 SLAVE...");
            }
            break;
            
        case ESP_GAP_BLE_SCAN_RESULT_EVT: 
        {
            esp_ble_gap_cb_param_t *scan_result = (esp_ble_gap_cb_param_t *)param;
            
            if (scan_result->scan_rst.search_evt == ESP_GAP_SEARCH_INQ_RES_EVT) {
                // 解析掃描到的藍牙名稱
                uint8_t *adv_name = NULL;
                uint8_t adv_name_len = 0;
                adv_name = esp_ble_resolve_adv_data(scan_result->scan_rst.ble_adv,
                                                    ESP_BLE_AD_TYPE_NAME_CMPL, &adv_name_len);
                
                // 動態組合我們要尋找的 SLAVE 目標名稱 (加上 _SEN 標籤)
                char target_name[40];
				snprintf(target_name, sizeof(target_name), "%s_SEN", g_ble_name);

                // 如果名字跟我們預設的 SLAVE 名字一樣，就發起連線！
                if (adv_name != NULL && strncmp((char *)adv_name, target_name, adv_name_len) == 0) {
                    ESP_LOGI("BLE_GAP", "🎯 發現目標 SLAVE (%s)！停止掃描，準備對接...", target_name);
                    
                    // 先停止掃描，避免干擾連線過程
                    esp_ble_gap_stop_scanning();
                    
                    // 發起連線 (注意：gl_gatts_client_if 是我們前面在 GATTC 註冊時存下來的變數)
                    esp_ble_gattc_open(gl_gatts_client_if, scan_result->scan_rst.bda, scan_result->scan_rst.ble_addr_type, true);
                }
            }
            break;
        }

        default:
            break;
    }
}
static bool ble_is_connected = false;
extern volatile float g_env_rms;
extern volatile bool g_vad_active;
extern volatile SceneMode g_current_scene;
void ble_heartbeat_task(void *pvParameters) {
    while (1) {
        if (ble_is_connected && gl_conn_id != 0xFFFF && gl_gatts_if != 0xFF) {
            
            // =========================================================
            // 📡 模式 B: 當我是 SLAVE (Sensor 機) 時，負責發射環境情報
            // (假設 g_system_role == 1 代表 SLAVE)
            // =========================================================
            if (g_system_role == 1) {
                char sensor_data[128];
                
                // 封包格式: "SEN,場景,RMS能量,EQ0,EQ1,EQ2,EQ3,EQ4,EQ5,EQ6,EQ7"
                // 提取 FFT 任務計算出來的動態防護值 (g_auto_offset)
                snprintf(sensor_data, sizeof(sensor_data), 
                         "SEN,%d,%.1f,%.1f,%.1f,%.1f,%.1f,%.1f,%.1f,%.1f,%.1f", 
                         g_current_scene, 
                         g_env_rms, 
                         g_auto_offset[0], g_auto_offset[1], g_auto_offset[2], g_auto_offset[3],
                         g_auto_offset[4], g_auto_offset[5], g_auto_offset[6], g_auto_offset[7]);

                // 透過 BLE 傳送給 MASTER (由於是即時 EQ 控制，傳輸頻率要拉高)
                esp_ble_gatts_send_indicate(gl_gatts_if, gl_conn_id, char_handle, 
                                           strlen(sensor_data), (uint8_t*)sensor_data, false);
                                           
                vTaskDelay(pdMS_TO_TICKS(100)); // SLAVE 每 100ms 更新一次情報給主機
            }
            // =========================================================
            // 👑 模式 A: 當我是 MASTER (主機) 時，原本給網頁看的狀態
            // =========================================================
            else {
                // 🌟 新增判斷：確認手機網頁有連線，才發送狀態
                if (g_web_is_connected && gl_web_conn_id != 0xFFFF) {
                    char status_msg[128];
                    snprintf(status_msg, sizeof(status_msg), "STATUS,%d,%.1f,%d", 
                             g_current_scene, 
                             g_env_rms, 
                             g_vad_active ? 1 : 0);

                    // 🌟 關鍵修改：把發送對象換成 gl_web_conn_id
                    esp_ble_gatts_send_indicate(gl_gatts_if, gl_web_conn_id, char_handle, 
                                               strlen(status_msg), (uint8_t*)status_msg, false);
                }
                                           
                vTaskDelay(pdMS_TO_TICKS(1000)); // 給網頁看的，1秒更新一次即可
            }
        } else {
            // 如果斷線了，稍微睡一下避免空轉
            vTaskDelay(pdMS_TO_TICKS(500)); 
        }
    }
}
// ==========================================
// 2. GATTS 事件處理 (負責設定屬性) - 雙機主從強化版
// ==========================================
void gatts_event_handler(esp_gatts_cb_event_t event,
                         esp_gatt_if_t gatts_if,
                         esp_ble_gatts_cb_param_t *param)
{
    ESP_LOGI("BLE_GATTS", "👉 收到 GATTS 事件 ID: %d", event);
    
    switch (event)
    {
        case ESP_GATTS_REG_EVT:
        {
            ESP_LOGI("BLE_GATTS", "1️⃣ 註冊成功，準備設定廣播資料...");
            
            // ⭐ 雙機架構修改：根據角色動態調整廣播名稱
            char current_adv_name[40];
            if (g_system_role == 1) {
                // 如果是 SLAVE (Sensor 機)，在名字後方加上 "_SEN" 標籤
                // 這樣 MASTER 雷達掃描時，就能精準鎖定它！
                snprintf(current_adv_name, sizeof(current_adv_name), "%s_SEN", g_ble_name);
                ESP_LOGI("BLE_GATTS", "📡 當前為 SLAVE，廣播名稱設定為: %s", current_adv_name);
            } else {
                // 如果是 MASTER，維持原本給手機網頁連線的名字
                strncpy(current_adv_name, g_ble_name, sizeof(current_adv_name));
                ESP_LOGI("BLE_GATTS", "👑 當前為 MASTER，廣播名稱設定為: %s", current_adv_name);
            }
            esp_ble_gap_set_device_name(current_adv_name);

            static uint8_t raw_adv_data_uuid[] = {0xFF, 0x00};
            
            // 🌟 極致瘦身版廣播參數：關閉不必要的資訊，保證不超過 31 Bytes 極限！
            static esp_ble_adv_data_t adv_data = {
                .set_scan_rsp = false,
                .include_name = true,
                .include_txpower = false,
                .min_interval = 0x0020, // 給定標準廣播間隔，避免底層報錯
                .max_interval = 0x0040,
                .appearance = 0,
                .manufacturer_len = 0,
                .p_manufacturer_data = NULL,
                .service_data_len = 0,
                .p_service_data = NULL,
                
                // ❌ 把 UUID 長度設為 0，讓底層略過檢查，100% 避開 258 錯誤！
                .service_uuid_len = 0, 
                .p_service_uuid = NULL,
                
                // 恢復最安全的旗標
                .flag = ESP_BLE_ADV_FLAG_GEN_DISC, 
            };
            
            esp_err_t err = esp_ble_gap_config_adv_data(&adv_data);
            if (err != ESP_OK) {
                ESP_LOGE("BLE_GATTS", "❌ 廣播資料設定失敗: %d", err);
            } else {
                ESP_LOGI("BLE_GATTS", "2️⃣ 廣播資料已送出，等待底層確認...");
            }

            esp_gatt_srvc_id_t service_id = {
                .is_primary = true,
                .id.inst_id = 0x00,
                .id.uuid.len = ESP_UUID_LEN_16,
                .id.uuid.uuid.uuid16 = GATTS_SERVICE_UUID,
            };
            esp_ble_gatts_create_service(gatts_if, &service_id, GATTS_NUM_HANDLE);
            break;
        }
        
        case ESP_GATTS_CREATE_EVT:
            ESP_LOGI("BLE_GATTS", "3️⃣ 服務建立成功，準備啟動服務...");
            service_handle = param->create.service_handle;
            esp_ble_gatts_start_service(service_handle);

            esp_bt_uuid_t char_uuid = {
                .len = ESP_UUID_LEN_16,
                .uuid.uuid16 = GATTS_CHAR_UUID,
            };

            esp_attr_value_t char_val = {
                .attr_max_len = 128,
                .attr_len = 1,
                .attr_value = (uint8_t *)"\0",
            };

            // ⭐ 終極修復：明確宣告「我要手動回覆 (RSP_BY_APP)」
            esp_attr_control_t control = {
                .auto_rsp = ESP_GATT_RSP_BY_APP
            };

            esp_ble_gatts_add_char(service_handle,
                       &char_uuid,
                       ESP_GATT_PERM_READ | ESP_GATT_PERM_WRITE,
                       ESP_GATT_CHAR_PROP_BIT_READ | ESP_GATT_CHAR_PROP_BIT_WRITE | ESP_GATT_CHAR_PROP_BIT_NOTIFY, 
                       &char_val,
                       &control);
            break;

        case ESP_GATTS_ADD_CHAR_EVT:
            char_handle = param->add_char.attr_handle;
            break;

        // =========================================
        // ⭐ 網頁請求讀取資料 (同步 ESP32 內的數值)
        // =========================================
        case ESP_GATTS_READ_EVT:
        {
            ESP_LOGI("BLE_GATTS", "📥 收到網頁同步請求！準備回傳目前基準值 (並認證為手機網頁)...");
            
            // 🌟 新增：記下手機網頁的專屬連線 ID，標記手機已連線
            gl_web_conn_id = param->read.conn_id;
            g_web_is_connected = true;

            esp_gatt_rsp_t rsp;
            memset(&rsp, 0, sizeof(esp_gatt_rsp_t));
            rsp.attr_value.handle = param->read.handle;

            extern volatile float g_master_volume, g_sidetone_ratio, g_hfp_rx_ratio;
            extern volatile float g_user_eq[8]; // ⭐ 傳送基準層給網頁

            char sync_buf[128];
            int len = snprintf(sync_buf, sizeof(sync_buf), 
                               "SYNC,%.2f,%.2f,%.2f,%.1f,%.1f,%.1f,%.1f,%.1f,%.1f,%.1f,%.1f",
                               g_master_volume, g_sidetone_ratio, g_hfp_rx_ratio,
                               g_user_eq[0], g_user_eq[1], g_user_eq[2], g_user_eq[3],
                               g_user_eq[4], g_user_eq[5], g_user_eq[6], g_user_eq[7]);
            rsp.attr_value.len = len;
            memcpy(rsp.attr_value.value, sync_buf, len);
            esp_ble_gatts_send_response(gatts_if, param->read.conn_id, param->read.trans_id, ESP_GATT_OK, &rsp);
            break;
        }

        case ESP_GATTS_CONNECT_EVT:
        {
            ESP_LOGI("BLE_GATTS", "🔗 連線建立，鎖定穩定傳輸間隔...");
            gl_conn_id = param->connect.conn_id;
            gl_gatts_if = gatts_if; 
            ble_is_connected = true;

            // 🌟 終極身分區隔：只讓 MASTER 保持廣播，讓 DEVICE 隱身！
            if (g_system_role == 0) {
                // 我是 MASTER：我必須保持廣播，讓手機網頁可以連進來控制我！
                esp_err_t ret = esp_ble_gap_start_advertising(&adv_params);
                if (ret == ESP_OK) {
                    ESP_LOGI("BLE_GATTS", "👑 MASTER 成功重啟廣播，等待手機連線...");
                } else {
                    ESP_LOGE("BLE_GATTS", "❌ MASTER 重啟廣播失敗！錯誤碼: 0x%X (極可能是 sdkconfig 連線數限制)", ret);
                }
            } else {
                // 我是 DEVICE：我已經被 MASTER 找到，立刻關閉廣播隱身，拒絕手機誤連！
                esp_ble_gap_stop_advertising();
                ESP_LOGI("BLE_GATTS", "📡 DEVICE 任務完成，關閉廣播隱身！");
            }

            esp_ble_conn_update_params_t conn_params = {0};
            memcpy(conn_params.bda, param->connect.remote_bda, sizeof(esp_bd_addr_t));
            
            // ⭐ 設定一個中等偏慢的間隔 (60ms)，這對 DSP 運算最友善
            conn_params.latency = 0;
            conn_params.max_int = 0x60; // 120ms
            conn_params.min_int = 0x40; // 80ms
            conn_params.timeout = 800;  // 8秒超時
            
            esp_ble_gap_update_conn_params(&conn_params);
            break;
        }

        case ESP_GATTS_WRITE_EVT:
            if (!param->write.is_prep) {
                // 🌟 新增：收到寫入指令，同樣認證為手機網頁並記下專屬連線 ID
                gl_web_conn_id = param->write.conn_id;
                g_web_is_connected = true;

                char cmd_buf[128] = {0};
                int len = param->write.len < 127 ? param->write.len : 127;
                memcpy(cmd_buf, param->write.value, len);
                cmd_buf[len] = '\0';
                ESP_LOGI("BLE_CMD", "收到 Web Tuning 指令: %s", cmd_buf); 
                process_cmd(cmd_buf); 
            }
            
            // ⭐ 終極修復：回覆確認 (ACK)
            if (param->write.need_rsp) {
                esp_ble_gatts_send_response(gatts_if, param->write.conn_id, param->write.trans_id, ESP_GATT_OK, NULL);
            }
            break;

        case ESP_GATTS_DISCONNECT_EVT:
        {
            ESP_LOGW("BLE_GATTS", "💔 DISCONNECT reason=0x%02X", param->disconnect.reason);
            
            // 🌟 新增：如果是手機斷線了，清空手機專屬變數
            if (param->disconnect.conn_id == gl_web_conn_id) {
                g_web_is_connected = false;
                gl_web_conn_id = 0xFFFF;
            }

            // (維持您原本的程式碼)
            ble_is_connected = false;
            gl_conn_id = 0xFFFF;
            
            esp_ble_gap_start_advertising(&adv_params);
        }
        break;

        default:
            break;
    }
}
// 統一切換到 16kHz
void set_audio_to_16k(void) {
    g_i2s_is_reconfiguring = true;
    i2s_init_tx(16000);
    i2s_init_rx(16000);
    current_a2dp_sample_rate = 16000;
    vTaskDelay(pdMS_TO_TICKS(100));
    es8311_config_sample(16000); // 關鍵：這是你原本漏掉的！
    update_8band_eq(16000);      // 關鍵：這也要更新！
    i2c_write(0x18, 0x12, 0x00); // DAC ON
    g_i2s_is_reconfiguring = false;
}

// 統一切換回 44.1kHz
void set_audio_to_44p1k(void) {
    g_i2s_is_reconfiguring = true;
    i2s_init_tx(44100);
    i2s_init_rx(44100);
    current_a2dp_sample_rate = 44100;
    vTaskDelay(pdMS_TO_TICKS(100));
    es8311_init();
    es7243e_init();
    es8311_config_sample(44100);
    update_8band_eq(44100);
    i2c_write(0x18, 0x12, 0x00); // DAC ON
    g_i2s_is_reconfiguring = false;
}
void play_bluetooth_connected_sound(void) {
    ESP_LOGI("A2DP", "🎵 播放藍牙連線提示音 (AirPods Style)");

    // 第一聲：800Hz, 70dB, 持續 150 毫秒
    play_pure_tone(800.0f, 65.0f, 200);
    
    // 中間停頓一下
    vTaskDelay(pdMS_TO_TICKS(50));
    
    // 第二聲：高音 1200Hz, 70dB, 持續 200 毫秒
    play_pure_tone(1200.0f, 65.0f, 300);

    // 完成！不用切換 sample rate，不用霸佔 I2S，完美融入背景音！
}
void play_bluetooth_disconnected_sound(void) {
    ESP_LOGW("BT", "🎵 播放藍牙【斷線】提示音");

    // 斷線音效：降調 (高音 -> 低音)
    play_pure_tone(880.0f, 65.0f, 200);  // 第一聲：高音
    vTaskDelay(pdMS_TO_TICKS(50));
    play_pure_tone(440.0f, 65.0f, 300);  // 第二聲：沉穩低音結尾
}
void a2dp_cb(esp_a2d_cb_event_t event, esp_a2d_cb_param_t *param)
{
    switch (event)
    {
        case ESP_A2D_CONNECTION_STATE_EVT:
            if (param->conn_stat.state == ESP_A2D_CONNECTION_STATE_CONNECTED) {
                ESP_LOGI("A2DP", "✅ 手機藍牙音樂通道已連線");
				ESP_LOGI("A2DP", "i2s 目前狀態");
				print_i2s_status_reading();
				
				g_play_bt_conn_sound = true;
            } else if (param->conn_stat.state == ESP_A2D_CONNECTION_STATE_DISCONNECTED) {
                ESP_LOGI("A2DP", "❌ 手機藍牙音樂通道已斷開");
				g_play_bt_conn_sound = false;
            }
            break;

        case ESP_A2D_AUDIO_STATE_EVT:
            // 這是正確檢查 A2DP 狀態的方法
            if (param->audio_stat.state == ESP_A2D_AUDIO_STATE_STARTED) {
                ESP_LOGI("A2DP", "▶️ 音樂開始播放！");
                if (g_current_audio_state != AUDIO_STATE_HFP_16K) {
                    g_current_audio_state = AUDIO_STATE_A2DP_48K; 
                }
            } else if (param->audio_stat.state == ESP_A2D_AUDIO_STATE_STOPPED) {
                ESP_LOGI("A2DP", "⏸️ 音樂暫停！");
                if (g_current_audio_state == AUDIO_STATE_A2DP_48K) {
                    g_current_audio_state = AUDIO_STATE_IDLE;
                }
            }
            break;

        default:
            break;
    }
}
#define MIX_BUFFER_SIZE 4096
int16_t mixed_audio_buffer[MIX_BUFFER_SIZE / 2];
void audio_data_cb(const uint8_t *music_data, uint32_t music_len) 
{
    if (music_ringbuf != NULL) {
        xRingbufferSend(music_ringbuf, (void *)music_data, music_len, pdMS_TO_TICKS(10));
    }
}
void a2dp_init(void)
{
    esp_a2d_register_callback(a2dp_cb);
    esp_a2d_sink_register_data_callback(audio_data_cb);

    esp_a2d_sink_init();
}
int16_t clamp(int32_t val) {
    if (val > 32767) return 32767;
    if (val < -32768) return -32768;
    return (int16_t)val;
}

void mixer_task(void *arg)
{
	int64_t start_time = 0;
	int64_t end_time = 0;

	
   
    ESP_LOGI("MIXER", "🚀 Core 1 極速降噪混音大腦已啟動 (終極抗外星人與直流版)！");

    extern volatile uint32_t current_a2dp_sample_rate; // 引入我們設定的頻率變數

    const size_t block_bytes = 512;
    const int num_samples = block_bytes / 2; // 256 個樣本 (128 L + 128 R)
    
    static int16_t mic_history_L[256] = {0};
    int history_idx = 0;

    int16_t *out_buffer = (int16_t *)malloc(block_bytes);
    if (out_buffer == NULL) { vTaskDelete(NULL); }
    
    // 統一用這個 Buffer 來裝處理好的 HFP 資料 (不論是直通還是升頻，最後都會轉成立體聲對齊 out_buffer)
    int16_t hfp_processed_buf[256] = {0}; 
    
    // ⭐ 新增：HFP 專屬彈性蓄水池 (最大容納 2048 Bytes，對抗藍牙不穩定封包)
    static uint8_t hfp_accum_buf[2048] = {0};
    static size_t hfp_accum_bytes = 0;
    
    
    size_t mic_bytes = 0, music_bytes = 0, hfp_bytes = 0;
    float mic_envelope = 0.0f;
    
    // ⭐ 直流偏移追蹤器
    static float dc_offset_L = 0.0f; 

    while (1)
    {
		// 🌟 新增這行：每次進迴圈前，先把 HFP 陣列洗乾淨！
        memset(hfp_processed_buf, 0, sizeof(hfp_processed_buf));
		//end_time = esp_timer_get_time();
        static bool was_in_test_mode = false;
        // --- 以下維持原本的邏輯 ---
        if (g_i2s_is_reconfiguring) {
            hfp_accum_bytes = 0; // 清空接收蓄水池
            
            // 🌟 新增防護：清空發送郵筒 (Flush)
            // 防止上一通電話的殘留聲音把郵筒卡死
            if (hfp_tx_ringbuf != NULL) {
                size_t dummy_size;
                void *dummy_data;
                while ((dummy_data = xRingbufferReceive(hfp_tx_ringbuf, &dummy_size, 0)) != NULL) {
                    vRingbufferReturnItem(hfp_tx_ringbuf, dummy_data);
                }
            }
            
            vTaskDelay(pdMS_TO_TICKS(10));
            continue;
        }

		
        // 🎤 改成用 10ms 的容忍等待，如果沒收到資料，就視為靜音
        // 🚀 關鍵修復 1：把 pdMS_TO_TICKS(10) 改成 0！絕對不要在這邊等！
		int16_t* mic_data = NULL;
        
        if (g_system_role == 0) {
            // ==================================================
            // 👑 MASTER 模式
            // ==================================================
            if (g_is_device_connected) {
                // 正常連線：關閉本機麥克風，純接收 Device 傳來的藍牙音訊
                mic_bytes = 0; 
            } else {
                // 🚨 備援模式：Device 斷線，強制切回本機麥克風！
                mic_data = (int16_t*)xRingbufferReceiveUpTo(mic_ringbuf, &mic_bytes, pdMS_TO_TICKS(15), block_bytes);
            }
        } else {
            // ==================================================
            // 📡 DEVICE 模式
            // ==================================================
            // 永遠只讀取本機麥克風，準備透過藍牙發射
            mic_data = (int16_t*)xRingbufferReceiveUpTo(mic_ringbuf, &mic_bytes, pdMS_TO_TICKS(15), block_bytes);
        }

        int16_t* music_data = (int16_t*)xRingbufferReceiveUpTo(music_ringbuf, &music_bytes, 0, block_bytes);

        // ==========================================================
        // 📞 HFP 資料處理：終極預先緩衝 (Pre-buffering) 抗斷流機制
        // ==========================================================
        if (current_a2dp_sample_rate == 16000) {
            size_t chunk_size = 0;
            void *chunk = NULL;
            
            // 預先緩衝狀態旗標 (打電話剛接通時，先強制蓄水)
            static bool hfp_is_buffering = true; 
            
            // 1. 【瘋狂抽水】只要 RingBuffer 裡有資料，就全部倒進蓄水池
            while ((chunk = xRingbufferReceiveUpTo(hfp_ringbuf, &chunk_size, 0, 1024)) != NULL) {
                if (hfp_accum_bytes + chunk_size > sizeof(hfp_accum_buf)) {
                    hfp_accum_bytes = 0; // 防呆洩洪
                }
                memcpy(hfp_accum_buf + hfp_accum_bytes, chunk, chunk_size);
                hfp_accum_bytes += chunk_size;
                vRingbufferReturnItem(hfp_ringbuf, chunk);
            }

            // 2. 【預防斷流：檢查是否需要先蓄滿水】
            if (hfp_is_buffering) {
                if (hfp_accum_bytes >= 960) { // 強制等存滿 4 包 (4 * 240 = 960 Bytes)
                    ESP_LOGW("MIXER", "✅ 蓄水達標 (960 Bytes)，開始穩定播放！");
                    hfp_is_buffering = false; // 水夠了，解除緩衝狀態
                }
            }

            // 3. 【穩定播放期】(水夠了才准播)
            if (!hfp_is_buffering) {
                if (hfp_accum_bytes >= 256) {
                    
                    int16_t *hfp_mono_in = (int16_t *)hfp_accum_buf;

                    // 完美 1:1 複製給左右耳
                    for (int i = 0; i < 128; i++) {
                        int16_t pure_mono = hfp_mono_in[i]; 
                        
                        hfp_processed_buf[i * 2]     = pure_mono; // 左耳
                        hfp_processed_buf[i * 2 + 1] = pure_mono; // 右耳
                    }

                    // 挪動剩餘的水
                    hfp_accum_bytes -= 256;
                    if (hfp_accum_bytes > 0) {
                        memmove(hfp_accum_buf, hfp_accum_buf + 256, hfp_accum_bytes);
                    }
                } else {
                    // 萬一遇到網路大卡頓，水真的被抽乾了
                    ESP_LOGW("MIXER", "⚠️ 藍牙語音斷流！重新啟動蓄水...");
                    hfp_is_buffering = true; // 回到緩衝狀態，重新等 960 Bytes
                }
            }
        }
        else {
            // 【48kHz / 44.1kHz 模式】維持不變
            int16_t *hfp_data = (int16_t *)xRingbufferReceiveUpTo(hfp_ringbuf, &hfp_bytes, 0, 170);
            if (hfp_data != NULL) {
                upsample_16k_to_48k_fast(hfp_data, hfp_processed_buf, hfp_bytes / 2);
                vRingbufferReturnItem(hfp_ringbuf, (void *)hfp_data);
            }
        }
		int16_t hfp_tx_accum_buf[128] = {0};
        // ==========================================================
        // 🎛️ 主混音邏輯
        // ==========================================================
        if ((mic_data != NULL && mic_bytes == block_bytes) || (music_data != NULL && music_bytes == block_bytes))
        {

			extern volatile float g_master_volume;
            extern volatile float g_sidetone_ratio;
            extern volatile float g_hfp_rx_ratio;
            
            float current_master = g_master_volume;
            float current_sidetone = g_sidetone_ratio;
            float current_hfp = g_hfp_rx_ratio;
			
			// ==========================================================
            // 🛡️ 影子替身換班區 (Double Buffering) - 解決一格一格的破音！
            // ==========================================================
            // 1. 如果情報局 (Core 0) 已經把新的 EQ 算好了，我們就在這裡瞬間切換！
            if (g_eq_update_pending) {
                for (int b = 0; b < 8; b++) {
                    g_eq_coeffs[b] = g_eq_coeffs_shadow[b];
                }
                g_eq_update_pending = false; // 放下旗子
            }

            // 2. 如果情報局 (Core 0) 的狙擊槍 (Notch) 也鎖定新目標了，同步切換！
            if (g_notch_update_pending) {
                g_notch_coeffs = g_notch_coeffs_shadow;
                g_notch_update_pending = false; // 放下旗子
            }
            // ==========================================================
			
			// 🌟 新增：準備計算這 10ms 區塊的總能量
        float block_energy = 0.0f;

        for (int i = 0; i < num_samples; i += 2)
        {
            // ==========================================================
            // 🛡️ 1. 安全抓取資料防護升級
            // ==========================================================
            int16_t raw_mic = (mic_data != NULL && (i * 2) < mic_bytes) ? mic_data[i] : 0;
            int16_t music_L = (music_data != NULL && (i * 2) < music_bytes) ? music_data[i] : 0;
            int16_t music_R = (music_data != NULL && ((i + 1) * 2) < music_bytes) ? music_data[i + 1] : 0;

            // 🛡️ 2. DC Blocker 
            dc_offset_L = dc_offset_L * 0.995f + raw_mic * 0.005f; 
            int16_t clean_mic = raw_mic - (int16_t)dc_offset_L; 

            // 🌟 能量與 VAD 提取
            block_energy += (float)clean_mic * (float)clean_mic;
            
            float current_val = (float)abs(clean_mic);
            mic_envelope = (current_val > mic_envelope) ? 
                           (mic_envelope * 0.1f + current_val * 0.9f) : 
                           (mic_envelope * 0.999f + current_val * 0.001f);
                           
            if (!g_vad_active && mic_envelope > g_noise_gate_threshold) g_vad_active = true;
            else if (g_vad_active && mic_envelope < (g_noise_gate_threshold * 0.5f)) g_vad_active = false;
            
            // 🛡️ 2.5 全域絕對防禦
            int16_t current_limit = g_hard_limit;
            if (clean_mic > current_limit) clean_mic = current_limit;
            else if (clean_mic < -current_limit) clean_mic = -current_limit;

            // ==========================================================
            // 🎤 3. 麥克風核心 DSP
            // ==========================================================
            float current_sample = (float)clean_mic;
            
            if (g_target_noise_freq > 100.0f) {
                static float last_notch_freq = 0.0f;
                if (fabsf(g_target_noise_freq - last_notch_freq) > 0.1f) {
                    calculate_notch_filter(g_target_noise_freq, (float)current_a2dp_sample_rate, 10.0f, &g_notch_coeffs);
                    last_notch_freq = g_target_noise_freq;
                }
                current_sample = process_biquad(current_sample, &g_notch_coeffs, &g_notch_state);
            }
            for (int b = 0; b < 8; b++) {
                current_sample = process_biquad(current_sample, &g_eq_coeffs[b], &g_eq_states[b]);
            }
            
            int16_t eq_mic = (int16_t)current_sample; 

            // ====================================================
            // 🌟 修復 1：場景切換的「平滑漸變增益 (Smooth Cross-fade)」
            // ====================================================
            static float current_scene_gain = 1.0f; // 記住當前的真實倍數
            float target_scene_gain = 1.0f;         // 大腦期望的倍數

            // 決定目標倍數
            if (g_current_scene == SCENE_NOISY_NO_VOICE) {
                target_scene_gain = 0.5f; // 深度降噪，目標壓到 50%
            } else {
                target_scene_gain = 1.0f; // 其他模式，目標維持 100%
            }

            // 執行平滑追蹤 (這就是消除「波」一聲爆音的魔法！)
            current_scene_gain = (current_scene_gain * 0.999f) + (target_scene_gain * 0.001f);
            
            // 最終套用平滑增益
            eq_mic = (int16_t)(eq_mic * current_scene_gain);

            // ==========================================================
            // 🎧 4. 決定輸出的側音/環境音 (根據當前模式)
            // ==========================================================
            int32_t processed_mic = 0;
            switch (g_audio_mode) {
                case 0: 
                    processed_mic = eq_mic; 
                    break;
                case 1: 
                    mic_history_L[history_idx] = clean_mic; 
                    int target_idx = (history_idx - g_phase_delay_samples + 256) % 256;
                    int16_t delayed_mic = mic_history_L[target_idx];
                    history_idx = (history_idx + 1) % 256;
                    processed_mic = (int32_t)(delayed_mic * -1.0f * g_anc_gain);
                    break;
                case 2: 
                    // 🧠 語音增強模式 (噪音閘門 + AGC 智能自動增益)
                    {
                        static bool is_gate_open = false;
                        float gate_open_threshold = g_noise_gate_threshold;
                        float gate_close_threshold = g_noise_gate_threshold * 0.5f;
                        
                        if (!is_gate_open && mic_envelope > gate_open_threshold) is_gate_open = true;
                        else if (is_gate_open && mic_envelope < gate_close_threshold) is_gate_open = false;
                        
                        static float current_agc_gain = 1.0f;
                        extern volatile float g_agc_target_level;
                        extern volatile float g_agc_max_gain;
                        
                        float agc_target_level = g_agc_target_level; 
                        float agc_max_gain = g_agc_max_gain;        

                        if (is_gate_open) {
                            float ideal_gain = 1.0f;
                            if (mic_envelope > 10.0f) { 
                                ideal_gain = agc_target_level / mic_envelope;
                            }
                            if (ideal_gain > agc_max_gain) ideal_gain = agc_max_gain;
                            if (ideal_gain < 1.0f) ideal_gain = 1.0f; 

                            current_agc_gain = current_agc_gain * 0.99f + ideal_gain * 0.01f;
                            processed_mic = (int32_t)(eq_mic * current_agc_gain);
                        } else {
                            current_agc_gain = current_agc_gain * 0.99f + 1.0f * 0.01f;
                            processed_mic = 0;
                        }
                    }
                    break;
            }

            // ==========================================================
            // 📞 5. 發送給對方的手機收音 (TX)
            // ==========================================================
            if (current_a2dp_sample_rate == 16000 || current_a2dp_sample_rate == 8000) {
                int32_t tx_mic = (int32_t)(clean_mic * 1.5f); 
                if (tx_mic > 32767) tx_mic = 32767;
                else if (tx_mic < -32768) tx_mic = -32768;
                hfp_tx_accum_buf[i / 2] = (int16_t)tx_mic;  
            }

            // ==========================================================
            // 🚀 6. 單聲道優化版混音公式
            // ==========================================================
            int32_t mono_music = (music_L + music_R) / 2;
            float f_music = (float)mono_music;

            for (int b = 0; b < 8; b++) {
                f_music = process_biquad(f_music, &g_eq_coeffs[b], &g_eq_states_music[b]);
            }
            mono_music = (int32_t)f_music;

            int32_t final_mic = (int32_t)(processed_mic * current_sidetone);
            int32_t final_hfp = (int32_t)(hfp_processed_buf[i] * current_hfp);
            int32_t mixed_mono = (int32_t)((mono_music + final_hfp) * current_master) + final_mic;

            int32_t final_output_limit = g_hard_limit;
            if (mixed_mono > final_output_limit) mixed_mono = final_output_limit;
            else if (mixed_mono < -final_output_limit) mixed_mono = -final_output_limit;

            out_buffer[i]     = clamp(mixed_mono);
            out_buffer[i + 1] = clamp(mixed_mono);
        } // <--- for 迴圈結束

        // 🌟 新增 4：迴圈結束，結算這 10ms 的平均能量給大腦
        float block_rms = sqrtf(block_energy / (num_samples / 2.0f));
        g_env_rms = g_env_rms * 0.9f + block_rms * 0.1f; // 平滑過渡防突波
			
            // ==========================================================
            // 🌟 關鍵修復 2：把發送給手機的程式碼，搬進這個 if 裡面！
            // ==========================================================
            
            // 🛑【Error 終結者】：不要只看頻率，必須確保大腦判定「通話真正連線中」才搖鈴鐺！
            if ((g_current_audio_state == AUDIO_STATE_HFP_16K) && 
				(current_a2dp_sample_rate == 16000 || current_a2dp_sample_rate == 8000) && 
				hfp_tx_ringbuf != NULL) {
                
                // 🚀 自動洩洪 (Leaky Bucket) 機制
                BaseType_t res;
                while ((res = xRingbufferSend(hfp_tx_ringbuf, hfp_tx_accum_buf, sizeof(hfp_tx_accum_buf), 0)) != pdTRUE) {
                    size_t dummy_size = 0;
                    void *dummy_data = xRingbufferReceiveUpTo(hfp_tx_ringbuf, &dummy_size, 0, sizeof(hfp_tx_accum_buf));
                    if (dummy_data != NULL) {
                        vRingbufferReturnItem(hfp_tx_ringbuf, dummy_data);
                    } else {
                        break; 
                    }
                }

                // ⭐⭐⭐ 搖鈴鐺！
                esp_hf_client_outgoing_data_ready();

                // 🕵️‍♂️ 降速除錯探針
                static int tx_log_cnt = 0;
                if (++tx_log_cnt % 100 == 0) {
                    ESP_LOGI("HFP_TX", "✅ 放進郵筒成功! 頻率: %lu Hz, 波形數據: [%d, %d, %d, %d]", 
                             current_a2dp_sample_rate, 
                             hfp_tx_accum_buf[0], hfp_tx_accum_buf[1], 
                             hfp_tx_accum_buf[2], hfp_tx_accum_buf[3]);
                }
            }
			
        } // <=== 🌟 這裡才是 if ((mic_data != NULL ...)) 混音大腦的結束大括號！
        else 
        {
            memset(out_buffer, 0, block_bytes);
        }
		// ==========================================================
        // 🧹 關鍵修復 2：歸還記憶體【必須移到 if/else 的外面】！
        // 這樣就算收到不完整的碎片，用完也會乖乖還給郵筒，麥克風絕對不會再卡死！
        // ==========================================================
        if (mic_data != NULL) {
            vRingbufferReturnItem(mic_ringbuf, (void *)mic_data);
            mic_data = NULL; 
        }
        if (music_data != NULL) {
            vRingbufferReturnItem(music_ringbuf, (void *)music_data);
            music_data = NULL; 
        }
        // ==========================================================
        // 🚨 終極匯出區：這段【必須】放在 if-else 判斷式的外面！
        // 確保不管前面發生什麼事，每一回合都一定要把資料塞給硬體！
        // ==========================================================
        // 2. 餵資料給喇叭 (I2S DMA)
        if (!g_i2s_is_reconfiguring && tx_handle != NULL) {
            
            // 🔇 如果我是 SLAVE (Sensor 機)，強制把要送給喇叭的聲音清零！
            if (g_system_role == 1) {
                memset(out_buffer, 0, block_bytes);
            }

            esp_err_t err = i2s_channel_write(tx_handle, out_buffer, block_bytes, NULL, portMAX_DELAY);
        } else {
            vTaskDelay(pdMS_TO_TICKS(10));
        }
        
    } 
} 





// --- 3. A2DP 回調 ---
void app_a2d_callback(esp_a2d_cb_event_t event, esp_a2d_cb_param_t *param) {
    switch (event) {
        case ESP_A2D_AUDIO_CFG_EVT:
            if (param->audio_cfg.mcc.type == ESP_A2D_MCT_SBC) {
                uint8_t sbc_header = param->audio_cfg.mcc.cie.sbc[0];
                uint32_t rate = 44100;

                // 判斷 SBC 的採樣率位元
                if (sbc_header & (1 << 6)) {
                    rate = 44100;
                } else if (sbc_header & (1 << 5)) {
                    rate = 48000;
                } else if (sbc_header & (1 << 7)) {
                    rate = 16000;
                } else if (sbc_header & (1 << 4)) {
                    rate = 32000;
                }
                
                current_a2dp_sample_rate = rate;
				update_8band_eq(rate);
                // 1. 先停掉 TX 和 RX 通道
				i2s_channel_disable(tx_handle); 
				i2s_channel_disable(rx_handle);

				
                // 1. 先更新系統內部的時鐘變數或 I2S 驅動
                //update_audio_system_clock(rate);
				i2s_init_tx(rate);
				i2s_init_rx(rate);
				// 3. 改完後，重新啟動通道
				//i2s_channel_enable(tx_handle);
				//i2s_channel_enable(rx_handle);
                // 2. 緊接著呼叫 ES8311 的配置函數，同步 Codec 的硬體時鐘
                ESP_LOGI("A2DP_CB", "A2DP 設定變更，同步 ES8311 採樣率至: %lu Hz", (unsigned long)rate);
                es8311_config_sample(rate);
				i2c_write(0x18,0x12,0x00);//////DAC ON
				print_i2s_status_reading();
				es8311_i2s_config_debug();
            }
            break;
        default:
            break;
    }
}
void es8311_i2s_config_debug(void)
{
   ESP_LOGI(TAG, "========= ES8311 R&D TELEMETRY EXTREME EDITION =========");

    // --- 1. 讀取所有關鍵暫存器 ---
    uint8_t reg00 = es8311_read_reg(0x00); // 系統狀態與主從模式
    uint8_t reg01 = es8311_read_reg(0x01); // 時鐘管理 (MCLK來源)
    uint8_t reg09 = es8311_read_reg(0x09); // DAC I2S 配置
    uint8_t reg0A = es8311_read_reg(0x0A); // ADC I2S 配置
    uint8_t reg0D = es8311_read_reg(0x0D); // 類比總電源與 VREF (⭐極重要)
    uint8_t reg12 = es8311_read_reg(0x12); // DAC 系統電源
    uint8_t reg14 = es8311_read_reg(0x14); // MIC 偏壓與選擇
    uint8_t reg15 = es8311_read_reg(0x15); // ADC HPF (高通濾波)
    uint8_t reg16 = es8311_read_reg(0x16); // MIC PGA 增益
    uint8_t reg17 = es8311_read_reg(0x17); // ADC 類比電源
    uint8_t reg18 = es8311_read_reg(0x18); // ALC 控制
    uint8_t reg31 = es8311_read_reg(0x31); // DAC 靜音與相位
    uint8_t reg32 = es8311_read_reg(0x32); // DAC 數位音量
    uint8_t reg37 = es8311_read_reg(0x37); // DAC 類比驅動器
    uint8_t reg44 = es8311_read_reg(0x44); // 內部路由與 Loopback
    uint8_t regfc = es8311_read_reg(0xFC); // PLL 狀態監控

    // --- [輔助解析巨集] ---
    #define GET_FMT(r)  (((r)&0x03)==0?"I2S(Philips)":((r)&0x03)==1?"Left-J":((r)&0x03)==2?"DSP/PCM":"RSV")
    #define GET_WL(r)   ((((r)>>2)&0x07)==0?"24-bit":(((r)>>2)&0x07)==1?"20-bit":(((r)>>2)&0x07)==2?"18-bit":(((r)>>2)&0x07)==3?"16-bit":(((r)>>2)&0x07)==4?"32-bit":"ERR")
    #define GET_LRP(r)  (((r)&0x20)?"Inverted":"Normal")
    #define GET_CH(r)   (((r)&0x80)?"Right":"Left")

    // --- [Block A: 系統電源與核心 (The Master Switches)] ---
    ESP_LOGI(TAG, "[A. System Core & Master Power]");
    ESP_LOGI(TAG, " - State Machine  : %s (Reg 0x00=0x%02X)", (reg00 & 0x80) ? "RUNNING" : "STANDBY", reg00);
    ESP_LOGI(TAG, " - Analog Master  : %s (Reg 0x0D=0x%02X)", (reg0D & 0x80) ? "POWER DOWN (Dead)" : "POWERED UP (OK)", reg0D);
    ESP_LOGI(TAG, " - VREF State     : %s (Reg 0x0D Bit2)", (reg0D & 0x04) ? "OFF" : "ON"); 
    ESP_LOGI(TAG, " - DAC Sys Power  : %s (Reg 0x12=0x%02X)", (reg12 == 0x00) ? "ON" : "OFF/SUSPEND", reg12);

    // --- [Block B: I2S 時鐘與通訊介面] ---
    ESP_LOGI(TAG, "[B. Clock & I2S Interface]");
    ESP_LOGI(TAG, " - I2S Role       : %s (Reg 0x00 Bit6)", (reg00 & 0x40) ? "MASTER (Codec generates Clock)" : "SLAVE (ESP32 gives Clock)");
    ESP_LOGI(TAG, " - MCLK Source    : %s (Reg 0x01 Bit7)", (reg01 & 0x80) ? "Recovered from BCLK (Internal)" : "External MCLK Pin");
    ESP_LOGI(TAG, " - MCLK PLL Lock  : %s (Reg 0xFC=0x%02X)", (regfc >= 0x03) ? "LOCKED" : "UNLOCKED/ERR", regfc);
    ESP_LOGI(TAG, " - ADC (RX) Format: %s, %s | CH: %s | Phase LRP: %s", GET_WL(reg0A), GET_FMT(reg0A), GET_CH(reg0A), GET_LRP(reg0A));
    ESP_LOGI(TAG, " - DAC (TX) Format: %s, %s | CH: %s | Phase LRP: %s", GET_WL(reg09), GET_FMT(reg09), GET_CH(reg09), GET_LRP(reg09));

    // --- [Block C: ADC 錄音硬體路徑 (Input)] ---
    ESP_LOGI(TAG, "[C. ADC / Microphone Path]");
    ESP_LOGI(TAG, " - MIC Bias (MICP): %s (Reg 0x14=0x%02X)", (reg14 & 0x08) ? "OFF" : "ON", reg14);
    ESP_LOGI(TAG, " - ADC Analog Pwr : %s (Reg 0x17=0x%02X)", (reg17 == 0xBF) ? "ON" : "OFF", reg17);
    ESP_LOGI(TAG, " - MIC PGA Gain   : +%d dB (Reg 0x16=0x%02X)", (reg16 & 0x3F), reg16);
    ESP_LOGI(TAG, " - HPF Filter     : %s (Reg 0x15=0x%02X)", (reg15 & 0x20) ? "BYPASS" : "ENABLED", reg15);
    ESP_LOGI(TAG, " - ALC (Auto Gain): %s (Reg 0x18=0x%02X)", (reg18 & 0x80) ? "ENABLED" : "DISABLED", reg18);

    // --- [Block D: DAC 放音硬體路徑 (Output)] ---
    ESP_LOGI(TAG, "[D. DAC / Speaker Path]");
    ESP_LOGI(TAG, " - Analog Driver  : %s (Reg 0x37=0x%02X)", (reg37 & 0x08) ? "ON (Physical Output Enable)" : "OFF", reg37);
    float vol_db = (reg32 * 0.5) - 95.5; 
    ESP_LOGI(TAG, " - Digital Volume : %.1f dB (%s)", vol_db, (reg31 & 0x20) ? "MUTED (Soft)" : "UNMUTED");
    ESP_LOGI(TAG, " - H/W Loopback   : %s (Reg 0x44=0x%02X)", (reg44 & 0x80) ? "ENABLED (ADC->DAC Direct)" : "DISABLED", reg44);

    ESP_LOGI(TAG, "========================================================");
}
// ==========================================
// AVRCP 目標設備 (TG) 回調：專門負責接收手機的音量指令
// ==========================================
void bt_app_avrc_tg_cb(esp_avrc_tg_cb_event_t event, esp_avrc_tg_cb_param_t *param)
{
    switch (event) {
        case ESP_AVRC_TG_SET_ABSOLUTE_VOLUME_CMD_EVT: {
            uint8_t volume = param->set_abs_vol.volume;
            
            extern volatile float g_master_volume; 
            
            // 🌟 關鍵修改 1：改成平方曲線！
            float linear_ratio = (float)volume / 127.0f;
            g_master_volume = linear_ratio * linear_ratio; // 自己乘自己 (平方)
            
            ESP_LOGI("AVRCP_TG", "📱 手機傳來絕對音量: %d, 轉換總音量增益: %.4f", volume, g_master_volume);
            break;
        }

        case ESP_AVRC_TG_REGISTER_NOTIFICATION_EVT: {
            if (param->reg_ntf.event_id == ESP_AVRC_RN_VOLUME_CHANGE) {
                esp_avrc_rn_param_t rn_param;
                extern volatile float g_master_volume;
                
                // 🌟 關鍵修改 2：因為前面平方了，回傳給手機要「開根號 (sqrtf)」還原！
                int calculated_vol = (int)(sqrtf(g_master_volume) * 127.0f);
                if (calculated_vol > 127) calculated_vol = 127;
                if (calculated_vol < 0) calculated_vol = 0;
                
                rn_param.volume = (uint8_t)calculated_vol;
                esp_avrc_tg_send_rn_rsp(ESP_AVRC_RN_VOLUME_CHANGE, ESP_AVRC_RN_RSP_INTERIM, &rn_param);
            }
            break;
        }
            
        default:
            break;
    }
}

// ==========================================
// AVRCP 控制器 (CT) 回調：負責處理播放/暫停等狀態
// ==========================================
void bt_app_avrc_ct_cb(esp_avrc_ct_cb_event_t event, esp_avrc_ct_cb_param_t *param)
{
    switch (event) {
        case ESP_AVRC_CT_CONNECTION_STATE_EVT:
            if (param->conn_stat.connected) {
                ESP_LOGI("AVRCP_CT", "✅ AVRCP 控制通道已連線");
            }
            break;
            
        case ESP_AVRC_CT_CHANGE_NOTIFY_EVT:
            ESP_LOGW("AVRCP_CT", "收到手機 CT 通知！ Event ID: %d", param->change_ntf.event_id);
            break;
            
        default:
            break;
    }
}
volatile bool g_is_slave_online = false;

void process_slave_sensor_data(const uint8_t *payload, uint16_t len) {
    char buf[128] = {0};
    memcpy(buf, payload, len < 127 ? len : 127);
    
    // 確保這是一包 Sensor 資料
    if (strncmp(buf, "SEN,", 4) == 0) {
        int scene = 0;
        float rms = 0;
        float eq[8] = {0};
        
        // 解析 CSV 格式字串 (對應 SLAVE 傳出的 10 個變數)
        if (sscanf(buf, "SEN,%d,%f,%f,%f,%f,%f,%f,%f,%f,%f",
                   &scene, &rms,
                   &eq[0], &eq[1], &eq[2], &eq[3],
                   &eq[4], &eq[5], &eq[6], &eq[7]) >= 10) {
            
            // 1. 同步 SLAVE 的場景判斷到 MASTER
            g_current_scene = (SceneMode)scene;
            g_env_rms = rms;
            
            // 2. 寫入 8 段動態防護 EQ
            for(int i = 0; i < 8; i++) {
                g_auto_offset[i] = eq[i];
                // 重新結算最終輸出目標 = 使用者設定 + SLAVE 動態防護
                g_target_gains_db[i] = g_user_eq[i] + g_auto_offset[i];
            }
            
            // 3. 標記 SLAVE 穩定連線中
            g_is_slave_online = true;
            
            // 4. 觸發 DSP 更新 (交給 Core 0 去算，不卡 BLE)
            update_8band_eq(current_a2dp_sample_rate);
        }
    }
}
// ==========================================
// 👑 MASTER 專用：GATT Client 事件處理
// ==========================================
// 用來暫存 SLAVE 的 MAC 位置
static esp_bd_addr_t gl_remote_bda;

void gattc_event_handler(esp_gattc_cb_event_t event, esp_gatt_if_t gattc_if, esp_ble_gattc_cb_param_t *param) {
    switch (event) {
        case ESP_GATTC_REG_EVT:
            gl_gatts_client_if = gattc_if;
            if (g_system_role == 0) {
                esp_ble_scan_params_t ble_scan_params = {
                    .scan_type              = BLE_SCAN_TYPE_ACTIVE,
                    .own_addr_type          = BLE_ADDR_TYPE_PUBLIC,
                    .scan_filter_policy     = BLE_SCAN_FILTER_ALLOW_ALL,
                    .scan_interval          = 0x50,
                    .scan_window            = 0x30,
                    .scan_duplicate         = BLE_SCAN_DUPLICATE_DISABLE
                };
                esp_ble_gap_set_scan_params(&ble_scan_params);
            }
            break;
            
        case ESP_GATTC_CONNECT_EVT:
            ESP_LOGI("BLE_GATTC", "🔗 MASTER 成功連上 SLAVE！準備同步資料...");
            g_is_slave_online = true;
            
            // ⭐ 1. 記住對方的 MAC 位址
            memcpy(gl_remote_bda, param->connect.remote_bda, sizeof(esp_bd_addr_t));
            
            // 🚀 【新增這行】發起 MTU 擴充請求，突破 20 Bytes 限制！
            esp_ble_gattc_send_mtu_req(gattc_if, param->connect.conn_id);
            
            // ⭐ 2. 尋找指定的 Service
            esp_bt_uuid_t filter_uuid = { .len = ESP_UUID_LEN_16, .uuid.uuid16 = GATTS_SERVICE_UUID };
            esp_ble_gattc_search_service(gattc_if, param->connect.conn_id, &filter_uuid);
            break;

        case ESP_GATTC_SEARCH_CMPL_EVT:
        {
            // ⭐ 3. 搜尋完成後，找出用來傳輸資料的 Characteristic (UUID: 0xFF01) 並註冊
            ESP_LOGI("BLE_GATTC", "🔍 服務搜尋完成，正在掛載資料監聽...");
            if (param->search_cmpl.status != ESP_GATT_OK) {
                break;
            }
            
            esp_bt_uuid_t char_uuid = { .len = ESP_UUID_LEN_16, .uuid.uuid16 = GATTS_CHAR_UUID };
            esp_gattc_char_elem_t result;
            uint16_t count = 1;
            
            // 透過 UUID 取得特徵值的 handle
            esp_err_t err = esp_ble_gattc_get_char_by_uuid(gattc_if, param->search_cmpl.conn_id, 0x0001, 0xFFFF, char_uuid, &result, &count);
            if (err == ESP_OK && count > 0) {
                // 註冊 Notify 監聽
                esp_ble_gattc_register_for_notify(gattc_if, gl_remote_bda, result.char_handle);
            } else {
                ESP_LOGE("BLE_GATTC", "❌ 找不到指定的特徵值 (Characteristic)");
            }
            break;
        }
            
        case ESP_GATTC_NOTIFY_EVT:
            // ⭐ 4. 收到 Notify！直接解析 SLAVE 傳來的字串
            process_slave_sensor_data(param->notify.value, param->notify.value_len);
            break;

        case ESP_GATTC_DISCONNECT_EVT:
            ESP_LOGE("BLE_GATTC", "💔 與 SLAVE 斷線！啟動本機容錯機制，重新掃描...");
            g_is_slave_online = false;
            
            if (g_system_role == 0) {
                // 1. 啟動雷達繼續找 Slave
                esp_ble_gap_start_scanning(0); 
                
                // 🌟 關鍵修復：重新掃描的同時，強制再次打開對外的網頁廣播！
                esp_ble_gap_start_advertising(&adv_params);
                ESP_LOGI("BLE_GATTS", "👑 MASTER 雖然在找 Slave，但依然保持對外網頁廣播！");
            }
            break;
            
        default:
            break;
    }
}

void start_bluetooth(void)
{
    // 1. 初始化並啟用控制器 (雙模)
    esp_bt_controller_status_t bt_status = esp_bt_controller_get_status();
    if (bt_status == ESP_BT_CONTROLLER_STATUS_IDLE) {
        esp_bt_controller_config_t cfg = BT_CONTROLLER_INIT_CONFIG_DEFAULT();
        ESP_ERROR_CHECK(esp_bt_controller_init(&cfg));
        ESP_ERROR_CHECK(esp_bt_controller_enable(ESP_BT_MODE_BTDM)); 
    }

    // 2. 初始化並啟用 Bluedroid
    esp_bluedroid_status_t bluedroid_status = esp_bluedroid_get_status();
    if (bluedroid_status == ESP_BLUEDROID_STATUS_UNINITIALIZED) {
        ESP_ERROR_CHECK(esp_bluedroid_init());
        ESP_ERROR_CHECK(esp_bluedroid_enable()); 
    }

    // 3. 註冊 BLE 網頁調音通道
    // 3. 註冊 BLE 網頁調音與雙機通訊通道
    ESP_ERROR_CHECK(esp_ble_gap_register_callback(gap_event_handler));
    
    // (原本的 Server)
    ESP_ERROR_CHECK(esp_ble_gatts_register_callback(gatts_event_handler));
    ESP_ERROR_CHECK(esp_ble_gatts_app_register(0));
    
    // ⭐ (新增的 Client)
    ESP_ERROR_CHECK(esp_ble_gattc_register_callback(gattc_event_handler));
    ESP_ERROR_CHECK(esp_ble_gattc_app_register(0));
	
    esp_ble_gatt_set_local_mtu(500);

    // ==========================================
    // 4. 註冊傳統藍牙 (A2DP 音樂與 HFP 通話)
    // ==========================================
    esp_bt_gap_set_device_name(g_bt_name);
    esp_bt_gap_set_scan_mode(ESP_BT_CONNECTABLE, ESP_BT_GENERAL_DISCOVERABLE);

    // ⭐ 關鍵修復：加入 SSP (Secure Simple Pairing) 安全配對設定！
    // 告訴手機：「我是一副耳機，沒有螢幕也沒有鍵盤，請直接讓我配對」
    esp_bt_sp_param_t param_type = ESP_BT_SP_IOCAP_MODE;
    esp_bt_io_cap_t iocap = ESP_BT_IO_CAP_NONE; 
    esp_bt_gap_set_security_param(param_type, &iocap, sizeof(uint8_t));

    // 備用防護：設定傳統 Legacy 配對的 PIN 碼為 0000
    esp_bt_pin_type_t pin_type = ESP_BT_PIN_TYPE_FIXED;
    esp_bt_pin_code_t pin_code = {'0', '0', '0', '0'};
    esp_bt_gap_set_pin(pin_type, 4, pin_code);
    // ==========================================

    esp_bt_cod_t cod;
    memset(&cod, 0, sizeof(cod));
    cod.major = 0x04; cod.minor = 0x04; cod.service = 0x001A; // 耳機設備
    esp_bt_gap_set_cod(cod, ESP_BT_SET_COD_MAJOR_MINOR);

    ESP_ERROR_CHECK(esp_avrc_ct_init());
    ESP_ERROR_CHECK(esp_avrc_tg_init());
    ESP_ERROR_CHECK(esp_avrc_ct_register_callback(bt_app_avrc_ct_cb));
    ESP_ERROR_CHECK(esp_avrc_tg_register_callback(bt_app_avrc_tg_cb));

    a2dp_init(); 
    
    esp_hf_client_register_callback(bt_app_hf_client_cb);
    esp_hf_client_register_data_callback(bt_app_hf_client_incoming_data_cb, bt_app_hf_client_outgoing_data_cb);
    esp_hf_client_init();
    esp_hf_client_send_nrec();

    ESP_LOGI("BT_DEBUG", "✅ 藍牙雙模 (BLE 調音 + A2DP 音樂 + HFP 通話) 完美復活！");
}

void check_8311_mode()
{
    // 假設有一個 i2c_read 函式可以讀 ES8311 暫存器
    uint8_t reg00 = i2c_read_reg(0x18, 0x00);

    if (reg00 & (1 << 6)) {
        printf("ES8311 mode: master\n");
    } else {
        printf("ES8311 mode: slave\n");
    }
	
}


void tone_task(void *arg)
{
    int16_t buffer[BUF_LEN * 2];
    size_t bytes_written;
    float phase = 0.0f;
    float step = 2 * PI * TONE_FREQ / SAMPLE_RATE;

    while (1) {
        for (int n = 0; n < BUF_LEN; n++) {
            float sample = sinf(phase);
            phase += step;
            if (phase > 2 * PI) phase -= 2 * PI; // 避免溢出
            int16_t val = (int16_t)(sample * 30000);
            buffer[2*n]   = val;
            buffer[2*n+1] = val;
        }
        i2s_channel_write(tx_handle, buffer, sizeof(buffer), &bytes_written, pdMS_TO_TICKS(100));
    }
}


void audio_init_default(void) {
    ESP_LOGI("AUDIO", "執行開機預設 Audio 初始化...");
	current_a2dp_sample_rate=44100;
    i2s_init_tx(current_a2dp_sample_rate);
	i2s_init_rx(current_a2dp_sample_rate);
	
    es8311_config_sample(current_a2dp_sample_rate);
    i2c_write(0x18,0x12,0x00);//////DAC ON
	
	update_8band_eq(current_a2dp_sample_rate);
    ESP_LOGI("AUDIO", "開機 Audio 初始化完成");
	print_i2s_status_reading();
	es8311_i2s_config_debug();
}


typedef struct {
    float freq;
    int duration_ms;
} note_t;
note_t happy_song[] = {
    {523.25, 250}, {587.33, 250}, {659.25, 250}, {698.46, 250}, // Do, Re, Mi, Fa
    {783.99, 500}, {783.99, 500},                              // So, So
    {880.00, 250}, {880.00, 250}, {880.00, 250}, {880.00, 250}, // La, La, La, La
    {783.99, 1000}                                             // So (結尾)
};








#define TABLE_SIZE 1024
static int16_t sin_table[TABLE_SIZE];

// 程式啟動時呼叫一次這個函式來填表
void init_sin_table() {
    for (int i = 0; i < TABLE_SIZE; i++) {
        // 🌟 必須乘上 32767.0，這樣系統的 0 dBFS 才會對齊真實的硬體極限！
        sin_table[i] = (int16_t)(sin(2.0 * M_PI * i / TABLE_SIZE) * 32767.0);
    }
}
// ==========================================================
// 🔊 醫療級純音產生器 (精準分貝輸出)
// ==========================================================
void play_pure_tone(float freq_hz, float target_db_hl, int duration_ms) {
    g_is_audiometry_mode = true;
    ringbuf_flush(music_ringbuf);
    init_sin_table();
    float dbfs = target_db_hl - 100.0f + g_spk_calib_offset;
    if (dbfs > 0.0f) dbfs = 0.0f;

    float multiplier = powf(10.0f, dbfs / 20.0f);

    int total_samples = (current_a2dp_sample_rate * duration_ms) / 1000;
    int chunks = total_samples / 128;
    uint32_t step = (uint32_t)((double)freq_hz * 4294967296.0 / (double)current_a2dp_sample_rate);
    static uint32_t phase = 0;
    int16_t buf[256];
    ESP_LOGW("DEBUG", "TARGET: %.1f, OFFSET: %.1f, DBFS: %.2f", target_db_hl, g_spk_calib_offset, dbfs);
    for (int c = 0; c < chunks; c++) {
        for (int i = 0; i < 128; i++) {
            uint16_t idx = (uint16_t)(phase >> 22);
            int16_t val = (int16_t)(sin_table[idx] * multiplier);
            buf[i * 2] = val;
            buf[i * 2 + 1] = val;
            phase += step;
        }
        // ⭐ 改回這裡：送進 RingBuffer
        xRingbufferSend(music_ringbuf, buf, sizeof(buf), portMAX_DELAY);
    }

    // 等待聲音播完
    vTaskDelay(pdMS_TO_TICKS(duration_ms + 100));
    g_is_audiometry_mode = false;
}

// 🏥 專業版全自動 8 頻段原位測聽 (含 5取3 穩定性驗證)
void audiometry_task(void* arg) {
    const float TEST_FREQS[8] = { 250.0f, 500.0f, 1000.0f, 2000.0f, 3000.0f, 4000.0f, 6000.0f, 8000.0f };
	float final_threshold = 0.0f;
    while (1) {
        if (g_run_audiometry) {
            ESP_LOGW("CLINIC", "🏥 聽力驗配：啟動 5取3 穩定性驗證模式...");
            g_audio_mode = 0; // 強制通透，確保聽力環境純淨
            
            for (int f = 0; f < 8; f++) {
                float freq = TEST_FREQS[f];
                float thresholds[5] = {0}; // 儲存 5 次測試的結果
                int attempts = 0;
                bool frequency_done = false;

                ESP_LOGW("CLINIC", "▶️ 開始測量頻率: %.0f Hz", freq);

                // 嘗試最多 5 次
                for (attempts = 0; attempts < 5; attempts++) {
                    float test_db_hl = 40.0f; // 初始音量
                    bool current_test_success = false;

                    // 執行一次標準閾值搜索
                    while (!current_test_success && test_db_hl <= 90.0f) {
                        g_user_heard_it = false;
                        play_pure_tone(freq, test_db_hl, 500);
                        
                        // 等待 1.5 秒讓病患反應
                        for(int w=0; w<15; w++) {
                            if(g_user_heard_it) break;
                            vTaskDelay(pdMS_TO_TICKS(100));
                        }

                        if (g_user_heard_it) {
                            thresholds[attempts] = test_db_hl;
                            current_test_success = true;
                        } else {
                            test_db_hl += 5.0f; // 聽不到就加大音量
                        }
                    }
                    
                    if (!current_test_success) thresholds[attempts] = 95.0f; // 超出聽力範圍
                    ESP_LOGI("CLINIC", "Attempt %d: %.0f dB", attempts + 1, thresholds[attempts]);
                    vTaskDelay(pdMS_TO_TICKS(500));
                }

                // --- ⭐ 嚴謹穩定性判定邏輯 ---
                float sum = 0;
                int valid_count = 0;
                bool stable = false;

                // 檢查是否有至少 3 個數值在 ±5dB 誤差範圍內
                for(int i = 0; i < 5; i++) {
                    int group_size = 0;
                    float group_sum = 0;
                    for(int j = 0; j < 5; j++) {
                        if(fabsf(thresholds[i] - thresholds[j]) <= 5.0f) {
                            group_size++;
                            group_sum += thresholds[j];
                        }
                    }
                    if(group_size >= 3) {
                        final_threshold = group_sum / group_size; // 取穩定群組的平均值
                        stable = true;
                        break;
                    }
                }

                if (stable) {
                    ESP_LOGW("CLINIC", "✅ 穩定！%.0f Hz 閾值最終判定: %.1f dB", freq, final_threshold);
                    
                    // ==================================================
                    // 🚨 修正後的聽力補償演算法 (防爆音安全版)
                    // ==================================================
                    
                    // 1. 設定正常人的聽力基準線 (以你的測試起始音量 40dB 為基準)
                    const float NORMAL_HEARING_BASE = 40.0f;
                    
                    // 2. 計算真實的聽力損失 (Hearing Loss)
                    float hearing_loss = final_threshold - NORMAL_HEARING_BASE;
                    if (hearing_loss < 0.0f) {
                        hearing_loss = 0.0f; // 聽力比正常人好或一樣，不須補償
                    }

                    // 3. 半增益法則 (只補償損失的一半)
                    float target_gain = hearing_loss / 2.0f;

                    // 4. 數位防爆音絕對限制 (Digital Hard Limit)
                    // 在 ESP32 16-bit 系統中，單一頻段 EQ 絕對不要超過 +12.0 dB
                    const float MAX_SAFE_GAIN = 12.0f;
                    if (target_gain > MAX_SAFE_GAIN) {
                        target_gain = MAX_SAFE_GAIN;
                    }

                    // 5. 寫入系統變數
                    g_user_eq[f] = target_gain;
                    g_target_gains_db[f] = g_user_eq[f] + g_auto_offset[f];
                    
                    ESP_LOGW("CLINIC", "🎚️ %.0f Hz 聽損: %.1f dB -> 換算 EQ 增益為: +%.1f dB", freq, hearing_loss, g_user_eq[f]);
                    
                } else {
                    ESP_LOGE("CLINIC", "❌ 該頻率測試數值波動過大 (不穩定)！請考慮重測此頻段。");
                    // 波動過大時，我們可以選擇保留預設值或前一次的數值
                }
            }

            update_8band_eq(current_a2dp_sample_rate);
            ESP_LOGW("CLINIC", "🎉 驗配完成！專屬 EQ 已套用。");
            g_run_audiometry = false;
        }
        vTaskDelay(pdMS_TO_TICKS(100));
    }
}
void passthrough_task(void *arg) {
    int16_t sine_buf[512]; 
    size_t bytes_written = 0;
    static uint32_t phase_accumulator = 0;
    
    float sample_rate = 16000.0;
    init_sin_table(); 

    // 序列播放需要的變數
    int song_length = sizeof(happy_song) / sizeof(note_t);
    int note_idx = 0;
    TickType_t last_note_time = xTaskGetTickCount();

    ESP_LOGI(TAG, "Happy Song Player Started...");

    while (1) {
        // 1. 自動切換音符邏輯
        TickType_t current_time = xTaskGetTickCount();
        if ((current_time - last_note_time) * portTICK_PERIOD_MS >= happy_song[note_idx].duration_ms) {
            note_idx = (note_idx + 1) % song_length; // 循環播放
            current_freq = happy_song[note_idx].freq; // 更新全域變數
            last_note_time = current_time;
            ESP_LOGI(TAG, "Playing note: %.2f Hz", current_freq);
        }

        // ✅ 產生波形：直接使用你剛剛抓到的音符頻率
        float freq = current_freq; 
        
        // 順便把公式裡的 sample_rate 換成 current_a2dp_sample_rate，這樣切換 16k/48k 時音高才不會跑掉！
        uint32_t step = (uint32_t)((double)freq * 4294967296.0 / (double)current_a2dp_sample_rate);
        for (int i = 0; i < 256; i++) {
            uint16_t index = (uint16_t)(phase_accumulator >> 22);
            int16_t val = sin_table[index];
            
            sine_buf[i * 2]     = val;
            sine_buf[i * 2 + 1] = val;
            
            phase_accumulator += step;
        }

        i2s_channel_write(tx_handle, sine_buf, sizeof(sine_buf), &bytes_written, portMAX_DELAY);
    }
}


void hp_timer_callback(TimerHandle_t xTimer)
{
    int state = gpio_get_level(GPIO_NUM_19);
    if (state != last_state) {
        if (state == 0) {
            ESP_LOGI(HP_TAG, "耳機插入 (Low)");
        } else {
            ESP_LOGI(HP_TAG, "耳機拔出 (High)");
        }
        last_state = state;
    }
}

void mic_read_task(void *arg)
{
    // ⭐ 改變 1：宣告成 int16_t 陣列，為未來的 FFT 和數學運算鋪路
    int16_t audio_buffer[256]; 
    size_t bytes_read = 0;

    ESP_LOGI("MIC", "🎙️ 麥克風極速收音任務啟動 (具備硬體熱插拔防護)！");

    while (1)
    {
        // ==========================================================
        // 🚨 終極防護網！讀取麥克風之前，必須檢查旗標與 Handle
        // ==========================================================
        if (!g_i2s_is_reconfiguring && rx_handle != NULL) 
        {
            size_t bytes_read = 0;
            // 正常讀取麥克風資料
            esp_err_t res = i2s_channel_read(rx_handle, audio_buffer, sizeof(audio_buffer), &bytes_read, portMAX_DELAY);

            if (res == ESP_OK && bytes_read > 0)
            {
                // 1. 正常送給 Mixer 混音
                xRingbufferSend(mic_ringbuf, (void*)audio_buffer, bytes_read, pdMS_TO_TICKS(10));
                
                // 2. 送給 FFT 前，破解立體聲翻倍陷阱 (我們之前寫好的邏輯)
                if (fft_ringbuf != NULL) {
                    int16_t mono_buffer[512] = {0}; 
                    int samples = bytes_read / sizeof(int16_t);
                    int mono_idx = 0;
                    
                    for (int i = 0; i < samples; i += 2) {
                        mono_buffer[mono_idx++] = audio_buffer[i]; 
                    }
                    xRingbufferSend(fft_ringbuf, (void*)mono_buffer, mono_idx * sizeof(int16_t), 0); 
                }
            }
        } 
        else 
        {
            // ⚠️ 如果系統正在切換頻率 (APLL 釋放重建中)，收音員就睡 10ms，絕對不去碰壞掉的 handle！
            vTaskDelay(pdMS_TO_TICKS(10));
        }
    }
}
void fft_task(void *arg)
{
    ESP_LOGI("FFT", "📊 多頻段頻譜分析任務啟動 (綁定 Core 0)！");
    // 引入全域的取樣率變數，以便精準計算真實頻率
    extern volatile uint32_t current_a2dp_sample_rate; 

    // 1. 初始化 DSP 與 漢寧窗 (Hann Window)
    dsps_fft2r_init_fc32(NULL, CONFIG_DSP_MAX_FFT_SIZE);
    
    // ⭐ 加上 static，把它們從狹窄的 Task Stack 移到全域記憶體！
    static float fft_data[2048]; 
    static float wind[1024];
    static int16_t sample_accumulator[1024];

    dsps_wind_hann_f32(wind, 1024);

    // 2. 建立「蓄水池」指標
    int accum_idx = 0;
    size_t bytes_received = 0;

    while(1) 
    {
		// ==========================================================
        // 🛡️ 容錯機制 (Fallback) 判斷
        // ==========================================================
        // 如果我是 MASTER，而且 SLAVE 正在穩定連線中傳送資料
        if (g_system_role == 0 && g_is_slave_online == true) {
            // 我不需要自己算 FFT 了！直接清空收到的麥克風資料，睡覺省電
            size_t dummy_bytes;
            void *dummy_data = xRingbufferReceive(fft_ringbuf, &dummy_bytes, pdMS_TO_TICKS(100));
            if (dummy_data != NULL) {
                vRingbufferReturnItem(fft_ringbuf, dummy_data);
            }
            continue; // 跳過下面的 FFT 運算，直接進入下一次迴圈
        }
		int64_t start_time = esp_timer_get_time();
        // 阻塞等待，直到 mic_read_task 丟資料過來
        int16_t *data = (int16_t *)xRingbufferReceive(fft_ringbuf, &bytes_received, portMAX_DELAY);
        
        if (data != NULL) 
        {
            int num_samples = bytes_received / 2; // 收到了 256 個樣本 (128 L + 128 R)

            // 3. 我們只取「左耳」的聲音來分析，裝進蓄水池
            for(int i = 0; i < num_samples; i ++ ) {
                if (accum_idx < 1024) {
                    sample_accumulator[accum_idx++] = data[i];
                }
            }
            vRingbufferReturnItem(fft_ringbuf, (void *)data);

            // ==========================================
            // ⭐ 蓄水池滿了！開始執行 FFT 魔術！
            // ==========================================
            if (accum_idx >= 1024) 
            {
                // A. 轉成浮點數、套用漢寧窗、並填入交錯陣列
                for (int i = 0; i < 1024; i++) {
                    fft_data[i * 2 + 0] = (float)sample_accumulator[i] * wind[i]; // 實部
                    fft_data[i * 2 + 1] = 0;                                      // 虛部
                }

                // B. 呼叫底層 FPU 硬體加速運算 FFT
                dsps_fft2r_fc32(fft_data, 1024);
                dsps_bit_rev_fc32(fft_data, 1024);

                // ==========================================
                // C. 8 頻段分析 + 最強窄頻追蹤 (狙擊情報)
                // ==========================================
                float band_max_db[8] = {-100.0f, -100.0f, -100.0f, -100.0f, -100.0f, -100.0f, -100.0f, -100.0f}; 
                float freq_resolution = (float)current_a2dp_sample_rate / 1024.0f; 
                
                float max_power = 0;     // 新增：尋找最強能量
                int max_freq_idx = 0;    // 新增：最強能量的 index

                for (int i = 2; i < 512; i++) { 
                    float re = fft_data[i*2 + 0];
                    float im = fft_data[i*2 + 1];
                    float power = re * re + im * im; // 避免在這裡用 sqrt，節省一次算力
                    float magnitude = sqrtf(power);
                    
                    // --- 1. 抓出最吵的單一頻率 (狙擊目標) ---
                    if (power > max_power) {
                        max_power = power;
                        max_freq_idx = i;
                    }

                    // --- 2. 計算 8 頻段 dBFS (散彈槍場景分析) ---
                    float normalized_mag = magnitude / (512.0f * 32768.0f);
                    float dbfs = -100.0f;
                    if (normalized_mag > 0.00001f) {
                        dbfs = 20.0f * log10f(normalized_mag);
                    }

                    float freq = i * freq_resolution;

                    if      (freq < 250.0f)  { if (dbfs > band_max_db[0]) band_max_db[0] = dbfs; } 
                    else if (freq < 500.0f)  { if (dbfs > band_max_db[1]) band_max_db[1] = dbfs; } 
                    else if (freq < 1000.0f) { if (dbfs > band_max_db[2]) band_max_db[2] = dbfs; } 
                    else if (freq < 2000.0f) { if (dbfs > band_max_db[3]) band_max_db[3] = dbfs; } 
                    else if (freq < 3000.0f) { if (dbfs > band_max_db[4]) band_max_db[4] = dbfs; } 
                    else if (freq < 4000.0f) { if (dbfs > band_max_db[5]) band_max_db[5] = dbfs; } 
                    else if (freq < 6000.0f) { if (dbfs > band_max_db[6]) band_max_db[6] = dbfs; } 
                    else                     { if (dbfs > band_max_db[7]) band_max_db[7] = dbfs; } 
                }

                // ==========================================
                // D. 決策大腦：發布狙擊命令
                // ==========================================
                float peak_freq = max_freq_idx * freq_resolution;
                
                // 假設 power 大於這個門檻 (需要根據麥克風實際情況微調)，且頻率在人類最敏感的刺耳範圍 (300~4000Hz)
                if (max_power > 25000000000.0f && peak_freq > 300.0f && peak_freq < 4000.0f) {
                    g_target_noise_freq = peak_freq; // 鎖定目標！寫入全域變數交給 Core 1 擊殺
                } else {
                    g_target_noise_freq = 0.0f;      // 解除鎖定
                }

                // 為了方便除錯，印出追蹤狀態 (一樣每 10 次印一次)
                static int print_cnt = 0;
                if (++print_cnt >= 10) {
                    if (g_target_noise_freq > 0.0f) {
                        ESP_LOGW("FFT_BRAIN", "🎯 發現強烈窄頻噪音！鎖定目標: %.1f Hz", g_target_noise_freq);
                    } else {
                        //ESP_LOGI("FFT_8BAND", "[<250: %5.1f] [500: %5.1f] [1k: %5.1f] [2k: %5.1f] [3k: %5.1f] [4k: %5.1f] [6k: %5.1f] [>6k: %5.1f]", 
                                 //band_max_db[0], band_max_db[1], band_max_db[2], band_max_db[3], 
                                 //band_max_db[4], band_max_db[5], band_max_db[6], band_max_db[7]);
                    }
                    print_cnt = 0;
                }
                // ==========================================
                // 🛠️ 1. 套用硬體物理校正 (dBFS -> dB SPL)
                // ==========================================
                // 在進入動態 EQ 判斷前，先把所有頻段的能量轉成真實物理音量
                for (int b = 0; b < 8; b++) {
                    if (band_max_db[b] > -99.0f) {
                        band_max_db[b] += g_mic_calib_offset; // ⭐ 換成麥克風的變數
                    }
                }

                // ==========================================
                // 🤖 2. 動態 EQ (真實物理聲壓版)
                // ==========================================
                static const float default_gains[8] = { 0.0f, -2.0f, 3.0f, 4.0f, 2.0f, 0.0f, -8.0f, -12.0f };

                // ⭐ 門檻大進化：現在使用的是「真實世界的物理分貝 (dB SPL)」
                // 一般講話約 60dB，馬路噪音約 80dB，機房/救護車約 90~100dB
                const float PAIN_THRESHOLD = 85.0f; 
                const float SAFE_THRESHOLD = 75.0f;

                bool need_update = false;
                static int auto_eq_cooldown = 0;

                if (auto_eq_cooldown > 0) {
                    auto_eq_cooldown--;
                }
                else {
                    for (int b = 0; b < 8; b++) {
                        float current_pain_threshold = PAIN_THRESHOLD;
                        float attack_step = 0.5f;
                        float release_step = 0.5f;
                        float min_gain = -18.0f;

                        if (b == 2 || b == 3 || b == 4) {
                            current_pain_threshold = 95.0f;
                            attack_step = 0.2f;
                            min_gain = 0.0f;
                        } else if (b == 0 || b == 7) {
                            current_pain_threshold = 75.0f;
                            attack_step = 1.0f;
                            min_gain = -18.0f;
                        }

                        // 🔴 狀況 1：遇到噪音，瞬間重力壓制 (Attack)
                        if (band_max_db[b] > current_pain_threshold) {
                            // ⭐ 改為判斷與修改 auto_offset
                            if (g_auto_offset[b] > min_gain) { 
                                float overflow_db = band_max_db[b] - current_pain_threshold;
                                float dynamic_attack = overflow_db * 1.5f; 
                                if (dynamic_attack < 1.0f) dynamic_attack = 1.0f;

                                g_auto_offset[b] -= dynamic_attack;

                                if (g_auto_offset[b] < min_gain) g_auto_offset[b] = min_gain;
                                need_update = true;
                            }
                        }
                        // 🟢 狀況 2：環境安全，溫和緩慢恢復 (Release)
                        else if (band_max_db[b] < SAFE_THRESHOLD) {
                            // ⭐ 改為讓 auto_offset 回歸 0.0f
                            if (g_auto_offset[b] < 0.0f) { 
                                if (g_auto_offset[b] < -15.0f) {
                                    g_auto_offset[b] += (release_step * 5.0f);
                                } else {
                                    g_auto_offset[b] += release_step;
                                }

                                if (g_auto_offset[b] > 0.0f) g_auto_offset[b] = 0.0f; // 最高就是回到 0
                                need_update = true;
                            }
                        }
                    }

                    // ==========================================
                    // 🔄 4. 結算總和並通知 Core 1
                    // ==========================================
                    if (need_update) {
                        // 把 基準層 + 動態層 結算進最終輸出層
                        for(int i=0; i<8; i++){
                            g_target_gains_db[i] = g_user_eq[i] + g_auto_offset[i];
                        }
                        
                        update_8band_eq(current_a2dp_sample_rate);
                        ESP_LOGW("AUTO_EQ", "🤖 物理防護作動！當前實際輸出: [%.1f, %.1f, %.1f, %.1f, %.1f, %.1f, %.1f, %.1f]",
                            g_target_gains_db[0], g_target_gains_db[1], g_target_gains_db[2], g_target_gains_db[3],
                            g_target_gains_db[4], g_target_gains_db[5], g_target_gains_db[6], g_target_gains_db[7]);
                        auto_eq_cooldown = 2;
                    }
                }                 
                // 處理完畢，重置蓄水池準備接下一批資料
                accum_idx = 0;
                
                // 讓出 CPU 一下下，避免 Watchdog 咬人
                vTaskDelay(pdMS_TO_TICKS(10)); 
            }
        }
		int64_t end_time = esp_timer_get_time();
        int64_t cost_time_us = end_time - start_time;
		//ESP_LOGI("FFT_TIME", "📊 執行一次大 FFT 耗時: %.2f ms", (float)cost_time_us / 1000.0f);
    }
}

void sys_ctrl_task(void *pvParameters)
{
    while(1) {
        // ==========================================================
        // 📞 檢查是否需要切換到通話模式 (16kHz)
        // ==========================================================
        if (g_play_bt_conn_sound) {
            g_play_bt_conn_sound = false;
            play_bluetooth_connected_sound();
        }

        if (g_play_bt_disc_sound) {
            g_play_bt_disc_sound = false;
            play_bluetooth_disconnected_sound();
        }

        vTaskDelay(pdMS_TO_TICKS(20));
		if (g_flag_need_i2s_reconfig_16k) {
            ESP_LOGW("SYS_CTRL", "🚨 偵測到通話建立！啟動 16kHz 硬體重配流程...");
            g_hfp_reconfig_lock = true;
			g_i2s_is_reconfiguring = true;
			
			vTaskDelay(pdMS_TO_TICKS(50)); 
            // 🛑【逼逼聲終結者】：在休息前，直接把 DMA 掐斷！
            // 防止這 50ms 內喇叭因為沒資料而瘋狂重播產生 125Hz 逼逼聲！
            force_reset_i2s_clocks();

            vTaskDelay(pdMS_TO_TICKS(150));

			i2s_init_tx(16000);
            i2s_init_rx(16000);
            es8311_init();
            es8311_config_sample(16000);
			update_8band_eq(16000);
			i2c_write(0x18,0x12,0x00);//////DAC ON
			es7243e_init();

            
            current_a2dp_sample_rate = 16000;
            g_flag_need_i2s_reconfig_16k = false;
            g_hfp_reconfig_lock = false;
            // ⭐ 3. 重建完畢，放下警告旗，大家繼續工作！
            g_i2s_is_reconfiguring = false;
        }

        // 🎵 切換回 44.1kHz (A2DP) 的地方也一模一樣！
        if (g_flag_need_i2s_reconfig_44p1k) {
            ESP_LOGW("SYS_CTRL", "🛑 偵測到通話結束！恢復 44.1kHz 硬體重配流程...");
            
            g_i2s_is_reconfiguring = true;  // 撤退
            vTaskDelay(pdMS_TO_TICKS(50));
            force_reset_i2s_clocks();

            vTaskDelay(pdMS_TO_TICKS(150));
            i2s_init_tx(44100);
            i2s_init_rx(44100);
			es8311_init();
            es8311_config_sample(44100);
			update_8band_eq(44100);
			i2c_write(0x18,0x12,0x00);//////DAC ON
			es7243e_init();
            
            current_a2dp_sample_rate = 44100;
            g_flag_need_i2s_reconfig_44p1k = false;
            
            g_i2s_is_reconfiguring = false; // 放行
        }

        vTaskDelay(pdMS_TO_TICKS(20)); // 每 20ms 巡邏一次
    }
}
// ==========================================================
// 🧠 論文核心：多場景決策大腦 (綁定 Core 0，不卡音訊)
// ==========================================================
void scene_detect_task(void *arg) {
    ESP_LOGI("SCENE", "🧠 多場景動態大腦啟動！");
    SceneMode last_scene = SCENE_QUIET;

    while(1) {
        SceneMode temp_scene = SCENE_QUIET;

        // 1. 初步判斷當前環境
        if (g_env_rms < 200.0f) {
            temp_scene = SCENE_QUIET;
        } else if (g_env_rms >= 200.0f && !g_vad_active) {
            temp_scene = SCENE_NOISY_NO_VOICE;
        } else {
            temp_scene = SCENE_SPEECH;
        }

        // ====================================================
        // 🌟 修復 2：狀態遲滯與防彈跳 (Debounce / Hold Time)
        // ====================================================
        static SceneMode candidate_scene = SCENE_QUIET;
        static int confirm_count = 0;

        // 如果初步判斷跟上次一樣，就增加確認次數
        if (temp_scene == candidate_scene) {
            confirm_count++;
        } else {
            // 如果不一樣，重新開始觀察
            candidate_scene = temp_scene;
            confirm_count = 1;
        }

        // 必須「連續 3 次 (約 1.5 秒)」都偵測到同一個場景，才真正執行切換！
        if (confirm_count >= 3 && g_current_scene != candidate_scene) {
            
            g_current_scene = candidate_scene; // 正式切換全域狀態
            
            switch(g_current_scene) {
                case SCENE_QUIET:
                    ESP_LOGI("SCENE", "🟢 安靜場景：切換【平坦通透模式】");
                    for(int i=0; i<8; i++) g_scene_offset[i] = 0.0f;
                    break;
                    
                case SCENE_NOISY_NO_VOICE:
                    ESP_LOGI("SCENE", "🟡 吵雜(無人聲)：切換【深度降噪模式】");
                    g_scene_offset[0] = -6.0f; g_scene_offset[1] = -4.0f;
                    g_scene_offset[2] = 0.0f;  g_scene_offset[3] = 0.0f;
                    g_scene_offset[4] = 0.0f;  g_scene_offset[5] = 0.0f;
                    g_scene_offset[6] = -3.0f; g_scene_offset[7] = -6.0f;
                    break;
                    
                case SCENE_SPEECH:
                    ESP_LOGI("SCENE", "🔴 語音溝通中：切換【語音增強模式】");
                    g_scene_offset[0] = -2.0f; g_scene_offset[1] = -2.0f;
                    g_scene_offset[2] = 3.0f;  g_scene_offset[3] = 4.0f;
                    g_scene_offset[4] = 2.0f;  g_scene_offset[5] = 0.0f;
                    g_scene_offset[6] = -2.0f; g_scene_offset[7] = -4.0f;
                    break;
            }
            
            // 通知 DSP 系統重新組合 EQ
            extern volatile uint32_t current_a2dp_sample_rate;
            update_8band_eq(current_a2dp_sample_rate);
        }
        static int debug_cnt = 0;
        if (++debug_cnt % 4 == 0) { 
            ESP_LOGW("SCENE_PROBE", "📊 現況 -> 能量(RMS): %5.1f | 閘門閥值: %d | VAD: %s", 
                     g_env_rms, 
                     g_noise_gate_threshold, 
                     g_vad_active ? "🗣️ 有人講話" : "🔇 安靜");
        }
        vTaskDelay(pdMS_TO_TICKS(500)); // 每半秒偵測一次
    }
}
void play_system_boot_sound(void) {
    ESP_LOGW("AUDIO_EFFECT", "🔊 系統就緒，開始播放黃金開機和弦...");

    // ─── 這裡使用【方案 1：科技感上升和弦】範例 ───
    // 參數：play_pure_tone( 頻率Hz, 目標分貝dB_HL, 持續毫秒ms )
    
    play_pure_tone(440.0f, 65.0f, 200); // 第一聲：溫暖基音
    vTaskDelay(pdMS_TO_TICKS(30));       // 微小停頓讓音符有層次
    
    play_pure_tone(554.0f, 65.0f, 200); // 第二聲：和弦推進
    vTaskDelay(pdMS_TO_TICKS(30));
    
    play_pure_tone(659.0f, 65.0f, 200); // 第三聲：微調高音量
    vTaskDelay(pdMS_TO_TICKS(30));
    
    play_pure_tone(880.0f, 65.0f, 700); // 第四聲：明亮尾音拉長
    
    ESP_LOGI("AUDIO_EFFECT", "✅ 開機音效播放完畢，輔聽系統正式上線！");
}
// ================= MAIN =================
void app_main()
{
	gpio_reset_pin(BOARD_PA_EN_PIN);
	gpio_set_direction(BOARD_PA_EN_PIN, GPIO_MODE_OUTPUT);
	gpio_set_level(BOARD_PA_EN_PIN, 1); // 🔥 關鍵：拉高它，Codec 才有電
	
	gpio_reset_pin(BOARD_SY_LED1);
	gpio_set_direction(BOARD_SY_LED1, GPIO_MODE_OUTPUT);
	
	gpio_reset_pin(BOARD_SY_LED2);
	gpio_set_direction(BOARD_SY_LED2, GPIO_MODE_OUTPUT);
	
	
	// 檢查內部 RAM
	ESP_LOGW("MEM", "🧠 內部 SRAM 剩餘: %d bytes", heap_caps_get_free_size(MALLOC_CAP_INTERNAL));

	// 檢查外部 PSRAM (如果印出來是 0，代表你的板子根本沒有 PSRAM！)
	ESP_LOGW("MEM", "📦 外部 PSRAM 剩餘: %d bytes", heap_caps_get_free_size(MALLOC_CAP_SPIRAM));
	gpio_set_level(BOARD_SY_LED1, 1); // 🔥 關鍵：拉高它，Codec 才有電
	vTaskDelay(pdMS_TO_TICKS(100));
    i2c_init();
	gpio_set_level(BOARD_SY_LED1, 0); // 🔥 關鍵：拉高它，Codec 才有電
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);
	if (g_ota_mode_flag == OTA_MAGIC_NUM) {
        ESP_LOGI(TAG, "===============================");
        ESP_LOGI(TAG, "   進入專屬 OTA 更新模式");
        ESP_LOGI(TAG, "===============================");
        
        g_ota_mode_flag = 0; // 洗掉魔法數字，確保下次重啟回到一般模式

        wifi_init_softap();  // 啟動我們剛剛寫的 OTA 熱點
        start_webserver();   // 啟動你的 OTA 網頁伺服器
        
        return; // 🛑 直接 return！不執行下面的 I2S、藍牙與 DSP！
    }
	ESP_LOGI(TAG, "===============================");
    ESP_LOGI(TAG, "   進入正常助聽器運作模式");
    ESP_LOGI(TAG, "===============================");
	ESP_LOGI(TAG, "firmware_20260608_1610");
    g_ota_mode_flag = 0;
	load_calibration_from_flash();
	load_audio_tuning_from_nvs();
	gpio_reset_pin(GPIO_NUM_21);
    gpio_set_direction(GPIO_NUM_21, GPIO_MODE_OUTPUT);
	gpio_set_level(GPIO_NUM_21, 0);
	ESP_LOGI(TAG, "PA_ON");
	gpio_reset_pin(GPIO_NUM_19);
    gpio_set_direction(GPIO_NUM_19, GPIO_MODE_INPUT);
    gpio_set_pull_mode(GPIO_NUM_19, GPIO_PULLUP_ONLY);
	i2s_init_tx(44100);
    vTaskDelay(pdMS_TO_TICKS(200));
	i2s_init_rx(44100);
	vTaskDelay(pdMS_TO_TICKS(100)); // 等時鐘穩定
	es8311_init();
	check_8311_mode();
	start_bluetooth();
	audio_init_default();
	es7243e_init();
	if (hfp_ringbuf == NULL) {
        hfp_ringbuf = xRingbufferCreate(8192, RINGBUF_TYPE_BYTEBUF);
        if (hfp_ringbuf == NULL) {
            ESP_LOGE("SYS", "❌ 嚴重錯誤：無法分配記憶體給 HFP RingBuffer！");
        } else {
            ESP_LOGI("SYS", "✅ HFP RX 郵筒建立成功！");
        }
    }
	if (mic_ringbuf == NULL) {
        mic_ringbuf = xRingbufferCreate(8192, RINGBUF_TYPE_BYTEBUF);
        if (mic_ringbuf == NULL) {
            ESP_LOGE("SYS", "❌ 嚴重錯誤：無法分配記憶體給 RingBuffer！");
        } else {
            ESP_LOGI("SYS", "✅ 麥克風郵筒建立成功！");
        }
    }
	if (music_ringbuf == NULL) {
        // ==========================================================
        // 🌟 終極懶人法：把 16KB 的大水庫直接建在外部 PSRAM 上！
        // 這樣內部 SRAM 一滴都不會少，藍牙絕對不會再當機！
        // ==========================================================
        uint8_t *rb_storage = (uint8_t *)heap_caps_malloc(16384, MALLOC_CAP_SPIRAM);
        StaticRingbuffer_t *rb_struct = (StaticRingbuffer_t *)heap_caps_malloc(sizeof(StaticRingbuffer_t), MALLOC_CAP_SPIRAM);
        
        if (rb_storage != NULL && rb_struct != NULL) {
            music_ringbuf = xRingbufferCreateStatic(16384, RINGBUF_TYPE_BYTEBUF, rb_storage, rb_struct);
            ESP_LOGI("SYS", "✅ 音樂郵筒建立成功！(已安全移至外部 PSRAM 📦)");
        } else {
            ESP_LOGE("SYS", "❌ 嚴重錯誤：無法在 PSRAM 分配記憶體給 Music RingBuffer！");
        }
    }
	if (fft_ringbuf == NULL) {
        fft_ringbuf = xRingbufferCreate(8192, RINGBUF_TYPE_BYTEBUF);    // 👈 新增：FFT 收集水庫
        if (fft_ringbuf != NULL) {
            ESP_LOGI("SYS", "✅ FFT 旁路郵筒建立成功！");
        }
    }
	if (hfp_tx_ringbuf ==NULL )
	{
		hfp_tx_ringbuf = xRingbufferCreate(2048, RINGBUF_TYPE_BYTEBUF);
		if (hfp_tx_ringbuf != NULL) {
            ESP_LOGI("SYS", "✅ HFP TX 旁路郵筒建立成功！");
        }
	}
	if (mic_ringbuf != NULL && music_ringbuf != NULL) {
        
        // 1. 啟動收音任務 (綁定 Core 1)
        xTaskCreatePinnedToCore(mic_read_task, "mic_read_task", 4096, NULL, 5, NULL, 1);
        
        // 2. 啟動混音大腦 (綁定 Core 1)
        xTaskCreatePinnedToCore(mixer_task, "mixer_task", 4096, NULL, 5, NULL, 1);
        
        ESP_LOGI("SYS", "🎧 音訊雙任務已成功綁定至 Core 1！");
    } else {
        ESP_LOGE("SYS", "❌ 郵筒未建立，無法啟動音訊任務！");
    }
	// 原本：xTaskCreatePinnedToCore(fft_task, ... NULL);
    // ✅ 改成：把最後一個參數帶入 &fft_task_handle 存下來
    if (fft_ringbuf != NULL) {
        xTaskCreatePinnedToCore(fft_task, "fft_task", 8192, NULL, 2, &fft_task_handle, 1); 
    }
	// 原本：xTaskCreatePinnedToCore(sys_ctrl_task, ... NULL);
    // ✅ 改成：把最後一個參數帶入 &sys_ctrl_task_handle 存下來
    xTaskCreatePinnedToCore(sys_ctrl_task, "sys_ctrl_task", 4096, NULL, 2, &sys_ctrl_task_handle, 0);
	
    //xTaskCreate(passthrough_task, "passthrough_task", 4096, NULL, 5, NULL);
	xTaskCreatePinnedToCore(scene_detect_task, "scene_task", 4096, NULL, 2, NULL, 0);
	xTaskCreate(ble_heartbeat_task, "ble_hb", 2048, NULL, 5, NULL);
    uart_driver_install(UART_NUM, 2048, 0, 0, NULL, 0);
	//xTaskCreate(mic_task, "mic_task", 4096, NULL, 5, NULL);
	
	//xTaskCreatePinnedToCore(audiometry_task, "audiometry_task", 4096, NULL, 2, NULL, 0);
    xTaskCreatePinnedToCore(uart_shell_task, "shell", 4096, NULL, 3, NULL, 0);
    adc_init();
    xTaskCreatePinnedToCore(button_task, "button_task", 4096, NULL, 3, NULL, 0);
	TimerHandle_t hp_timer = xTimerCreate("hp_timer",
											  pdMS_TO_TICKS(300),
											  pdTRUE,   // 自動重複
											  NULL,
											  hp_timer_callback);

    xTimerStart(hp_timer, 0);
	play_system_boot_sound();
    ESP_LOGI(TAG, "READY. type: read/write/scan");
    
}