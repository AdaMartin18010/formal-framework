# 智能家居架构DSL草案

## 1. 概述

智能家居架构DSL用于统一描述家庭物联网系统：设备互联、场景自动化、隐私安全与权限、语音助手与多模交互、能源与安防等，支持与主流生态（Matter、HomeKit、Alexa、Google Home、Home Assistant）对接。

## 2. 核心语法定义

### 2.1 设备互联（Matter/通用抽象）

```yaml
device_interoperability:
  fabric: "home_fabric_1"
  bridges:
    - name: "matter_bridge"
      protocols: ["matter", "zigbee", "zwave", "ble", "wifi"]
  devices:
    - id: "light.living_main"
      type: "light"
      capabilities: ["on_off", "brightness", "color_temperature"]
      room: "living_room"
      matter:
        endpoint: 1
        clusters: ["OnOff", "LevelControl", "ColorControl"]
    - id: "thermostat.hvac"
      type: "thermostat"
      capabilities: ["mode", "target_temp", "fan"]
      room: "hall"
      matter:
        endpoint: 2
        clusters: ["Thermostat", "FanControl"]
    - id: "lock.front_door"
      type: "lock"
      capabilities: ["lock_control", "pin", "auto_lock"]
      room: "entrance"
```

### 2.2 场景自动化（规则与编排）

```yaml
scenario_automation:
  scenes:
    - name: "good_morning"
      triggers:
        - type: "time"; at: "07:00"
        - type: "voice"; phrase: "早上好"
      conditions:
        - expr: "weekday in [Mon,Tue,Wed,Thu,Fri]"
      actions:
        - device: "blind.bedroom"; set: {position: 70}
        - device: "light.living_main"; set: {on: true, brightness: 60}
        - device: "thermostat.hvac"; set: {mode: "heat", target_temp: 22}
    - name: "away_mode"
      triggers:
        - type: "geofence"; event: "leave"; radius_m: 200
      actions:
        - group: "all_lights"; set: {off: true}
        - device: "lock.front_door"; set: {lock: true}
        - device: "camera.front"; set: {arm: "away"}
```

### 2.3 隐私与安全（权限、数据与网络）

```yaml
privacy_security:
  access_control:
    roles:
      - name: "owner"; permissions: ["all"]
      - name: "adult"; permissions: ["scene_run", "device_control"]
      - name: "child"; permissions: ["scene_run_limited"]
      - name: "guest"; permissions: ["guest_mode"]
    policies:
      - resource: "lock.front_door"; allow: ["owner", "adult"]
      - resource: "camera.*"; allow: ["owner"]
  data_protection:
    retention:
      camera_video: "7d"
      sensor_history: "90d"
    encryption:
      at_rest: "aes-256"
      in_transit: "tls-1.3"
    exports:
      - target: "cloud_archive"; fields: ["events", "metrics"]; consent: true
  network_security:
    segmentation: ["iot_vlan", "guest_wifi", "home_lan"]
    firewall:
      rules: ["deny_iot_to_lan", "allow_controller_to_iot"]
```

### 2.4 语音助手与多模交互

```yaml
voice_assistant:
  assistants: ["alexa", "google", "xiaomi"]
  intents:
    - name: "turn_on_light"
      utterances: ["打开客厅灯", "turn on living room light"]
      slots: ["room"]
      actions:
        - device: "light.{room}_main"; set: {on: true}
    - name: "set_temp"
      utterances: ["把温度设为{temp}度", "set temperature to {temp}"]
      slots: ["temp:int"]
      actions:
        - device: "thermostat.hvac"; set: {target_temp: "{temp}"}
  tts_prompts:
    - name: "ack_ok"; text: "好的，已为您完成"
```

### 2.5 能源与安防

```yaml
home_services:
  energy:
    meters: ["grid", "solar", "battery"]
    optimization:
      strategy: "time_of_use"
      targets: {self_consumption_pct: 60}
  security:
    arming_profiles:
      - name: "home"; sensors: ["door", "window"]; camera: "disarm"
      - name: "away"; sensors: ["door", "window", "motion"]; camera: "arm"
    notifications:
      - channel: "mobile_push"; severity: ["warn", "critical"]
```

## 3. 自动化生成示例

```python
# 基于时段与价格的能耗自动优化
def optimize_energy(tou_prices, load_forecast):
    cheap_hours = [h for h,p in tou_prices.items() if p < 0.1]
    schedule = {"water_heater": cheap_hours, "ev_charge": cheap_hours[-4:]}
    return schedule
```

## 4. 验证与测试

```python
class SmartHomeDSLValidator:
    def validate_acl(self, acl):
        assert any(r["name"] == "owner" for r in acl["roles"])
```

## 5. 总结

本DSL覆盖智能家居核心域并对接主流生态，支持设备抽象、场景编排、安全治理与语音交互的自动化配置生成。
