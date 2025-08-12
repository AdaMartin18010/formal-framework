# 智能家居 语音助手 DSL 草案

## 1. 概述

该DSL用于统一配置智能家居的语音交互能力，包括意图识别、槽位提取、TTS合成、多模态交互等，支持与Alexa、Google Assistant、小爱同学等主流语音平台对接。

## 2. 核心语法定义

### 2.1 意图与槽位定义

```yaml
intents:
  - name: "turn_on_device"
    utterances:
      - "打开{room}的{device}"
      - "turn on {device} in {room}"
      - "把{room}的{device}打开"
    slots:
      - name: "room"; type: "enum"; values: ["客厅", "卧室", "厨房", "书房"]
      - name: "device"; type: "enum"; values: ["灯", "空调", "电视", "音响"]
    actions:
      - device: "{room}.{device}"; set: {on: true}
      - tts: "好的，已为您打开{room}的{device}"

  - name: "set_temperature"
    utterances:
      - "把温度调到{temp}度"
      - "set temperature to {temp}"
      - "空调温度设为{temp}"
    slots:
      - name: "temp"; type: "number"; range: [16, 30]
    actions:
      - device: "thermostat.hvac"; set: {target_temp: "{temp}"}
      - tts: "温度已设置为{temp}度"

  - name: "scene_activation"
    utterances:
      - "启动{scene}模式"
      - "执行{scene}场景"
      - "activate {scene} scene"
    slots:
      - name: "scene"; type: "enum"; values: ["回家", "离家", "睡眠", "阅读", "娱乐"]
    actions:
      - scene: "{scene}"
      - tts: "已启动{scene}模式"
```

### 2.2 语音合成配置

```yaml
tts_config:
  voices:
    - name: "xiaomei"; gender: "female"; language: "zh-CN"
    - name: "xiaoming"; gender: "male"; language: "zh-CN"
    - name: "alex"; gender: "male"; language: "en-US"
  
  prompts:
    - name: "ack_ok"; text: "好的，已为您完成"
    - name: "ack_error"; text: "抱歉，操作失败，请重试"
    - name: "ack_confirm"; text: "确认要执行此操作吗？"
    - name: "ack_unknown"; text: "抱歉，我没有理解您的指令"
  
  settings:
    speed: 1.0
    pitch: 1.0
    volume: 0.8
    language: "zh-CN"
```

### 2.3 多模态交互

```yaml
multimodal:
  wake_words:
    - "小爱同学"
    - "Hey Google"
    - "Alexa"
  
  visual_feedback:
    - intent: "turn_on_device"
      display: "正在打开{device}..."
      icon: "light_on"
    - intent: "set_temperature"
      display: "温度设置为{temp}°C"
      icon: "thermostat"
  
  gesture_recognition:
    - gesture: "wave_up"; action: "volume_up"
    - gesture: "wave_down"; action: "volume_down"
    - gesture: "point_left"; action: "previous_track"
    - gesture: "point_right"; action: "next_track"
```

### 2.4 上下文管理

```yaml
context_management:
  session_timeout: 30  # seconds
  context_variables:
    - name: "last_room"; type: "string"
    - name: "last_device"; type: "string"
    - name: "user_preference"; type: "object"
  
  follow_up:
    - intent: "turn_on_device"
      follow_ups:
        - "亮度调到{level}%"
        - "颜色改为{color}"
    - intent: "set_temperature"
      follow_ups:
        - "开启制冷模式"
        - "开启制热模式"
```

### 2.5 平台集成

```yaml
platform_integration:
  alexa:
    skill_id: "amzn1.ask.skill.xxx"
    invocation_name: "智能家居"
    endpoint: "https://api.example.com/alexa"
  
  google_assistant:
    project_id: "smart-home-xxx"
    action_name: "智能家居控制"
    endpoint: "https://api.example.com/google"
  
  xiaomi:
    app_id: "miot_xxx"
    token: "xxx"
    endpoint: "https://api.example.com/xiaomi"
```

## 3. 自动化生成示例

```python
# 基于意图定义自动生成语音识别训练数据
def generate_training_data(intents):
    training_data = []
    for intent in intents:
        for utterance in intent["utterances"]:
            training_data.append({
                "text": utterance,
                "intent": intent["name"],
                "slots": extract_slots(utterance)
            })
    return training_data
```

## 4. 验证与测试

```python
class VoiceAssistantValidator:
    def validate_intent(self, intent):
        assert "name" in intent, "intent must have name"
        assert "utterances" in intent, "intent must have utterances"
        assert "actions" in intent, "intent must have actions"
        
    def validate_slots(self, slots):
        for slot in slots:
            assert "name" in slot, "slot must have name"
            assert "type" in slot, "slot must have type"
```

## 5. 总结

本DSL覆盖语音助手的核心功能，支持意图识别、槽位提取、TTS配置、多模态交互与平台集成，可与设备互联、场景自动化模块协同工作，实现完整的语音控制体验。
