# 智能家居 场景自动化 DSL 草案

## 1. 语义

- trigger: 触发事件（时间、地理、设备、语音、传感器）
- condition: 条件表达式（时间窗、日出日落、家中在/离）
- action: 动作（设备/分组/场景/脚本）
- policy: 优先级、并发与冲突解决

## 2. 语法

```yaml
scenes:
  - name: "good_night"
    triggers:
      - type: "time"; at: "23:00"
      - type: "voice"; phrase: "晚安"
    conditions:
      - expr: "presence == 'home'"
      - astro: {after: "sunset"}
    actions:
      - group: "all_lights"; set: {off: true}
      - device: "lock.front_door"; set: {lock: true}
      - device: "thermostat.hvac"; set: {mode: "heat", target_temp: 20}
    policy:
      priority: 5
      concurrency: "sequential"
      conflict: "last_write_wins"
      rate_limit: {window_s: 60, max_runs: 2}

  - name: "arrive_home"
    triggers:
      - type: "geofence"; event: "enter"; radius_m: 150
    conditions:
      - weekday: ["Mon","Tue","Wed","Thu","Fri"]
    actions:
      - device: "light.entrance"; set: {on: true, brightness: 70}
      - scene: "comfort"
    policy:
      priority: 7
      concurrency: "parallel"
```

## 3. 验证

```python
class SceneValidator:
  def validate(self, scene):
    assert scene["policy"]["priority"] in range(0,11)
```
