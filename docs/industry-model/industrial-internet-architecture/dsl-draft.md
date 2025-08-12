# 工业互联网架构DSL草案（顶层）

## 1. 概述

本DSL用于统一描述工业互联网（IIoT）系统的顶层编排，包括工业平台、边云协同、分层控制、协议适配、资产模型、数据管道与安全治理等，可与现有子域DSL（工业平台、边云协同、分层控制、协议适配）协同工作。

## 2. 核心语法定义

### 2.1 资产与模型（AAS/通用抽象）

```yaml
asset_model:
  standard: "AAS"
  assets:
    - id: "asset.cnc_001"
      type: "cnc_machine"
      vendor: "fanuc"
      capabilities: ["spindle", "axis", "tool_mag"]
      metrics: ["spindle_speed", "feed_rate", "alarm"]
    - id: "asset.plc_001"
      type: "plc"
      vendor: "siemens"
      protocols: ["opc_ua"]
```

### 2.2 协议适配与数据采集（统一管道）

```yaml
protocol_adaptation:
  adapters:
    - name: "opcua_adapter"
      protocol: "opc_ua"
      endpoints:
        - url: "opc.tcp://10.0.0.10:4840"; security: "sign_encrypt"
      mapping:
        - node: "ns=2;s=Spindle.Speed"; metric: "spindle_speed"; type: "double"
        - node: "ns=2;s=Feed.Rate"; metric: "feed_rate"; type: "double"
    - name: "modbus_adapter"
      protocol: "modbus_tcp"
      endpoints: [{host: "10.0.0.20", port: 502}]
      mapping:
        - register: 40001; metric: "temperature"; scale: 0.1
```

### 2.3 分层控制（现场/单元/车间/企业）

```yaml
layered_control:
  layers:
    - name: "field"; scope: ["sensor", "actuator"]
    - name: "cell"; scope: ["machine", "robot"]
    - name: "shop"; scope: ["line", "workshop"]
    - name: "enterprise"; scope: ["plant", "enterprise"]
  control_policies:
    - layer: "field"; latency_ms: 5; reliability: "99.99%"
    - layer: "cell"; latency_ms: 20; reliability: "99.9%"
    - layer: "shop"; latency_ms: 100; reliability: "99.5%"
```

### 2.4 边云协同（数据、应用、状态）

```yaml
edge_cloud_collaboration:
  data_sync:
    direction: "edge_to_cloud"
    frequency: "10s"
    filters: [{metric: "alarm", condition: "!= 0"}]
  app_distribution:
    strategy: "canary"
    rollout: {batch_pct: 10, interval_min: 15}
  state_sync:
    conflict: "cloud_wins"
```

### 2.5 工业平台编排（模型/规则/可视化）

```yaml
industrial_platform:
  data_models: ["telemetry", "event", "timeseries"]
  rule_engine:
    rules:
      - name: "spindle_over_speed"
        condition: "spindle_speed > 8000"
        actions: ["notify", "slow_down"]
  dashboards:
    - name: "machine_overview"
      panels: ["spindle_speed", "feed_rate", "alarms"]
```

## 3. 自动化生成示例

```python
# 基于资产与适配映射自动生成OPC UA采集
def generate_opcua_pipeline(asset, mapping):
    return {
        "endpoint": mapping["endpoints"][0],
        "subscriptions": [m for m in mapping["mapping"]]
    }
```

## 4. 验证与测试

```python
class IIoTTopValidator:
    def validate_layers(self, layers):
        assert len(layers) >= 3 and layers[0]["name"] == "field"
```

## 5. 总结

该顶层DSL与子域DSL协同，提供资产抽象、协议适配、分层控制与边云协同的一体化描述，可驱动工业互联网平台的自动化部署与治理。
