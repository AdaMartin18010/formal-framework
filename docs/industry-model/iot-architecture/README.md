# 物联网行业模型 - 案例库（骨架占位）

## 案例一：多协议设备接入（MQTT/Modbus）

- 对齐：`L3_D01_交互标准模型.md` 协议 · `L2_D07_控制调度元模型.md`
- 不变式：ProtocolStateConsistency/MutualExclusion
- 交叉链接：`docs/formal-model/interaction-model/protocol/theory.md`
- evidence:IOT-DEVICE-ACCESS

## 案例二：边缘控制与实时调度

- 对齐：`L2_D07_控制调度元模型.md` · `L2_D04_运行时元模型.md`
- 不变式：EDFSchedulability/EventLatencyBound
- 交叉链接：`docs/formal-model/runtime-model/orchestration/theory.md`
- evidence:IOT-EDGE-RT

## 案例三：数据采集与离线回传

- 对齐：`L2_D02_数据元模型.md` 采集 · `L3_D06_监控标准模型.md`
- 不变式：DataIntegrity/LabelCardinalityBound
- 交叉链接：`docs/formal-model/monitoring-model/theory.md`
- evidence:IOT-DATA-COLLECT
