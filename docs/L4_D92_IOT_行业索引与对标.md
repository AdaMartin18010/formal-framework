---
id: L4_D92_IOT_IDX_V0.1
title: 物联网行业索引与对标（IoT）
level: L4
domain: D92
model: IOT-INDEX
version: V0.1
status: draft
---

## 目录

## 1. 范围与对象

- 核心对象：KubeEdge, ThingsBoard, EMQX, EdgeX Foundry

## 2. 对标来源

- 项目官方文档、IETF/OMA/LwM2M、工业协议 OPC UA/Modbus（参考）

## 3. 术语对齐（中英）

| 中文 | English | 关联模型 |
| --- | --- | --- |
| 设备 | Device | L3_D02_数据 + L3_D01_交互 |
| 网关 | Gateway | L3_D04_运行时 |
| 遥测 | Telemetry | L3_D06_监控 |
| 指令 | Command | L3_D01_交互/消息 |
| 边缘节点 | Edge Node | L3_D04_运行时 |

## 4. 标准/项目映射矩阵（草案）

| 领域/能力 | 国际标准/项目 | 本框架模型 | 关键术语 | 证据条目 | 备注 |
| --- | --- | --- | --- | --- | --- |
| 设备管理 | ThingsBoard | L3_D02 + L3_D01 | Device/Telemetry/Rule | evidence:IOT-001 | 生产实践 |
| 边缘编排 | KubeEdge | L3_D04 | Edge/Cloud Sync/Autonomy | evidence:IOT-002 | 稳定性 |
| 消息中间件 | EMQX | L3_D01/消息 | MQTT/QoS/Retain | evidence:IOT-003 | 性能 |

## 5. 成熟案例与证据

- 参照 `docs/TEMPLATE_证据条目.md` 填写 evidence:IOT-001..003

## 6. 待补充

- 工业协议映射、边云协同指标
