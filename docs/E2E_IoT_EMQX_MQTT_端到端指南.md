# 端到端示例：IoT-EMQX-MQTT（L2→L3→行业→证据→校验）

## 1. 目标

- 本地 EMQX + MQTT pub/sub，映射到 L3 运行时/控制调度不变式（连通性、稳定性）并与证据联动。

## 2. 相关文档

- L3：`L3_D04_运行时标准模型.md`、`L3_D07_控制调度标准模型.md`
- 行业：`L4_D92_IOT_行业索引与对标.md`
- 样例：`docs/samples/iot/`
- 证据：`EVIDENCE_IOT-001.md`、`EVIDENCE_IOT-002.md`
- 矩阵：`VERIFICATION_MATRIX.md`

## 3. 步骤

1) 启动 EMQX：`docker compose -f docs/samples/iot/emqx-docker-compose.yml up -d`
2) 订阅：`python docs/samples/iot/mqtt_sub.py`
3) 发布：`python docs/samples/iot/mqtt_pub.py`

## 4. 校验

- 连通性/稳定性：消息到达率与延迟（占位指标）
- 对应不变式：L3_D04 可达性、L3_D07 调度可行性（占位）

## 5. 结果与证据（占位）

- 截图：`images/iot-mqtt-messages.png`
- 指标：到达率≥99%，断连恢复≤30s（占位）
