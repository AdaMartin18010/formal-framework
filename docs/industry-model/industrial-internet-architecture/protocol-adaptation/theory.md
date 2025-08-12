# 工业互联网 协议适配 理论说明

## 1 形式化目标

- 统一描述OPC UA/Modbus/Profinet/EtherNet-IP/MQTT等协议的适配与语义映射
- 建立点位→语义指标的强类型映射与单位/缩放规范
- 支持采样/时间戳/时序一致/重放保护的形式化配置

## 2 核心概念

- 端点与会话：安全等级、握手、会话超时
- 点位/寄存器映射：NodeId/Address→metric(type, unit, scale)
- 时间语义：源时间戳/到达时间/时钟同步(PTP/NTP)
- 容错：重连、背压、重试、去抖、重复抑制

## 3 语义映射示例

- OPC UA: ns=2;s=Spindle.Speed → metric(spindle_speed, double, rpm, scale=1)
- Modbus: 40001..40002 → int16×2 → float(temp, °C, scale=0.1)
- Profinet: I/O slot/slotSub → boolean/alarm → event(alarm_code)

## 4 安全与合规

- 传输：TLS/SignEncrypt、证书信任链
- 访问：最小权限、白名单端点
- 审计：读写操作与重要点位变更留痕

## 5 可证明性

1 类型安全：单位/范围/缩放校验
2 时序一致：最大时间偏差Δt与缓冲窗口保证重组
3 丢包容忍：k次重传/滑动窗口/幂等写

---
该模块与边云协同、分层控制配合，共同保证数据/控制链路的正确性与鲁棒性。
