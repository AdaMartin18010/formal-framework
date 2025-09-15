# 金融行业模型 - 案例库（骨架占位）

## 案例一：支付网关合规模块

- 对齐：`L3_D01_交互标准模型.md` 契约 · `L3_D05_部署标准模型.md` 合规
- 不变式：AuthEnforcement/ImmutableArtifact
- 交叉链接：`docs/formal-model/interaction-model/theory.md`
- evidence:FIN-PAY-GW

## 案例二：交易撮合与一致性

- 对齐：`L3_D10_分布式模式标准模型.md` · `L2_D02_数据元模型.md` 事务
- 不变式：Linearizability/LatencySLA
- 交叉链接：`docs/formal-model/distributed-pattern-model/theory.md`
- evidence:FIN-TRADE-MATCH

## 案例三：风控规则与实时评估

- 对齐：`L2_D03_功能元模型.md` 规则引擎 · `L2_D07_控制调度元模型.md`
- 不变式：DeterministicStateMachine/EventLatencyBound
- 交叉链接：`docs/formal-model/functional-model/rule-engine/theory.md`
- evidence:FIN-RISK-REALTIME
