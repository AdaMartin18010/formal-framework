---
id: evidence:COURSE-ETH-DS
title: ETH Zürich — Distributed Systems 课程
version: V1.0
status: rc
category: 课程
source: ETH Zürich, Department of Computer Science
credibility: A
---

## 1. 基本信息

- **课程名称**：Distributed Systems（分布式系统）
- **机构**：ETH Zürich（苏黎世联邦理工学院）
- **版本/日期**：课程按学期开设；大纲与材料以当学期官网为准。
- **范围**：分布式系统基础与进阶：一致性模型、复制、容错、共识（Paxos/Raft）、分布式事务、时间与时钟、通信与 RPC、分布式存储与 MapReduce 等。
- **与本框架映射**：L3_D10 分布式模式标准模型；L4 各行业（云原生、金融、IoT、Web3）中的分布式与一致性设计。

## 2. 摘要

- 课程中的「一致性」「复制」「容错」「共识」「分布式事务」与本框架 L3_D10 的容错、一致性、负载均衡、服务发现等模式一一对应。
- 关键对齐：Paxos/Raft ↔ L3_D10 共识与一致性；复制与分区 ↔ 数据与运行时模型；RPC/消息 ↔ L3_D01 交互与 L3_D10 通信模式。
- 学习顺序建议：完成 L2 元模型与 L3_D01/L3_D04 后，再学本课程可加深对 L3_D10 及行业案例（如云原生服务网格、Web3 共识）的理解。

## 3. 对齐维度

- **术语对齐**：Consistency ↔ L3_D10 一致性；Fault tolerance ↔ 容错模式；Replication ↔ 复制与高可用；Consensus ↔ 分布式共识。
- **结构/接口**：课程中的系统模型与协议描述可对应本框架 theory.md 与 dsl-draft.md 中的分布式模式形式化片段。
- **约束/不变式**：线性一致性、顺序一致性等可与 L3_D10 的约束与验证小节对照。
- **度量/指标**：可用性、延迟、吞吐与 L3_D06 监控模型及行业 SLA 对应。

## 4. 映射

- **L2**：L2_D04 运行时、L2_D07 控制调度（调度与一致性边界）。
- **L3**：[L3_D10 分布式模式标准模型](../L3_D10_分布式模式标准模型.md)；[L3_D01 交互标准模型](../L3_D01_交互标准模型.md)（通信与协议）。
- **L4**：[L4_D90 云原生](../L4_D90_CN_行业索引与对标.md)、[L4_D94 Web3](../L4_D94_W3_行业索引与对标.md) 等涉及分布式与共识的行业索引。

## 5. 引用

- **原文/官方**：ETH 课程目录与当学期页面（如 [ETHZ D-INFK](https://inf.ethz.ch/) 课程列表）；分布式系统经典教材 *Distributed Systems* (Tanenbaum/van Steen)、*Designing Data-Intensive Applications* (Kleppmann)。
- **版本/日期**：课程按学期更新；本条目核查日期 2025-02。
- **其他参考**：[reference/AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节；[LEARNING_PATHS.md](../LEARNING_PATHS.md) 行业专项·分布式。

## 6. 评审

- 评审人：待定
- 结论：待评审
- 备注：与 Berkeley EECS 219C、CMU 15-414 等课程互补；219C 侧重形式化验证与综合，本课程侧重分布式系统原理，均对应本框架 L2/L3/L4。
