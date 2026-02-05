---
id: evidence:ISTIO-001
title: Istio 服务网格（L4 引用条目）
version: V1.0
status: rc
category: 应用
source: Istio
credibility: A
---

## 1. 基本信息

- **项目**：Istio（服务网格）
- **定位**：CNCF 毕业项目；L4_D90 云原生行业索引核心对标对象；流量治理、mTLS、可观测性。
- **与本框架映射**：L3_D04 运行时（Service Mesh、Sidecar）+ L3_D01 交互（流量策略、虚拟服务）；L4_D90。详细案例见 [CN-ISTIO-TRAFFIC](CN-ISTIO-TRAFFIC.md)；本条目为 L4 映射矩阵与行业 README 中 evidence:ISTIO-001 的统一点。

## 2. 摘要

- Istio 提供 VirtualService、DestinationRule、Gateway、Sidecar 等抽象，与 L3_D04 服务网格子域及 L3_D01 流量策略对应；mTLS、可观测性（指标/追踪）与 L3_D06 监控、L4_D90 可观测性案例对应。

## 3. 对齐维度

- **术语对齐**：VirtualService/DestinationRule ↔ L3 流量与路由；Sidecar ↔ L3_D04 代理/边车；mTLS ↔ L3 安全策略。
- **结构/接口**：Istio API 与 L3_D01 契约、L3_D04 编排/网格对象对应。
- **约束/不变式**：见 [alignment-L2-L3-matrix](../formal-model/alignment-L2-L3-matrix.md) §2.3、§2.1。

## 4. 映射

- **L2**：L2_D01 交互、L2_D04 运行时。
- **L3**：[L3_D01 交互标准模型](../L3_D01_交互标准模型.md)、[L3_D04 运行时标准模型](../L3_D04_运行时标准模型.md)、[L3_D06 监控标准模型](../L3_D06_监控标准模型.md)。
- **L4**：[L4_D90_CN 行业索引与对标](../L4_D90_CN_行业索引与对标.md)；[cloud-native-architecture README](../industry-model/cloud-native-architecture/README.md)。

## 5. 引用

- **原文/官方**：[Istio 官方文档](https://istio.io/latest/docs/)；[CNCF 项目](https://www.cncf.io/projects/istio/)。
- **版本/日期**：以官方最新稳定版为准；本条目核查日期 2025-02。
- **其他参考**：[AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 4 节；[evidence/README](README.md)。

## 6. 评审

- 评审人：待定
- 结论：待评审
- 备注：与 CN-ISTIO-TRAFFIC 区分：ISTIO-001 为 L4 矩阵与行业 README 引用用；CN-ISTIO-TRAFFIC 为流量治理案例详述。
