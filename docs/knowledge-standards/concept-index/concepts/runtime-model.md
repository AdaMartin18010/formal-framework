# 运行时模型 (Runtime Model) - 概念索引

## 概念基本信息

- **中文名称**: 运行时模型
- **英文名称**: Runtime Model
- **分类**: 建模概念
- **难度等级**: ⭐⭐⭐ (中级)
- **最后更新**: 2025-02

## 定义位置

- **完整定义**: [formal-model/runtime-model/theory.md](../../../formal-model/runtime-model/theory.md)
- **L2 元模型**: [L2_D04 运行时元模型](../../../L2_D04_运行时元模型.md)
- **L3 标准模型**: [L3_D04 运行时标准模型](../../../L3_D04_运行时标准模型.md)

## 前置与相关概念

- **前置知识**: 容器技术、编排 (Orchestration)
- **相关概念**: 容器、编排、网络、存储、[部署模型](./deployment-model.md)、[监控模型](./monitoring-model.md)、[交互模型](./interaction-model.md)

## 应用场景

容器编排、资源管理、运行时环境、服务网格；行业映射见 Kubernetes、Istio、云原生 L4_D90、AI 推理运行时等。

## 自测问句（先写再对）

- 能区分「API 网关的契约设计」与「API 网关的部署与副本数」分别对应哪个模型吗？→ 契约属 [交互模型](./interaction-model.md)/L3_D01，部署与副本属运行时/L3_D04。
- 运行时模型与交互模型的边界是什么？→ 运行时描述**载体与执行环境**（容器、Pod、Service、编排）；交互描述**接口与协议**（OpenAPI、gRPC、消息格式）。详见 [L3_D04](../../../L3_D04_运行时标准模型.md)、[L3_D01](../../../L3_D01_交互标准模型.md)。

## 参见

- [主概念索引](../CONCEPT_INDEX.md)
- [L2↔L3 映射总表](../../../formal-model/alignment-L2-L3-matrix.md)
