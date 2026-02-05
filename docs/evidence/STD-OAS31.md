---
id: evidence:STD-OAS31
title: OpenAPI Specification 3.1 — API 契约标准
version: V1.0
status: rc
category: 标准
source: OpenAPI Initiative (Linux Foundation)
credibility: A
---

## 1. 基本信息

- **标准/规范**：OpenAPI Specification (OAS) 3.1
- **名称**：OpenAPI Specification 3.1.0（与 JSON Schema 2020-12 对齐）
- **版本/日期**：3.1.0 现行；[发布说明](https://spec.openapis.org/oas/v3.1.0) 2021-02。
- **范围**：REST API 的机器可读描述（端点、请求/响应模式、认证、示例等）；支持 JSON Schema 2020-12，兼容 3.0 核心。
- **与本框架映射**：L3_D01 交互标准模型（API、契约）；[formal-model/interaction-model](../formal-model/interaction-model/theory.md) 中的 API/契约建模。

## 2. 摘要

- OAS 3.1 的「路径」「操作」「模式」「安全方案」与本框架 L3_D01 的 API 端点、请求/响应模式、认证配置一一对应。
- 关键对齐：OpenAPI `paths` ↔ L3_D01 APIEndpointStandard；`components/schemas` ↔ 数据模式；`securitySchemes` ↔ L3_D01 AuthConfig。
- 本框架 L3_D01 中的 RESTEndpoint、OpenAPI 片段可与 OAS 3.1 文档双向转换（设计时契约优先、代码生成或校验）。

## 3. 对齐维度

- **术语对齐**：Path ↔ 路径模式；Operation ↔ 方法+请求/响应；Schema ↔ 请求/响应模式；Security Scheme ↔ 认证/授权配置。
- **结构/接口**：YAML/JSON 描述的 OpenAPI 文档即 L3_D01 交互模型的一种序列化；可导出为 evidence 引用的标准实现。
- **约束/不变式**：OAS 3.1 的必填字段与校验规则可对应 L3_D01 的 formal_spec 约束。
- **度量/指标**：契约覆盖率、与实现一致性（契约测试）对应 L3_D08 测试与验证。

## 4. 映射

- **L2**：L2_D01 交互元模型（协议、消息、契约抽象）。
- **L3**：[L3_D01 交互标准模型](../L3_D01_交互标准模型.md)（REST/GraphQL/gRPC 端点标准；OpenAPI 对应 REST 部分）。
- **L4**：各行业 API 设计（云原生 API 网关、金融 Open Banking API 等）可引用本证据条目。

## 5. 引用

- **原文/官方**：[OAS 3.1.0 Specification](https://spec.openapis.org/oas/v3.1.0)；[OpenAPI Initiative](https://www.openapis.org/)。
- **版本/日期**：3.1.0，2021-02；本条目核查日期 2025-02。
- **其他参考**：[reference/AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 2 节；[L3_D01 交互标准模型](../L3_D01_交互标准模型.md)。

## 6. 评审

- 评审人：待定
- 结论：待评审
- 备注：AsyncAPI 为异步/事件 API 描述，见 [evidence/STD-ASYNCAPI](../STD-ASYNCAPI.md)；与本框架 L3_D01 消息/协议子域对应。
