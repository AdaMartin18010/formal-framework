---
id: evidence:CN-API-KONG
title: API 网关流量治理（Kong）案例
version: V1.0
status: final
category: 应用
source: Kong Gateway 官方文档
credibility: A
---

## 1. 基本信息

- **分类**：应用
- **来源**：Kong Gateway 官方文档
- **可信度**：A（广泛采用的 API 网关）
- **版本**：Kong 3.x
- **发布日期**：2023

## 2. 摘要

Kong 提供 API 网关能力：路由、认证鉴权（JWT/OAuth2）、限流、熔断、监控。本证据条目支撑云原生行业模型中的 API 网关案例（案例六），与 L3_D01 交互、L3_D04 流量控制对齐。

## 3. 对齐维度

### 3.1 术语对齐

- **Route / Service** ↔ `L3_D01_交互标准模型.md` 网关路由
- **Plugin / Policy** ↔ `L3_D01_交互标准模型.md` 安全策略
- **RateLimit / CircuitBreaker** ↔ `L3_D04_运行时标准模型.md` 流量控制
- **Auth / JWT** ↔ `L3_D01_交互标准模型.md` 认证授权

### 3.2 结构/接口对齐

- Kong 路由、插件、流量策略与 L3_D01、L3_D04 对齐

### 3.3 约束/不变式对齐

- 路由优先级、认证前置、限流阈值、熔断条件

### 3.4 度量/指标对齐

- 延迟、错误率、限流有效性、可用性

## 4. 映射

- **L2**：L2_D01 交互、L2_D04 运行时
- **L3**：L3_D01 交互标准模型、L3_D04 运行时标准模型
- **L4**：L4_D90_CN、industry-model/cloud-native-architecture README 案例六

## 5. 引用

- **Kong 文档**：<https://docs.konghq.com/>

## 6. 评审

- **结论**：通过
- **备注**：与云原生 README 案例六引用一致
