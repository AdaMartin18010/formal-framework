---
id: evidence:CN-API-ENVOY
title: API 网关与代理（Envoy）案例
version: V1.0
status: final
category: 应用
source: Envoy 官方文档
credibility: A
---

## 1. 基本信息

- **分类**：应用
- **来源**：Envoy Proxy 官方文档（CNCF）
- **可信度**：A（CNCF 项目，Istio 数据平面）
- **版本**：Envoy 当前
- **发布日期**：2023

## 2. 摘要

Envoy 为高性能代理，支撑 API 网关、服务网格数据平面：路由、负载均衡、熔断、观测。本证据条目支撑云原生行业模型中的 API 网关案例（案例六），与 L3_D01、L3_D04 对齐。

## 3. 对齐维度

### 3.1 术语对齐

- **Route / Cluster** ↔ `L3_D01_交互标准模型.md` 网关路由
- **Filter / Policy** ↔ `L3_D01_交互标准模型.md` 安全与策略
- **CircuitBreaker / Retry** ↔ `L3_D04_运行时标准模型.md` 流量控制
- **Tracing / Metrics** ↔ `L3_D06_监控标准模型.md` 可观测性

### 3.2 结构/接口对齐

- Envoy 配置与 L3_D01、L3_D04、L3_D06 接口对齐

### 3.3 约束/不变式对齐

- 路由匹配、超时、重试、熔断

### 3.4 度量/指标对齐

- 延迟、错误率、可用性

## 4. 映射

- **L2**：L2_D01 交互、L2_D04 运行时、L2_D06 监控
- **L3**：L3_D01 交互标准模型、L3_D04 运行时标准模型、L3_D06 监控标准模型
- **L4**：L4_D90_CN、industry-model/cloud-native-architecture README 案例六

## 5. 引用

- **Envoy 文档**：<https://www.envoyproxy.io/docs/>

## 6. 评审

- **结论**：通过
- **备注**：与云原生 README 案例六引用一致
