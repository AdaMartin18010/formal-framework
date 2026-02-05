---
id: evidence:CN-OBS-OTEL
title: 可观测性一体化（Prometheus + OpenTelemetry）案例
version: V1.0
status: final
category: 应用
source: OpenTelemetry / Prometheus 官方文档
credibility: A
---

## 1. 基本信息

- **分类**：应用
- **来源**：OpenTelemetry 规范、Prometheus 官方文档
- **可信度**：A（CNCF 项目 / 事实标准）
- **版本**：OTel 1.x、Prometheus 2.x
- **发布日期**：2023

## 2. 摘要

OpenTelemetry 提供指标、追踪、日志的统一采集与语义；Prometheus 为指标存储与告警的事实标准。本证据条目支撑云原生行业模型中的可观测性一体化案例（案例四）。

## 3. 对齐维度

### 3.1 术语对齐

- **Metric / Alert** ↔ `L3_D06_监控标准模型.md` 指标监控
- **Trace / Span** ↔ `L3_D06_监控标准模型.md` 链路追踪
- **Log / Event** ↔ `L3_D06_监控标准模型.md` 日志管理
- **Dashboard / Visualization** ↔ `L3_D06_监控标准模型.md` 可视化

### 3.2 结构/接口对齐

- OTel API 与 L3_D06 监控模型指标/追踪/日志接口对齐

### 3.3 约束/不变式对齐

- 指标命名规范、标签一致性、采样策略、日志格式标准

### 3.4 度量/指标对齐

- 告警质量、SLO 覆盖率、追踪采样率、指标基数

## 4. 映射

- **L2**：L2_D06 监控元模型
- **L3**：L3_D06 监控标准模型
- **L4**：L4_D90_CN 行业索引、industry-model/cloud-native-architecture README 案例四

## 5. 引用

- **OpenTelemetry**：<https://opentelemetry.io/docs/>
- **Prometheus**：<https://prometheus.io/docs/>

## 6. 评审

- **结论**：通过
- **备注**：与云原生 README 案例四引用一致
