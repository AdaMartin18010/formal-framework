---
id: evidence:CN-SERVERLESS-KNATIVE
title: Serverless 函数计算（Knative）案例
version: V1.0
status: final
category: 应用
source: Knative 官方文档
credibility: A
---

## 1. 基本信息

- **分类**：应用
- **来源**：Knative 官方文档（CNCF）
- **可信度**：A（CNCF 项目）
- **版本**：Knative Serving/Eventing 当前
- **发布日期**：2023

## 2. 摘要

Knative 在 Kubernetes 上提供 Serverless 抽象：Scale-to-zero、Revisions、事件驱动。本证据条目支撑云原生行业模型中的 Serverless 案例（案例五），与 L3_D04、L3_D03 对齐。

## 3. 对齐维度

### 3.1 术语对齐

- **Service / Revision** ↔ `L3_D04_运行时标准模型.md` 函数计算与版本
- **Trigger / Event** ↔ `L3_D03_功能标准模型.md` 事件驱动
- **Scaling** ↔ `L3_D04_运行时标准模型.md` 弹性伸缩

### 3.2 结构/接口对齐

- Knative Serving/Eventing 与 L3_D04、L3_D03 接口对齐

### 3.3 约束/不变式对齐

- 最小/最大副本、冷启动、并发

### 3.4 度量/指标对齐

- 冷启动、成功率、扩缩容时间

## 4. 映射

- **L2**：L2_D04 运行时、L2_D03 功能
- **L3**：L3_D04 运行时标准模型、L3_D03 功能标准模型
- **L4**：L4_D90_CN、industry-model/cloud-native-architecture README 案例五

## 5. 引用

- **Knative 文档**：<https://knative.dev/docs/>

## 6. 评审

- **结论**：通过
- **备注**：与云原生 README 案例五引用一致
