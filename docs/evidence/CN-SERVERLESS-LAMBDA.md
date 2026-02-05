---
id: evidence:CN-SERVERLESS-LAMBDA
title: Serverless 函数计算（AWS Lambda）案例
version: V1.0
status: final
category: 应用
source: AWS Lambda 官方文档
credibility: A
---

## 1. 基本信息

- **分类**：应用
- **来源**：AWS Lambda Developer Guide
- **可信度**：A（权威云厂商官方文档）
- **版本**：Lambda 当前文档
- **发布日期**：2023

## 2. 摘要

AWS Lambda 为 FaaS 典型实现：事件触发、自动扩缩容、按需计费。本证据条目支撑云原生行业模型中的 Serverless 函数计算案例（案例五），与 L3_D04 运行时、L3_D03 功能（事件/工作流）对齐。

## 3. 对齐维度

### 3.1 术语对齐

- **Function / Handler** ↔ `L3_D04_运行时标准模型.md` 函数计算
- **Trigger / Event** ↔ `L3_D03_功能标准模型.md` 事件驱动
- **Scaling / Concurrency** ↔ `L3_D04_运行时标准模型.md` 弹性伸缩
- **StateMachine / Workflow** ↔ `L3_D03_功能标准模型.md` 工作流编排

### 3.2 结构/接口对齐

- Lambda 函数配置、触发器、扩缩容与 L3_D04、L3_D03 对应接口对齐

### 3.3 约束/不变式对齐

- 内存限制、超时、并发限制、冷启动阈值

### 3.4 度量/指标对齐

- 冷启动、成功率、成本、扩展性

## 4. 映射

- **L2**：L2_D04 运行时、L2_D03 功能
- **L3**：L3_D04 运行时标准模型、L3_D03 功能标准模型
- **L4**：L4_D90_CN、industry-model/cloud-native-architecture README 案例五

## 5. 引用

- **AWS Lambda 开发者指南**：<https://docs.aws.amazon.com/lambda/>

## 6. 评审

- **结论**：通过
- **备注**：与云原生 README 案例五引用一致
