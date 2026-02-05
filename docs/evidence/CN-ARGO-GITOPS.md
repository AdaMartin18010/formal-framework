---
id: evidence:CN-ARGO-GITOPS
title: Argo CD GitOps 持续交付案例
version: V1.0
status: final
category: 应用
source: Argo CD官方文档
credibility: A
---

## 1. 基本信息

- **分类**：应用
- **来源**：Argo CD 官方文档
- **可信度**：A（权威 CNCF 项目）
- **版本**：Argo CD 2.x
- **发布日期**：2023

## 2. 摘要

Argo CD 是基于 Git 的声明式、GitOps 持续交付工具，实现期望状态与集群状态同步、自动修复、质量门禁与回滚。本证据条目支撑云原生行业模型中的 GitOps 案例（案例三）。

## 3. 对齐维度

### 3.1 术语对齐

- **Application / SyncPolicy** ↔ `L3_D05_部署标准模型.md` GitOps 部署
- **HealthCheck / SyncStatus** ↔ `L3_D06_监控标准模型.md` 健康检查
- **QualityGate / PR** ↔ `L3_D09_CICD标准模型.md` 质量门禁
- **Rollback / History** ↔ `L3_D05_部署标准模型.md` 版本回滚

### 3.2 结构/接口对齐

- GitOps 应用定义 ↔ L3_D05 部署配置
- 同步策略与健康检查 ↔ L3_D06 监控、L3_D09 流水线

### 3.3 约束/不变式对齐

- 期望状态一致性、不可变制品、声明式配置

### 3.4 度量/指标对齐

- 同步成功率、回滚时间、漂移检测、合规性

## 4. 映射

- **L2**：L2_D05 部署元模型、L2_D06 监控元模型
- **L3**：L3_D05 部署标准模型、L3_D06 监控标准模型、L3_D09_CICD标准模型
- **L4**：L4_D90_CN 行业索引、industry-model/cloud-native-architecture README 案例三

## 5. 引用

- **Argo CD 官方文档**：<https://argo-cd.readthedocs.io/>
- **CNCF 项目**：<https://www.cncf.io/projects/argo/>

## 6. 评审

- **结论**：通过
- **备注**：与云原生 README 案例三引用一致
