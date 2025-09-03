---
id: L4_D93_AI_IDX_V0.1
title: AI 基础设施行业索引与对标（AI Infra）
level: L4
domain: D93
model: AI-INDEX
version: V0.1
status: draft
---

## 目录

## 1. 范围与对象

- 核心对象：MLflow, Kubeflow, Feast, TF Serving, Airflow

## 2. 对标来源

- MLOps 开源项目文档、云厂商最佳实践、NIST AI RMF（参考）

## 3. 术语对齐（中英）

| 中文 | English | 关联模型 |
| --- | --- | --- |
| 特征存储 | Feature Store | L3_D02_数据 |
| 模型服务 | Model Serving | L3_D04_运行时 |
| 训练流水线 | Training Pipeline | L3_D09_CICD/流水线 |
| 实验追踪 | Experiment Tracking | L3_D06_监控/度量 |

## 4. 标准/项目映射矩阵（草案）

| 领域/能力 | 国际标准/项目 | 本框架模型 | 关键术语 | 证据条目 | 备注 |
| --- | --- | --- | --- | --- | --- |
| 模型服务 | TF Serving | L3_D04 | Model/Version/Canary | evidence:AI-001 | 性能 |
| 特征存储 | Feast | L3_D02 | Feature/Entity/Consistency | evidence:AI-002 | 一致性 |
| 工作流 | Airflow/Kubeflow | L3_D09 | DAG/Pipeline/Schedule | evidence:AI-003 | 稳定性 |

## 5. 成熟案例与证据

- 参照 `docs/TEMPLATE_证据条目.md` 填写 evidence:AI-001..003

## 6. 待补充

- 模型治理与安全、合规指标
