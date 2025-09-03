---
id: L4_D90_CN_IDX_V0.1
title: 云原生行业索引与对标（CNCF）
level: L4
domain: D90
model: CN-INDEX
version: V0.1
status: draft
---

## 目录

## 1. 范围与对象

- 核心对象：Kubernetes, Istio, Prometheus, Knative, ArgoCD

## 2. 对标来源

- CNCF Landscape / TOC 指南
- Kubernetes / Istio / Prometheus 官方文档
- NIST SP 800-190, ISO/IEC 27001 相关安全条款（参考）

## 3. 术语对齐（中英）

| 中文 | English | 关联模型 |
| --- | --- | --- |
| Pod | Pod | L3_D04_运行时标准模型 |
| 服务 | Service | L3_D01_交互标准模型 |
| 入口 | Ingress | L3_D01_交互标准模型 |
| 控制器 | Controller | L3_D04_运行时标准模型 |
| 自定义资源 | Custom Resource (CRD) | L2 元模型扩展 |
| 服务网格 | Service Mesh | L3_D04_网络/治理子域 |
| 观测性 | Observability | L3_D06_监控标准模型 |

## 4. 标准/项目映射矩阵（模板）

见 `docs/TEMPLATE_映射矩阵.md`，本行业矩阵草案：

| 领域/能力 | 国际标准/项目 | 本框架模型(Lx_Dyy_Mzz) | 关键术语 | 证据条目 | 备注 |
| --- | --- | --- | --- | --- | --- |
| 容器编排 | Kubernetes | L3_D04_运行时标准模型 | Pod/Service/Ingress | evidence:K8S-001 | 生产验证 |
| 服务网格 | Istio | L3_D04 + L3_D01 | mTLS/Sidecar/Traffic Policy | evidence:ISTIO-001 | 金融生产 |
| 可观测 | Prometheus | L3_D06_监控标准模型 | Metric/Alert/Rule | evidence:PROM-001 | SLO 监控 |
| Serverless | Knative | L3_D04 + L3_D05 | Scale-to-zero/Revisions | evidence:KNA-001 | 弹性实践 |
| GitOps | ArgoCD | L3_D05_部署标准模型 | Desired/Sync/PR Gate | evidence:ARGO-001 | 合规门禁 |

## 5. 成熟案例与证据（模板）

- 请使用 `docs/TEMPLATE_证据条目.md` 填写 evidence:K8S-001, ISTIO-001 ...

## 6. 待补充

- 术语双语表扩充；指标与合规映射；案例证据条目
