---
id: L4_D90_CN_IDX_V0.1
title: 云原生行业索引与对标（CNCF）
level: L4
domain: D90
model: CN-INDEX
version: V0.1
status: draft
---

**本节要点**：（1）云原生核心对象（Kubernetes、Istio、Prometheus、Knative、ArgoCD）与 L3 模型映射；（2）术语对齐与标准/项目映射矩阵；（3）CNCF 认证与 L3 映射；（4）技术栈详细映射（容器编排、服务网格等）。  
**预计阅读时间**：全文约 20–30 分钟；仅读 §1–§4 与映射表约 10 分钟。  
**5 分钟版**：§4 标准/项目映射矩阵 + §4.1 CNCF 认证与 L3 映射表；详见 [templates/TEMPLATE_映射矩阵](templates/TEMPLATE_映射矩阵.md)。

## 本行业 ↔ L2/L3 映射

| 本行业（云原生） | L2 元模型 | L3 标准模型 | 说明 |
| ---------------- | --------- | ----------- | ---- |
| 容器编排、服务网格、Serverless | L2_D04 运行时、L2_D01 交互 | [L3_D04 运行时](L3_D04_运行时标准模型.md)、[L3_D01 交互](L3_D01_交互标准模型.md) | Pod/Service/Ingress、mTLS、Scale-to-zero |
| 部署、GitOps | L2_D05 部署 | [L3_D05 部署](L3_D05_部署标准模型.md)、[L3_D09 CI/CD](L3_D09_CICD标准模型.md) | Argo CD、Desired State |
| 可观测性 | L2_D06 监控 | [L3_D06 监控](L3_D06_监控标准模型.md) | Prometheus、OpenTelemetry |
| 测试、安全 | L2_D08 测试、L2_D05 | L3_D08、L3_D04 安全 | 验证与合规 |

完整对象/属性/不变式对齐见 [L2↔L3 映射总表](formal-model/alignment-L2-L3-matrix.md)；L2 元模型见 [README §3.1](README.md#31-l2元模型快速导航)。

## 目录

- [1. 范围与对象](#1-范围与对象)

## 1. 范围与对象

- 核心对象：Kubernetes, Istio, Prometheus, Knative, ArgoCD

## 2. 对标来源

- CNCF Landscape / TOC 指南
- Kubernetes / Istio / Prometheus 官方文档
- NIST SP 800-190, ISO/IEC 27001 相关安全条款（参考）

**本段检查点**：此处可暂停；建议先能根据「本行业 ↔ L2/L3 映射」表说出至少 3 个云原生对象（如 K8s、Istio、Prometheus）对应的 L3 文档，再继续 §3。自测可参考 [LEARNING_PATHS 云原生专项](LEARNING_PATHS.md#云原生专项) 与 [REVIEW_CHECKLIST](learning/REVIEW_CHECKLIST.md)。

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

见 [templates/TEMPLATE_映射矩阵.md](templates/TEMPLATE_映射矩阵.md)，本行业矩阵草案：

| 领域/能力 | 国际标准/项目 | 本框架模型(Lx_Dyy_Mzz) | 关键术语 | 证据条目 | 备注 |
| --- | --- | --- | --- | --- | --- |
| 容器编排 | Kubernetes | L3_D04_运行时标准模型 | Pod/Service/Ingress | evidence:K8S-001 | 生产验证 |
| 服务网格 | Istio | L3_D04 + L3_D01 | mTLS/Sidecar/Traffic Policy | evidence:ISTIO-001 | 金融生产 |
| 可观测 | Prometheus | L3_D06_监控标准模型 | Metric/Alert/Rule | evidence:PROM-001 | SLO 监控 |
| Serverless | Knative | L3_D04 + L3_D05 | Scale-to-zero/Revisions | evidence:KNA-001 | 弹性实践 |
| GitOps | ArgoCD | L3_D05_部署标准模型 | Desired/Sync/PR Gate | evidence:ARGO-001 | 合规门禁 |

## 4.1 CNCF 认证与 L3 映射（全面覆盖）

完整认证列表与链接见 [AUTHORITY_ALIGNMENT_INDEX 第 4 节](reference/AUTHORITY_ALIGNMENT_INDEX.md#4-云原生与-cncf-资源)。下表为本框架 L3 与 CNCF 认证的映射摘要：

| 认证 | 全称 | 本框架映射 |
| ---- | ---- | ---------- |
| KCNA | Kubernetes and Cloud Native Associate | L4_D90、容器/基础概念 |
| CKA | Certified Kubernetes Administrator | L3_D04 运行时、编排 |
| CKAD | Certified Kubernetes Application Developer | L3_D04、L3_D05 部署 |
| PCA | Prometheus Certified Associate | L3_D06 监控 |
| ICA | Istio Certified Associate | L3_D04+L3_D01 服务网格 |
| CGOA | GitOps Certified Associate | L3_D05 部署、L3_D09 GitOps |
| CAPA | Certified Argo Project Associate | L3_D05、L3_D09 GitOps/Argo |
| OTCA | OpenTelemetry Certified Associate | L3_D06 监控、可观测性 |
| CBA | Certified Backstage Associate | L3_D05 部署、开发者门户 |
| KCA | Kyverno Certified Associate | L3_D04 策略、L3_D05 合规 |
| KCSA | Kubernetes and Cloud Native Security Associate | L3_D04、L4_D90 安全 |
| CNPA | Cloud Native Platform Engineering Associate | L3_D04、L3_D05、L3_D09 平台工程 |
| CNPE | Certified Cloud Native Platform Engineer | L3_D04/D05/D06/D09 综合 |
| CKS | Certified Kubernetes Security Specialist | L3_D04 运行时安全、L4_D90 安全 |

## 4.2 CNCF 课程与 L3 映射

CNCF 提供 30+ 门培训课程（[CNCF Training](https://www.cncf.io/training/courses/)），以下按主题与本框架 L3 标准模型对应，便于「学完某课程可对标本框架哪几节」。

| 课程主题/类型 | 主要 L3 映射 | 说明 |
| -------------- | ------------ | ---- |
| Kubernetes 基础 / 入门 | L3_D04 运行时标准模型 | 容器、Pod、Service、编排概念 |
| Kubernetes 运维 / 管理 | L3_D04、L3_D05 部署 | 集群管理、配置、升级 |
| Istio / 服务网格 | L3_D04、L3_D01 交互 | 流量治理、mTLS、可观测 |
| Prometheus / 监控 | L3_D06 监控标准模型 | 指标、告警、SLO |
| OpenTelemetry / 可观测 | L3_D06 监控 | 追踪、日志、指标一体化 |
| GitOps / Argo CD / Argo Workflows | L3_D05 部署、L3_D09 CI/CD | 期望状态、同步、流水线 |
| Serverless / Knative | L3_D04、L3_D05 | 弹性伸缩、Revision、事件 |
| 平台工程 / Backstage | L3_D05、L3_D09 | 开发者门户、自助能力 |
| 安全 / Kyverno / 策略 | L3_D04 策略、L3_D05 合规 | 策略即代码、准入控制 |

完整课程列表与最新名称以 [CNCF Training](https://www.cncf.io/training/courses/) 为准；认证大纲见 [cncf/curriculum](https://github.com/cncf/curriculum)。与权威索引的对应见 [AUTHORITY_ALIGNMENT_INDEX 第 4 节](reference/AUTHORITY_ALIGNMENT_INDEX.md#4-云原生与-cncf-资源)。

## 5. 成熟案例与证据（模板）

- 请使用 `docs/TEMPLATE_证据条目.md` 填写 evidence:K8S-001, ISTIO-001 ...

## 6. 云原生技术栈详细映射

### 6.1 容器编排技术栈

```yaml
kubernetes_ecosystem:
  core_components:
    - name: "kube-apiserver"
      function: "API网关与认证"
      mapping: "L3_D01_交互标准模型"
      evidence: "K8S-API-001"
      
    - name: "kube-controller-manager"
      function: "控制器管理"
      mapping: "L3_D04_运行时标准模型"
      evidence: "K8S-CTRL-001"
      
    - name: "kube-scheduler"
      function: "调度器"
      mapping: "L3_D07_控制调度标准模型"
      evidence: "K8S-SCHED-001"
      
    - name: "kubelet"
      function: "节点代理"
      mapping: "L3_D04_运行时标准模型"
      evidence: "K8S-NODE-001"
      
  networking:
    - name: "CNI"
      function: "容器网络接口"
      mapping: "L3_D04_网络子域"
      evidence: "K8S-CNI-001"
      
    - name: "Ingress"
      function: "入口控制器"
      mapping: "L3_D01_交互标准模型"
      evidence: "K8S-ING-001"
      
    - name: "Service"
      function: "服务发现"
      mapping: "L3_D01_交互标准模型"
      evidence: "K8S-SVC-001"
```

### 6.2 服务网格技术栈

```yaml
service_mesh_ecosystem:
  istio_components:
    - name: "istiod"
      function: "控制平面"
      mapping: "L3_D04_运行时标准模型"
      evidence: "ISTIO-CTRL-001"
      
    - name: "envoy_proxy"
      function: "数据平面"
      mapping: "L3_D01_交互标准模型"
      evidence: "ISTIO-DATA-001"
      
    - name: "pilot"
      function: "服务发现"
      mapping: "L3_D01_交互标准模型"
      evidence: "ISTIO-PILOT-001"
      
    - name: "citadel"
      function: "安全认证"
      mapping: "L3_D01_契约子域"
      evidence: "ISTIO-CITADEL-001"
      
  traffic_management:
    - name: "VirtualService"
      function: "流量路由"
      mapping: "L3_D01_交互标准模型"
      evidence: "ISTIO-VS-001"
      
    - name: "DestinationRule"
      function: "目标规则"
      mapping: "L3_D01_交互标准模型"
      evidence: "ISTIO-DR-001"
      
    - name: "Gateway"
      function: "网关配置"
      mapping: "L3_D01_交互标准模型"
      evidence: "ISTIO-GW-001"
```

### 6.3 可观测性技术栈

```yaml
observability_ecosystem:
  metrics:
    - name: "prometheus"
      function: "指标收集"
      mapping: "L3_D06_监控标准模型"
      evidence: "PROM-METRICS-001"
      
    - name: "grafana"
      function: "可视化"
      mapping: "L3_D06_监控标准模型"
      evidence: "GRAFANA-DASH-001"
      
  logging:
    - name: "fluentd"
      function: "日志收集"
      mapping: "L3_D06_监控标准模型"
      evidence: "FLUENTD-LOG-001"
      
    - name: "elasticsearch"
      function: "日志存储"
      mapping: "L3_D06_监控标准模型"
      evidence: "ES-LOG-001"
      
  tracing:
    - name: "jaeger"
      function: "链路追踪"
      mapping: "L3_D06_监控标准模型"
      evidence: "JAEGER-TRACE-001"
      
    - name: "opentelemetry"
      function: "遥测标准"
      mapping: "L3_D06_监控标准模型"
      evidence: "OTEL-STD-001"
```

## 7. GitOps 与持续交付

### 7.1 GitOps 工具链

```yaml
gitops_ecosystem:
  deployment:
    - name: "argocd"
      function: "GitOps部署"
      mapping: "L3_D05_部署标准模型"
      evidence: "ARGO-DEPLOY-001"
      
    - name: "flux"
      function: "GitOps控制器"
      mapping: "L3_D05_部署标准模型"
      evidence: "FLUX-CTRL-001"
      
  ci_cd:
    - name: "tekton"
      function: "CI/CD流水线"
      mapping: "L3_D09_CICD标准模型"
      evidence: "TEKTON-PIPELINE-001"
      
    - name: "jenkins"
      function: "持续集成"
      mapping: "L3_D09_CICD标准模型"
      evidence: "JENKINS-CI-001"
      
  package_management:
    - name: "helm"
      function: "包管理"
      mapping: "L3_D05_部署标准模型"
      evidence: "HELM-PKG-001"
      
    - name: "kustomize"
      function: "配置管理"
      mapping: "L3_D05_部署标准模型"
      evidence: "KUSTOMIZE-CFG-001"
```

### 7.2 Serverless 技术栈

```yaml
serverless_ecosystem:
  knative_components:
    - name: "knative_serving"
      function: "无服务器服务"
      mapping: "L3_D04_运行时标准模型"
      evidence: "KNA-SERVING-001"
      
    - name: "knative_eventing"
      function: "事件驱动"
      mapping: "L3_D01_交互标准模型"
      evidence: "KNA-EVENT-001"
      
  serverless_platforms:
    - name: "openfaas"
      function: "函数即服务"
      mapping: "L3_D04_运行时标准模型"
      evidence: "FAAS-FUNC-001"
      
    - name: "kubeless"
      function: "Kubernetes原生FaaS"
      mapping: "L3_D04_运行时标准模型"
      evidence: "KUBELESS-FUNC-001"
```

## 8. 安全与合规

### 8.1 云原生安全

```yaml
security_ecosystem:
  runtime_security:
    - name: "falco"
      function: "运行时安全"
      mapping: "L3_D06_监控标准模型"
      evidence: "FALCO-SEC-001"
      
    - name: "opa"
      function: "策略引擎"
      mapping: "L3_D01_契约子域"
      evidence: "OPA-POLICY-001"
      
  image_security:
    - name: "clair"
      function: "镜像扫描"
      mapping: "L3_D05_部署标准模型"
      evidence: "CLAIR-SCAN-001"
      
    - name: "trivy"
      function: "漏洞检测"
      mapping: "L3_D05_部署标准模型"
      evidence: "TRIVY-VULN-001"
      
  network_security:
    - name: "calico"
      function: "网络策略"
      mapping: "L3_D04_网络子域"
      evidence: "CALICO-NET-001"
      
    - name: "cilium"
      function: "eBPF网络"
      mapping: "L3_D04_网络子域"
      evidence: "CILIUM-EBPF-001"
```

## 9. 存储与数据

### 9.1 云原生存储

```yaml
storage_ecosystem:
  persistent_storage:
    - name: "ceph"
      function: "分布式存储"
      mapping: "L3_D04_存储子域"
      evidence: "CEPH-STOR-001"
      
    - name: "rook"
      function: "存储编排"
      mapping: "L3_D04_存储子域"
      evidence: "ROOK-ORCH-001"
      
  databases:
    - name: "postgresql_operator"
      function: "PostgreSQL管理"
      mapping: "L3_D02_数据标准模型"
      evidence: "PG-OP-001"
      
    - name: "mongodb_operator"
      function: "MongoDB管理"
      mapping: "L3_D02_数据标准模型"
      evidence: "MONGO-OP-001"
      
  data_processing:
    - name: "apache_spark"
      function: "大数据处理"
      mapping: "L3_D04_运行时标准模型"
      evidence: "SPARK-PROC-001"
      
    - name: "kafka"
      function: "消息队列"
      mapping: "L3_D01_消息子域"
      evidence: "KAFKA-MSG-001"
```

## 10. 成熟度评估与最佳实践

### 10.1 云原生成熟度模型

```yaml
maturity_assessment:
  level_1_basic:
    characteristics:
      - "容器化应用"
      - "基础监控"
      - "CI/CD流水线"
    tools: ["Docker", "Kubernetes", "Prometheus"]
    
  level_2_intermediate:
    characteristics:
      - "微服务架构"
      - "服务网格"
      - "GitOps部署"
    tools: ["Istio", "ArgoCD", "Helm"]
    
  level_3_advanced:
    characteristics:
      - "Serverless架构"
      - "多集群管理"
      - "高级可观测性"
    tools: ["Knative", "Rancher", "Jaeger"]
    
  level_4_expert:
    characteristics:
      - "边缘计算"
      - "AI/ML集成"
      - "零信任安全"
    tools: ["K3s", "Kubeflow", "OPA"]
```

### 10.2 实施路线图

```yaml
implementation_roadmap:
  phase_1_foundation:
    duration: "3-6个月"
    goals:
      - "容器化现有应用"
      - "建立Kubernetes集群"
      - "实施基础监控"
    deliverables:
      - "容器化应用清单"
      - "Kubernetes集群"
      - "Prometheus监控"
      
  phase_2_automation:
    duration: "6-12个月"
    goals:
      - "实施CI/CD"
      - "引入服务网格"
      - "建立GitOps流程"
    deliverables:
      - "Jenkins/Tekton流水线"
      - "Istio服务网格"
      - "ArgoCD部署"
      
  phase_3_optimization:
    duration: "12-18个月"
    goals:
      - "优化性能"
      - "增强安全"
      - "提升可观测性"
    deliverables:
      - "性能优化报告"
      - "安全策略"
      - "完整可观测性"
```

## 11. 案例研究与实践

### 11.1 成功案例

- **Netflix**：微服务架构、Chaos Engineering、多区域部署
- **Spotify**：Kubernetes大规模部署、服务网格、GitOps
- **Uber**：多集群管理、边缘计算、实时数据处理

### 11.2 失败教训

- **过度工程化**：过早引入复杂技术栈
- **技能缺口**：团队缺乏云原生技能
- **文化阻力**：传统运维模式阻碍转型

## 12. 未来趋势与创新

### 12.1 技术趋势

- **eBPF技术**：内核级可观测性和安全
- **WebAssembly**：轻量级运行时
- **边缘计算**：K3s、KubeEdge
- **AI/ML集成**：Kubeflow、MLOps

### 12.2 标准化进展

- **CNCF项目**：云原生计算基金会项目
- **OCI标准**：开放容器倡议
- **CNAB规范**：云原生应用包
- **SMI规范**：服务网格接口
