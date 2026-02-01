# 云原生行业模型 - 案例库

## 概述

云原生行业模型基于通用形式化建模体系，为云原生应用提供统一的理论基础和工程实践框架。本模型涵盖容器编排、服务网格、API网关、可观测性、Serverless等核心云原生技术要素。

## 目录

- [云原生行业模型 - 案例库](#云原生行业模型---案例库)
  - [概述](#概述)
  - [目录](#目录)
  - [1. 核心业务领域](#1-核心业务领域)
    - [1.1 容器编排 (Container Orchestration)](#11-容器编排-container-orchestration)
    - [1.2 服务网格 (Service Mesh)](#12-服务网格-service-mesh)
    - [1.3 API网关 (API Gateway)](#13-api网关-api-gateway)
    - [1.4 可观测性 (Observability)](#14-可观测性-observability)
    - [1.5 Serverless (无服务器)](#15-serverless-无服务器)
  - [2. 技术架构组件](#2-技术架构组件)
    - [2.1 开源技术栈](#21-开源技术栈)
    - [2.2 云原生架构模式](#22-云原生架构模式)
  - [3. 行业案例库](#3-行业案例库)
    - [案例一：Kubernetes 集群编排（基础）](#案例一kubernetes-集群编排基础)
      - [场景与目标](#场景与目标)
      - [术语与概念对齐](#术语与概念对齐)
      - [结构与约束](#结构与约束)
      - [接口与 DSL 片段](#接口与-dsl-片段)
      - [验证与度量](#验证与度量)
      - [证据与引用](#证据与引用)
  - [案例二：Service Mesh 流量治理（Istio）](#案例二service-mesh-流量治理istio)
    - [场景与目标2](#场景与目标2)
    - [术语与概念对齐2](#术语与概念对齐2)
    - [结构与约束2](#结构与约束2)
    - [接口与 DSL 片段2](#接口与-dsl-片段2)
    - [验证与度量2](#验证与度量2)
    - [证据与引用2](#证据与引用2)
  - [案例三：GitOps 持续交付（ArgoCD）](#案例三gitops-持续交付argocd)
    - [场景与目标3](#场景与目标3)
    - [术语与概念对齐3](#术语与概念对齐3)
    - [结构与约束3](#结构与约束3)
    - [接口与 DSL 片段3](#接口与-dsl-片段3)
    - [验证与度量3](#验证与度量3)
    - [证据与引用3](#证据与引用3)
  - [案例四：可观测性一体化（Prometheus+OTel）](#案例四可观测性一体化prometheusotel)
    - [场景与目标4](#场景与目标4)
    - [术语与概念对齐4](#术语与概念对齐4)
    - [结构与约束4](#结构与约束4)
    - [接口与 DSL 片段4](#接口与-dsl-片段4)
    - [验证与度量4](#验证与度量4)
    - [证据与引用4](#证据与引用4)
  - [案例五：Serverless 函数计算（AWS Lambda/Knative）](#案例五serverless-函数计算aws-lambdaknative)
    - [场景与目标5](#场景与目标5)
    - [术语与概念对齐5](#术语与概念对齐5)
    - [结构与约束5](#结构与约束5)
    - [接口与 DSL 片段5](#接口与-dsl-片段5)
    - [验证与度量5](#验证与度量5)
    - [证据与引用5](#证据与引用5)
  - [案例六：API 网关流量治理（Kong/Envoy）](#案例六api-网关流量治理kongenvoy)
    - [场景与目标6](#场景与目标6)
    - [术语与概念对齐6](#术语与概念对齐6)
    - [结构与约束6](#结构与约束6)
    - [接口与 DSL 片段6](#接口与-dsl-片段6)
    - [验证与度量6](#验证与度量6)
    - [证据与引用6](#证据与引用6)
  - [相关概念](#相关概念)
  - [子模块导航](#子模块导航)
  - [参考文献](#参考文献)

## 1. 核心业务领域

### 1.1 容器编排 (Container Orchestration)

- **工作负载管理**：Pod、Deployment、StatefulSet、DaemonSet
- **服务发现**：Service、Ingress、DNS 解析
- **配置管理**：ConfigMap、Secret、环境变量
- **存储管理**：PV、PVC、StorageClass、CSI 驱动
- **案例与子模块**：→ [案例一：Kubernetes 集群编排](#案例一kubernetes-集群编排基础) | [理论](container-orchestration/theory.md) | [DSL](container-orchestration/dsl-draft.md)

### 1.2 服务网格 (Service Mesh)

- **流量管理**：路由规则、负载均衡、故障注入
- **安全策略**：mTLS、访问控制、策略执行
- **可观测性**：指标收集、链路追踪、日志聚合
- **多集群**：跨集群通信、服务发现、配置同步
- **案例与子模块**：→ [案例二：Service Mesh 流量治理](#案例二service-mesh-流量治理istio) | [理论](service-mesh/theory.md) | [DSL](service-mesh/dsl-draft.md)

### 1.3 API网关 (API Gateway)

- **请求路由**：路径匹配、方法过滤、参数验证
- **认证授权**：JWT、OAuth2、API 密钥管理
- **限流熔断**：速率限制、熔断器、重试策略
- **监控分析**：请求统计、性能分析、错误追踪
- **案例与子模块**：→ [案例六：API 网关流量治理](#案例六api-网关流量治理kongenvoy) | [理论](api-gateway/theory.md) | [DSL](api-gateway/dsl-draft.md)

### 1.4 可观测性 (Observability)

- **指标监控**：Prometheus、Grafana、告警规则
- **日志管理**：ELK Stack、Fluentd、日志聚合
- **链路追踪**：Jaeger、Zipkin、分布式追踪
- **事件管理**：事件驱动、消息队列、工作流
- **案例与子模块**：→ [案例四：可观测性一体化](#案例四可观测性一体化prometheusotel) | [理论](observability/theory.md) | [DSL](observability/dsl-draft.md)

### 1.5 Serverless (无服务器)

- **函数计算**：事件触发、自动扩缩容、按需计费
- **工作流编排**：状态机、条件分支、并行执行
- **事件驱动**：消息队列、事件总线、流处理
- **资源管理**：冷启动优化、内存配置、超时控制
- **案例与子模块**：→ [案例五：Serverless 函数计算](#案例五serverless-函数计算aws-lambdaknative) | [理论](serverless/theory.md) | [DSL](serverless/dsl-draft.md)

## 2. 技术架构组件

### 2.1 开源技术栈

| 组件类型 | 主流技术 | 功能描述 |
|---------|---------|---------|
| 容器编排 | Kubernetes, Docker Swarm | 容器生命周期管理、服务发现 |
| 服务网格 | Istio, Linkerd, Consul Connect | 服务间通信、安全、可观测性 |
| API网关 | Envoy, Kong, Traefik | 流量管理、认证授权、监控 → [案例六](#案例六api-网关流量治理kongenvoy) |
| 可观测性 | Prometheus, Grafana, Jaeger | 指标监控、可视化、链路追踪 |
| 配置管理 | Helm, Kustomize, ArgoCD | 应用配置、版本管理、GitOps → [案例三](#案例三gitops-持续交付argocd) |

### 2.2 云原生架构模式

```yaml
cloud_native_architecture:
  infrastructure_layer:
    - compute: "Kubernetes集群"
    - storage: "分布式存储"
    - network: "CNI网络插件"
  
  platform_layer:
    - service_mesh: "Istio/Linkerd"
    - api_gateway: "Envoy/Kong"
    - ingress_controller: "Nginx/HAProxy"
  
  application_layer:
    - microservices: "容器化应用"
    - serverless: "函数计算"
    - batch_jobs: "批处理任务"
  
  observability_layer:
    - metrics: "Prometheus"
    - logging: "ELK Stack"
    - tracing: "Jaeger/Zipkin"
```

## 3. 行业案例库

### 案例一：Kubernetes 集群编排（基础）

#### 场景与目标

- **业务场景**：微服务应用部署，支持多环境、多版本管理
- **技术目标**：实现容器编排、服务发现、负载均衡、健康检查
- **质量目标**：高可用性 > 99.9%，零停机部署，自动故障恢复

#### 术语与概念对齐

- **Pod/Deployment** ↔ [L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md) 容器编排
- **Service/Ingress** ↔ [L3_D01_交互标准模型](../../L3_D01_交互标准模型.md) 服务暴露
- **ConfigMap/Secret** ↔ [L3_D05_部署标准模型](../../L3_D05_部署标准模型.md) 配置管理
- **PV/PVC** ↔ [L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md) 存储管理

#### 结构与约束

- **工作负载约束**：Pod资源限制、健康检查、重启策略
- **服务约束**：服务发现、负载均衡、网络策略
- **存储约束**：持久化存储、访问模式、回收策略

#### 接口与 DSL 片段

```yaml
kubernetes_cluster:
  namespace: "production"
  
  deployments:
    - name: "user-service"
      replicas: 3
      image: "user-service:v1.2.0"
      resources:
        requests:
          cpu: "100m"
          memory: "256Mi"
        limits:
          cpu: "500m"
          memory: "512Mi"
      
      health_checks:
        liveness:
          path: "/health"
          initial_delay: 30
          period: 10
        readiness:
          path: "/ready"
          initial_delay: 5
          period: 5
  
  services:
    - name: "user-service"
      type: "ClusterIP"
      ports:
        - port: 80
          target_port: 8080
      selector:
        app: "user-service"
  
  ingress:
    - name: "user-ingress"
      host: "api.company.com"
      paths:
        - path: "/users"
          service: "user-service"
          port: 80
```

#### 验证与度量

- **可用性指标**：服务可用性 > 99.9%，Pod重启次数 < 5次/天
- **健康检查**：健康检查成功率 > 99.5%，响应时间 < 1s
- **资源配额**：CPU利用率 60-80%，内存利用率 70-85%
- **部署成功率**：部署成功率 > 95%，回滚时间 < 2分钟

#### 证据与引用

- **evidence:CN-K8S-BASE**：Kubernetes官方文档
- **交叉链接**：[运行时建模理论](../../formal-model/runtime-model/theory.md)、[编排建模理论](../../formal-model/runtime-model/orchestration/theory.md)
- **标准对齐**：[L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md)

## 案例二：Service Mesh 流量治理（Istio）

### 场景与目标2

- **业务场景**：微服务间通信治理，支持蓝绿部署、金丝雀发布、流量管理
- **技术目标**：实现服务间安全通信、流量路由、故障隔离、可观测性
- **质量目标**：服务可用性 > 99.9%，零停机部署，自动故障恢复

### 术语与概念对齐2

- **VirtualService/DestinationRule** ↔ [L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md) 服务网格
- **Gateway/Ingress** ↔ [L3_D01_交互标准模型](../../L3_D01_交互标准模型.md) 网关路由
- **PeerAuthentication** ↔ [L3_D01_交互标准模型](../../L3_D01_交互标准模型.md) 安全认证
- **AuthorizationPolicy** ↔ [L3_D01_交互标准模型](../../L3_D01_交互标准模型.md) 访问控制

### 结构与约束2

- **流量管理约束**：路由规则一致性、负载均衡策略、超时配置
- **安全策略约束**：mTLS强制、证书管理、访问控制规则
- **可观测性约束**：指标收集、链路追踪、日志聚合

### 接口与 DSL 片段2

```yaml
service_mesh:
  virtual_services:
    - name: "user-service-vs"
      hosts: ["user-service"]
      http:
        - match:
            - headers:
                canary:
                  exact: "true"
          route:
            - destination:
                host: "user-service"
                subset: "v2"
              weight: 100
        - route:
            - destination:
                host: "user-service"
                subset: "v1"
              weight: 90
            - destination:
                host: "user-service"
                subset: "v2"
              weight: 10
  
  destination_rules:
    - name: "user-service-dr"
      host: "user-service"
      traffic_policy:
        connection_pool:
          tcp:
            max_connections: 100
          http:
            http1_max_pending_requests: 50
            max_requests_per_connection: 10
        circuit_breaker:
          consecutive_errors: 5
          interval: "30s"
          base_ejection_time: "30s"
      subsets:
        - name: "v1"
          labels:
            version: "v1"
        - name: "v2"
          labels:
            version: "v2"
  
  gateways:
    - name: "user-gateway"
      selector:
        istio: "ingressgateway"
      servers:
        - port:
            number: 80
            name: "http"
            protocol: "HTTP"
          hosts: ["api.company.com"]
```

### 验证与度量2

- **错误率SLO**：错误率 < 0.1%，5xx错误 < 0.05%
- **延迟SLO**：P99延迟 < 500ms，P95延迟 < 200ms
- **成功率SLO**：成功率 > 99.9%，可用性 > 99.95%
- **流量切换**：金丝雀发布成功率 > 95%，回滚时间 < 1分钟

### 证据与引用2

- **evidence:CN-ISTIO-TRAFFIC**：Istio官方文档
- **交叉链接**：[运行时建模理论](../../formal-model/runtime-model/theory.md)、[服务网格理论](service-mesh/theory.md)
- **标准对齐**：[L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md)、[L3_D01_交互标准模型](../../L3_D01_交互标准模型.md)

## 案例三：GitOps 持续交付（ArgoCD）

### 场景与目标3

- **业务场景**：基于Git的持续交付，支持多环境部署、自动同步、质量门禁
- **技术目标**：实现GitOps工作流、期望状态管理、自动回滚、质量检查
- **质量目标**：部署成功率 > 95%，同步延迟 < 5分钟，回滚时间 < 2分钟

### 术语与概念对齐3

- **Application/SyncPolicy** ↔ [L3_D05_部署标准模型](../../L3_D05_部署标准模型.md) GitOps 部署
- **HealthCheck/SyncStatus** ↔ [L3_D06_监控标准模型](../../L3_D06_监控标准模型.md) 健康检查
- **QualityGate/PR** ↔ [L3_D09_CICD标准模型](../../L3_D09_CICD标准模型.md) 质量门禁
- **Rollback/History** ↔ [L3_D05_部署标准模型](../../L3_D05_部署标准模型.md) 版本回滚

### 结构与约束3

- **GitOps约束**：期望状态一致性、不可变制品、声明式配置
- **同步约束**：自动同步策略、健康检查、冲突解决
- **质量约束**：门禁检查、PR审批、测试验证

### 接口与 DSL 片段3

```yaml
gitops:
  applications:
    - name: "user-service"
      namespace: "argocd"
      project: "default"
      
      source:
        repo_url: "https://git.company.com/k8s-manifests"
        target_revision: "main"
        path: "apps/user-service"
      
      destination:
        server: "https://kubernetes.default.svc"
        namespace: "production"
      
      sync_policy:
        automated:
          prune: true
          self_heal: true
        sync_options:
          - CreateNamespace=true
          - PrunePropagationPolicy=foreground
          - PruneLast=true
      
      health_checks:
        - type: "Rollout"
          name: "user-service"
        - type: "Service"
          name: "user-service"
      
      sync_windows:
        - kind: "allow"
          schedule: "0 9-17 * * 1-5"
          duration: "8h"
          applications: ["user-service"]
  
  app_projects:
    - name: "production"
      description: "Production applications"
      source_repos:
        - "https://git.company.com/k8s-manifests"
      destinations:
        - namespace: "production"
          server: "https://kubernetes.default.svc"
      cluster_resource_whitelist:
        - group: ""
          kind: "Namespace"
```

### 验证与度量3

- **同步成功率**：应用同步成功率 > 98%，自动修复成功率 > 95%
- **回滚时间**：紧急回滚时间 < 2分钟，正常回滚时间 < 5分钟
- **漂移检测**：配置漂移检测准确率 > 99%，检测延迟 < 1分钟
- **合规性**：GitOps合规性 > 99%，审计日志完整性 100%

### 证据与引用3

- **evidence:CN-ARGO-GITOPS**：ArgoCD官方文档
- **交叉链接**：[部署建模理论](../../formal-model/deployment-model/theory.md)
- **标准对齐**：[L3_D05_部署标准模型](../../L3_D05_部署标准模型.md)、[L3_D09_CICD标准模型](../../L3_D09_CICD标准模型.md)

## 案例四：可观测性一体化（Prometheus+OTel）

### 场景与目标4

- **业务场景**：统一可观测性平台，支持指标监控、链路追踪、日志聚合、智能告警
- **技术目标**：实现OpenTelemetry标准、Prometheus指标、Jaeger追踪、ELK日志
- **质量目标**：监控覆盖率 > 95%，告警准确率 > 90%，MTTR < 15分钟

### 术语与概念对齐4

- **Metric/Alert** ↔ [L3_D06_监控标准模型](../../L3_D06_监控标准模型.md) 指标监控
- **Trace/Span** ↔ [L3_D06_监控标准模型](../../L3_D06_监控标准模型.md) 链路追踪
- **Log/Event** ↔ [L3_D06_监控标准模型](../../L3_D06_监控标准模型.md) 日志管理
- **Dashboard/Visualization** ↔ [L3_D06_监控标准模型](../../L3_D06_监控标准模型.md) 可视化

### 结构与约束4

- **指标约束**：指标命名规范、标签一致性、采样策略
- **追踪约束**：采样率控制、上下文传播、性能影响
- **日志约束**：日志格式标准、存储策略、检索性能

### 接口与 DSL 片段4

```yaml
observability:
  metrics:
    - name: "http_requests_total"
      type: "counter"
      labels: ["method", "status", "endpoint"]
      cardinality_limit: 1000
    
    - name: "http_request_duration_seconds"
      type: "histogram"
      buckets: [0.1, 0.5, 1.0, 2.0, 5.0]
  
  traces:
    - service_name: "user-service"
      sampling_rate: 0.1
      attributes: ["user.id", "request.id"]
  
  logs:
    - format: "json"
      fields: ["timestamp", "level", "message", "trace_id"]
      retention: "30d"
  
  alerts:
    - name: "high_error_rate"
      condition: "rate(http_requests_total{status=~'5..'}[5m]) > 0.1"
      severity: "critical"
      runbook: "https://runbooks.company.com/high-error-rate"
```

### 验证与度量4

- **告警质量**：告警噪声 < 5%，误报率 < 2%
- **SLO覆盖率**：关键服务SLO覆盖率 > 95%
- **追踪采样率**：生产环境采样率 1-10%，开发环境 100%
- **指标基数**：标签基数 < 1000，避免基数爆炸

### 证据与引用4

- **evidence:CN-OBS-OTEL**：OpenTelemetry官方文档
- **交叉链接**：[监控建模理论](../../formal-model/monitoring-model/theory.md)
- **标准对齐**：[L3_D06_监控标准模型](../../L3_D06_监控标准模型.md)

## 案例五：Serverless 函数计算（AWS Lambda/Knative）

### 场景与目标5

- **业务场景**：事件驱动函数计算，支持 HTTP 触发、消息队列、定时任务、对象存储事件
- **技术目标**：实现函数即服务（FaaS）、自动扩缩容、按需计费、冷启动优化
- **质量目标**：冷启动 < 500ms，成功率 > 99.9%，成本按实际调用量计费

### 术语与概念对齐5

- **Function/Handler** ↔ [L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md) 函数计算
- **Trigger/Event** ↔ [L3_D03_功能标准模型](../../L3_D03_功能标准模型.md) 事件驱动
- **Scaling/Concurrency** ↔ [L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md) 弹性伸缩
- **StateMachine/Workflow** ↔ [L3_D03_功能标准模型](../../L3_D03_功能标准模型.md) 工作流编排

### 结构与约束5

- **函数约束**：内存限制、超时配置、并发限制、冷启动阈值
- **事件约束**：触发器类型、过滤条件、重试策略、死信队列
- **扩缩容约束**：最小/最大实例、预留并发、突发容量

### 接口与 DSL 片段5

```yaml
serverless:
  functions:
    - name: "user-auth"
      runtime: "nodejs18.x"
      handler: "index.handler"
      memory: 512
      timeout: 30
      triggers:
        - type: "http"
          path: "/auth/login"
          method: "POST"
        - type: "schedule"
          expression: "rate(5 minutes)"
      scaling:
        min_capacity: 0
        max_capacity: 100
        target_utilization: 70
      permissions:
        - service: "dynamodb"
          actions: ["GetItem", "PutItem"]
          resources: ["arn:aws:dynamodb:*:*:table/users"]
  
  state_machines:
    - name: "order-workflow"
      definition:
        start_at: "ValidateOrder"
        states:
          ValidateOrder:
            type: "task"
            resource: "arn:aws:lambda:region:account:function:ValidateOrder"
            next: "ProcessPayment"
          ProcessPayment:
            type: "task"
            resource: "arn:aws:lambda:region:account:function:ProcessPayment"
            next: "FulfillOrder"
          FulfillOrder:
            type: "task"
            resource: "arn:aws:lambda:region:account:function:FulfillOrder"
            next: "OrderComplete"
          OrderComplete:
            type: "succeed"
```

### 验证与度量5

- **冷启动指标**：P99 冷启动 < 500ms，预热策略有效性
- **成功率**：函数调用成功率 > 99.9%，错误重试率 < 1%
- **成本**：按调用次数与执行时长计费，预留并发成本优化
- **扩展性**：突发扩缩容 < 30s，预留实例预热覆盖率 > 80%

### 证据与引用5

- **evidence:CN-SERVERLESS-LAMBDA**：AWS Lambda 官方文档
- **evidence:CN-SERVERLESS-KNATIVE**：Knative 官方文档
- **交叉链接**：[Serverless 理论](serverless/theory.md)、[Serverless DSL 草案](serverless/dsl-draft.md)
- **标准对齐**：[L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md)、[L3_D03_功能标准模型](../../L3_D03_功能标准模型.md)

## 案例六：API 网关流量治理（Kong/Envoy）

### 场景与目标6

- **业务场景**：统一 API 入口、请求路由、认证鉴权、限流熔断、灰度发布
- **技术目标**：实现 API 网关、JWT/OAuth2 认证、速率限制、熔断器、请求追踪
- **质量目标**：P99 延迟 < 100ms，错误率 < 0.1%，零停机配置更新

### 术语与概念对齐6

- **Route/Service** ↔ [L3_D01_交互标准模型](../../L3_D01_交互标准模型.md) 网关路由
- **Plugin/Policy** ↔ [L3_D01_交互标准模型](../../L3_D01_交互标准模型.md) 安全策略
- **RateLimit/CircuitBreaker** ↔ [L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md) 流量控制
- **Auth/JWT** ↔ [L3_D01_交互标准模型](../../L3_D01_交互标准模型.md) 认证授权

### 结构与约束6

- **路由约束**：匹配优先级、路径规范、方法过滤
- **安全约束**：认证前置、权限最小化、CORS 策略
- **流量约束**：限流阈值、熔断条件、重试策略

### 接口与 DSL 片段6

```yaml
api_gateway:
  name: "user-api-gateway"
  routes:
    - path: "/users/*"
      method: "GET"
      service:
        name: "user-service"
        url: "http://user-service:8080"
      middleware:
        - type: "jwt-auth"
          config:
            claims_required: ["sub", "roles"]
        - type: "rate-limit"
          requests_per_minute: 1000
          burst: 100
    - path: "/auth/login"
      method: "POST"
      service:
        name: "auth-service"
        url: "http://auth-service:8080"
      middleware:
        - type: "cors"
          origins: ["https://app.company.com"]
  
  traffic:
    circuit_breaker:
      failure_threshold: 5
      success_threshold: 2
      timeout: "30s"
    retry:
      attempts: 3
      backoff: "exponential"
  
  monitoring:
    metrics: ["latency", "errors", "requests_total"]
    tracing:
      enabled: true
      sampling_rate: 0.1
```

### 验证与度量6

- **延迟指标**：P99 网关延迟 < 100ms，P95 < 50ms
- **错误率**：5xx 错误率 < 0.1%，认证失败率 < 1%
- **限流有效性**：超限请求拒绝率准确，无漏限流
- **可用性**：网关可用性 > 99.99%，配置热更新零中断

### 证据与引用6

- **evidence:CN-API-KONG**：Kong 官方文档
- **evidence:CN-API-ENVOY**：Envoy 官方文档
- **交叉链接**：[API 网关理论](api-gateway/theory.md)、[API 网关 DSL 草案](api-gateway/dsl-draft.md)
- **标准对齐**：[L3_D01_交互标准模型](../../L3_D01_交互标准模型.md)、[L3_D04_运行时标准模型](../../L3_D04_运行时标准模型.md)

## 相关概念

- [云原生架构理论](theory.md)
- [运行时建模](../../formal-model/runtime-model/theory.md) - 容器、网络、存储、编排
- [功能建模](../../formal-model/functional-model/theory.md) - 工作流、状态机、规则引擎
- [交互建模](../../formal-model/interaction-model/theory.md) - API、消息、协议
- [监控建模](../../formal-model/monitoring-model/theory.md) - 指标、日志、追踪
- [部署建模](../../formal-model/deployment-model/theory.md) - 配置、版本、回滚
- [CI/CD 建模](../../formal-model/cicd-model/theory.md) - 流水线、质量门禁、GitOps

## 子模块导航

| 子模块 | 理论文档 | DSL 草案 |
|--------|----------|----------|
| 容器编排 | [container-orchestration/theory.md](container-orchestration/theory.md) | [container-orchestration/dsl-draft.md](container-orchestration/dsl-draft.md) |
| 服务网格 | [service-mesh/theory.md](service-mesh/theory.md) | [service-mesh/dsl-draft.md](service-mesh/dsl-draft.md) |
| API 网关 | [api-gateway/theory.md](api-gateway/theory.md) | [api-gateway/dsl-draft.md](api-gateway/dsl-draft.md) |
| 可观测性 | [observability/theory.md](observability/theory.md) | [observability/dsl-draft.md](observability/dsl-draft.md) |
| Serverless | [serverless/theory.md](serverless/theory.md) | [serverless/dsl-draft.md](serverless/dsl-draft.md) |

## 参考文献

1. Kubernetes Documentation (2023). "Kubernetes Concepts"
2. Istio Documentation (2023). "Istio Traffic Management"
3. Argo CD Documentation (2023). "Argo CD User Guide"
4. OpenTelemetry Documentation (2023). "OpenTelemetry Specification"
5. AWS Lambda Documentation (2023). "AWS Lambda Developer Guide"
6. Knative Documentation (2023). "Knative Serving"
7. Kong Documentation (2023). "Kong Gateway"
8. Envoy Documentation (2023). "Envoy Proxy"
