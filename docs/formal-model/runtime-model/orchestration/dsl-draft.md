# 编排建模DSL草案

## 1. 设计目标

- 用统一DSL描述服务、容器分组、调度、扩缩容、健康检查、依赖、工作流、策略控制等编排要素。
- 支持自动生成Kubernetes YAML、Docker Compose、Helm、Argo Workflows、BPMN等配置。
- 覆盖资源调度、服务编排、工作流管理、策略控制、弹性伸缩五大核心组件。

## 2. 基本语法结构

### 2.1 服务编排

```dsl
service backend {
  containers: [web, app]
  replicas: 3
  resources: {
    cpu: "1"
    memory: "1Gi"
  }
  healthcheck: {
    type: http
    path: "/health"
    interval: "10s"
  }
  network: {
    expose: 8080
    policy: "ClusterIP"
  }
  depends_on: [db]
}

service db {
  containers: [db]
  resources: {
    cpu: "2"
    memory: "4Gi"
  }
  healthcheck: {
    type: tcp
    port: 5432
  }
}
```

### 2.2 弹性伸缩与调度

```dsl
scaling backend_hpa {
  service: backend
  strategy: horizontal
  metrics:
    - type: cpu
      target: 70
      scale_up_threshold: 80
      scale_down_threshold: 30
    - type: custom
      name: "requests_per_second"
      target: 1000
  min_replicas: 2
  max_replicas: 10
  cooldown: "60s"
}

scheduling backend_scheduler {
  service: backend
  algorithm: round_robin
  affinity:
    - type: pod_anti_affinity
      weight: 100
  resource_allocation: dynamic
}
```

### 2.3 部署策略

```dsl
deployment backend_deploy {
  service: backend
  strategy: rolling  # blue_green | rolling | canary
  rolling_config:
    max_unavailable: 0
    max_surge: 1
  canary_config:  # 当 strategy: canary 时生效
    initial_traffic: 10
    step: 5
    interval: "5m"
}
```

### 2.4 工作流定义

```dsl
workflow order_process {
  type: sequential
  tasks:
    - name: validate
      type: service
      service: validator
    - name: process
      type: parallel
      branches:
        - service: payment
        - service: inventory
    - name: notify
      type: service
      service: notifier
      depends_on: [process]
}
```

### 2.5 策略控制

```dsl
policy access_policy {
  type: access_control
  rules:
    - allow: ["admin"]
      resources: ["*"]
    - allow: ["user"]
      resources: ["read"]
      
policy resource_policy {
  type: resource
  rules:
    - max_cpu: "4"
      max_memory: "8Gi"
    - scaling_policy: backend_hpa
}
```

## 3. 关键元素

| 类别 | 元素 | 说明 |
|------|------|------|
| 服务编排 | service/containers | 服务与容器分组 |
| | replicas/resources | 副本数与资源 |
| | healthcheck | 健康检查 |
| | network | 网络策略 |
| | depends_on | 依赖关系 |
| 弹性伸缩 | scaling | 扩缩容策略 |
| | metrics | 扩缩容指标 |
| | min/max_replicas | 副本数边界 |
| 调度 | scheduling | 调度策略 |
| | algorithm | 调度算法 |
| | affinity | 亲和性配置 |
| 部署 | deployment | 部署策略 |
| | strategy | 蓝绿/滚动/金丝雀 |
| 工作流 | workflow | 工作流定义 |
| | tasks | 任务节点 |
| 策略 | policy | 策略控制 |
| | rules | 策略规则 |

## 4. 常用编排声明方式一览（表格）

| 语法示例 | 说明 |
|-----------------------------------------------|----------------|
| service backend { ... } | 服务定义 |
| containers: [web, app] | 容器分组 |
| replicas: 3 | 副本数 |
| healthcheck: { ... } | 健康检查 |
| network: { ... } | 网络策略 |
| depends_on: [db] | 依赖关系 |
| scaling backend_hpa { ... } | 弹性伸缩 |
| scheduling backend_scheduler { ... } | 调度策略 |
| deployment backend_deploy { ... } | 部署策略 |
| workflow order_process { ... } | 工作流定义 |
| policy access_policy { ... } | 策略控制 |

## 5. 与主流标准的映射

| DSL 元素 | Kubernetes | Docker Compose | 其他 |
|----------|------------|----------------|------|
| service | Deployment, Service | services | - |
| scaling | HPA, VPA | deploy.replicas | - |
| scheduling | affinity, nodeSelector | placement | - |
| deployment | RollingUpdate, BlueGreen | deploy.update_config | Argo Rollouts |
| workflow | - | - | Argo Workflows, BPMN |
| policy | NetworkPolicy, RBAC | - | OPA, Kyverno |

## 6. 递归扩展建议

- 支持自动扩缩容、调度策略、亲和性
- 支持多服务依赖与网络拓扑
- 支持工作流嵌套与子流程
- 支持策略组合与策略链
- 支持服务发现配置（service_discovery）
- 支持服务网格配置（service_mesh）

## 7. 相关概念

- [编排建模理论](theory.md)
- [容器建模](../container/theory.md)
- [网络建模](../network/theory.md)
- [存储建模](../storage/theory.md)
- [运行时建模](../theory.md)

## 8. 参考文献

1. Kubernetes Documentation (2023). "Kubernetes Concepts - Workloads"
2. Burns, B., & Beda, J. (2019). "Kubernetes: Up and Running"
3. Argo Project (2023). "Argo Workflows Documentation"
4. OMG (2011). "BPMN 2.0 Specification"
5. Open Policy Agent (2023). "OPA Policy Language"
6. Docker Documentation (2023). "Docker Compose"
