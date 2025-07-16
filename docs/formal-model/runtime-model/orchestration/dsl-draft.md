# 编排建模DSL草案

## 1. 设计目标

- 用统一DSL描述服务、容器分组、调度、扩缩容、健康检查、依赖等编排要素。
- 支持自动生成Kubernetes YAML、Docker Compose、Helm等配置。

## 2. 基本语法结构

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

## 3. 关键元素

- service/containers：服务与容器分组
- replicas/resources：副本数与资源
- healthcheck：健康检查
- network：网络策略
- depends_on：依赖关系

## 4. 常用编排声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| service backend { ... }                       | 服务定义       |
| containers: [web, app]                        | 容器分组       |
| replicas: 3                                   | 副本数         |
| healthcheck: { ... }                          | 健康检查       |
| network: { ... }                              | 网络策略       |
| depends_on: [db]                              | 依赖关系       |

## 5. 与主流标准的映射

- 可自动转换为Kubernetes YAML、Docker Compose、Helm等配置
- 支持与主流容器编排工具集成

## 6. 递归扩展建议

- 支持自动扩缩容、调度策略、亲和性
- 支持多服务依赖与网络拓扑
