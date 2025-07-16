# 运行时模型DSL草案

## 1. 设计目标

- 用统一DSL描述容器、编排、网络、存储等运行时要素。
- 支持自动生成Dockerfile、Kubernetes YAML、Helm Chart等主流配置。

## 2. 基本语法结构

```dsl
container web {
  image: "nginx:latest"
  ports: [80, 443]
  env: {
    NGINX_HOST: "localhost"
  }
  resources: {
    cpu: "500m"
    memory: "256Mi"
  }
}

service backend {
  containers: [web, app]
  replicas: 3
  network: {
    expose: 8080
    policy: "ClusterIP"
  }
  storage: {
    mount: "/data"
    size: "10Gi"
    class: "fast-ssd"
  }
}
```

## 3. 关键元素

- container：容器定义
- image/ports/env/resources：镜像、端口、环境变量、资源
- service：服务编排
- replicas：副本数
- network：网络策略
- storage：存储卷定义

## 4. 示例

```dsl
container db {
  image: "postgres:14"
  env: {
    POSTGRES_PASSWORD: "example"
  }
  storage: {
    mount: "/var/lib/postgresql/data"
    size: "20Gi"
  }
}

service database {
  containers: [db]
  network: {
    expose: 5432
    policy: "NodePort"
  }
}
```

## 5. 与主流标准的映射

- 可自动转换为Dockerfile、docker-compose、Kubernetes YAML、Helm Chart等
- 支持与云原生工具链集成

## 6. 递归扩展建议

- 支持多容器编排、服务依赖
- 支持自动扩缩容、健康检查、探针
- 支持网络策略、服务网格、存储策略等高级特性
