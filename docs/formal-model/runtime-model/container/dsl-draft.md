# 容器建模DSL草案

## 1. 设计目标

- 用统一DSL描述镜像、资源、环境、生命周期、依赖等容器要素。
- 支持自动生成Dockerfile、docker-compose、K8s Pod等配置。

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
  volumes: ["/data:/data"]
}

container app {
  image: "myapp:v1.0"
  depends_on: [web]
  env: {
    APP_ENV: "production"
  }
}
```

## 3. 关键元素

- container：容器声明
- image/ports/env/resources/volumes：镜像、端口、环境、资源、存储
- depends_on：依赖关系

## 4. 常用容器声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| container web { ... }                         | 容器定义       |
| image: "nginx:latest"                         | 镜像声明       |
| ports: [80, 443]                              | 端口映射       |
| env: { ... }                                  | 环境变量       |
| resources: { cpu: "500m" }                    | 资源限制       |
| volumes: ["/data:/data"]                      | 卷挂载         |
| depends_on: [web]                             | 依赖关系       |

## 5. 与主流标准的映射

- 可自动转换为Dockerfile、docker-compose、K8s Pod等配置
- 支持与主流容器编排工具集成

## 6. 递归扩展建议

- 支持健康检查、生命周期钩子、自动扩缩容
- 支持多容器编排与服务依赖
