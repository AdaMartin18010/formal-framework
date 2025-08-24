# 运行时建模DSL草案

## 1. 设计目标

- 用统一DSL描述容器、编排、网络、存储等运行时要素
- 支持自动生成Docker、Kubernetes、Docker Compose等运行时配置
- 支持容器编排、服务发现、负载均衡、存储管理等高级特性

## 2. 基本语法结构

```dsl
runtime "webapp_runtime" {
  description: "Web应用运行时环境"
  version: "1.0.0"
  author: "system"
  
  containers: [
    {
      name: "webapp"
      image: "nginx:1.21"
      ports: [
        { container: 80, host: 8080, protocol: "tcp" }
      ]
      environment: [
        { name: "NODE_ENV", value: "production" }
      ]
      volumes: [
        { source: "./logs", target: "/var/log/nginx", type: "bind" }
      ]
      resources: {
        cpu: { request: "100m", limit: "500m" }
        memory: { request: "128Mi", limit: "512Mi" }
      }
      health_check: {
        type: "http"
        path: "/health"
        port: 80
        interval: 30
        timeout: 5
        retries: 3
      }
    }
  ]
  
  orchestration: {
    platform: "kubernetes"
    namespace: "webapp"
    replicas: 3
    strategy: {
      type: "rolling"
      max_surge: 1
      max_unavailable: 0
    }
    autoscaling: {
      enabled: true
      min_replicas: 1
      max_replicas: 10
      target_cpu_utilization: 70
    }
  }
  
  networking: {
    service_type: "loadbalancer"
    ports: [
      { port: 80, target_port: 80, protocol: "tcp" }
    ]
    ingress: {
      enabled: true
      host: "app.example.com"
      tls: {
        enabled: true
        secret_name: "app-tls"
      }
    }
  }
  
  storage: {
    persistent_volumes: [
      {
        name: "app-data"
        size: "10Gi"
        access_mode: "ReadWriteOnce"
        storage_class: "standard"
        mount_path: "/app/data"
      }
    ]
  }
  
  monitoring: {
    metrics: {
      enabled: true
      port: 9090
      path: "/metrics"
    }
    logging: {
      driver: "json-file"
      options: {
        max_size: "10m"
        max_file: "3"
      }
    }
  }
  
  security: {
    security_context: {
      run_as_user: 1000
      run_as_group: 1000
      read_only_root_filesystem: true
    }
  }
}
```

## 3. 关键元素

- runtime：运行时声明
- description：描述信息
- version：版本号
- author：作者
- containers：容器定义
- orchestration：编排配置
- networking：网络配置
- storage：存储配置
- monitoring：监控配置
- security：安全配置

## 4. 高级用法

### 4.1 微服务运行时

```dsl
runtime "microservices_runtime" {
  description: "微服务运行时环境"
  version: "1.0.0"
  
  services: [
    {
      name: "api-gateway"
      containers: [
        {
          name: "kong"
          image: "kong:2.8"
          ports: [
            { container: 8000, host: 8000, protocol: "tcp" }
          ]
        }
      ]
      replicas: 2
      service_type: "loadbalancer"
    },
    {
      name: "user-service"
      containers: [
        {
          name: "user-api"
          image: "user-service:v1.0.0"
          ports: [
            { container: 8080, host: 8080, protocol: "tcp" }
          ]
        }
      ]
      replicas: 3
      service_type: "clusterip"
    }
  ]
  
  service_mesh: {
    enabled: true
    type: "istio"
    version: "1.15"
  }
  
  networking: {
    ingress: {
      enabled: true
      host: "api.example.com"
      tls: {
        enabled: true
        secret_name: "api-tls"
      }
    }
  }
}
```

### 4.2 高可用运行时

```dsl
runtime "high_availability_runtime" {
  description: "高可用运行时环境"
  version: "1.0.0"
  
  services: [
    {
      name: "webapp"
      containers: [
        {
          name: "webapp"
          image: "webapp:v1.0.0"
          ports: [
            { container: 8080, host: 8080, protocol: "tcp" }
          ]
          health_check: {
            type: "http"
            path: "/health"
            port: 8080
            interval: 10
            timeout: 3
            retries: 3
          }
        }
      ]
      replicas: 5
      service_type: "loadbalancer"
      autoscaling: {
        enabled: true
        min_replicas: 3
        max_replicas: 20
        target_cpu_utilization: 70
      }
      pod_disruption_budget: {
        min_available: 2
      }
    }
  ]
  
  networking: {
    ingress: {
      enabled: true
      host: "app.example.com"
      tls: {
        enabled: true
        secret_name: "app-tls"
      }
    }
  }
  
  monitoring: {
    metrics: {
      enabled: true
      port: 9090
      path: "/metrics"
    }
    alerting: {
      enabled: true
      rules: [
        {
          name: "pod_down"
          condition: "pod_status != running"
          duration: "1m"
          severity: "critical"
        }
      ]
    }
  }
}
```

## 5. 代码生成模板

### 5.1 Docker Compose生成

```yaml
version: '3.8'
services:
  webapp:
    image: nginx:1.21
    ports:
      - "8080:80"
    environment:
      - NODE_ENV=production
    volumes:
      - ./logs:/var/log/nginx
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 512M
        reservations:
          cpus: '0.1'
          memory: 128M
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost/health"]
      interval: 30s
      timeout: 5s
      retries: 3
```

### 5.2 Kubernetes生成

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: webapp
  namespace: webapp
spec:
  replicas: 3
  selector:
    matchLabels:
      app: webapp
  template:
    metadata:
      labels:
        app: webapp
    spec:
      containers:
      - name: webapp
        image: nginx:1.21
        ports:
        - containerPort: 80
        env:
        - name: NODE_ENV
          value: "production"
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 80
          initialDelaySeconds: 30
          periodSeconds: 30
          timeoutSeconds: 5
          failureThreshold: 3
---
apiVersion: v1
kind: Service
metadata:
  name: webapp-service
  namespace: webapp
spec:
  selector:
    app: webapp
  ports:
  - port: 80
    targetPort: 80
    protocol: TCP
  type: LoadBalancer
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - runtime.name
    - runtime.description
    - runtime.version
    - runtime.containers
  
  type_constraints:
    - field: "runtime.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "runtime.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "runtime.containers"
      type: "array"
      min_items: 1
```

### 6.2 运行时验证规则

```yaml
runtime_validation:
  container_consistency:
    - rule: "all container images must be valid"
    - rule: "port mappings must not conflict"
    - rule: "volume mounts must reference defined volumes"
  
  resource_validation:
    - rule: "resource limits must be greater than requests"
    - rule: "resource values must be within platform limits"
    - rule: "health checks must be properly configured"
```

## 7. 最佳实践

### 7.1 运行时设计模式

```dsl
# 简单运行时模式
runtime "simple_runtime" {
  description: "简单运行时配置"
  
  containers: [
    {
      name: "app"
      image: "app:latest"
      ports: [
        { container: 8080, host: 8080, protocol: "tcp" }
      ]
    }
  ]
  
  orchestration: {
    platform: "docker"
  }
}

# 生产运行时模式
runtime "production_runtime" {
  description: "生产运行时配置"
  
  containers: [
    {
      name: "app"
      image: "app:v1.0.0"
      ports: [
        { container: 8080, host: 8080, protocol: "tcp" }
      ]
      health_check: {
        type: "http"
        path: "/health"
        port: 8080
        interval: 30
        timeout: 5
        retries: 3
      }
      resources: {
        cpu: { request: "100m", limit: "500m" }
        memory: { request: "128Mi", limit: "512Mi" }
      }
    }
  ]
  
  orchestration: {
    platform: "kubernetes"
    namespace: "production"
    replicas: 3
    strategy: {
      type: "rolling"
      max_surge: 1
      max_unavailable: 0
    }
  }
  
  networking: {
    service_type: "loadbalancer"
    ingress: {
      enabled: true
      host: "app.example.com"
      tls: {
        enabled: true
        secret_name: "app-tls"
      }
    }
  }
  
  monitoring: {
    metrics: {
      enabled: true
      port: 9090
      path: "/metrics"
    }
    logging: {
      driver: "json-file"
      options: {
        max_size: "10m"
        max_file: "3"
      }
    }
  }
  
  security: {
    security_context: {
      run_as_user: 1000
      run_as_group: 1000
      read_only_root_filesystem: true
    }
  }
}
```

### 7.2 运行时命名规范

```dsl
# 推荐命名模式
runtime "environment_application_runtime" {
  # 环境_应用_运行时
}

runtime "service_type_runtime" {
  # 服务类型_运行时
}

runtime "platform_application_runtime" {
  # 平台_应用_运行时
}
```

## 8. 与主流标准的映射

| DSL元素 | Docker | Kubernetes | Docker Compose | Helm |
|---------|--------|------------|----------------|------|
| runtime | - | - | - | chart |
| containers | container | pod | service | deployment |
| orchestration | swarm | deployment | deploy | - |
| networking | network | service | networks | service |
| storage | volume | pv/pvc | volumes | pvc |

## 9. 工程实践示例

```dsl
# 生产环境Web应用运行时示例
runtime "production_webapp_runtime" {
  description: "生产环境Web应用运行时"
  version: "1.0.0"
  author: "system"
  
  containers: [
    {
      name: "webapp"
      image: "webapp:v1.0.0"
      ports: [
        { container: 8080, host: 8080, protocol: "tcp" }
      ]
      environment: [
        { name: "NODE_ENV", value: "production" },
        { name: "DB_HOST", value: "database" }
      ]
      volumes: [
        { source: "app-data", target: "/app/data", type: "persistent" }
      ]
      resources: {
        cpu: { request: "200m", limit: "1000m" }
        memory: { request: "256Mi", limit: "1Gi" }
      }
      health_check: {
        type: "http"
        path: "/health"
        port: 8080
        interval: 30
        timeout: 5
        retries: 3
      }
    }
  ]
  
  orchestration: {
    platform: "kubernetes"
    namespace: "production"
    replicas: 5
    strategy: {
      type: "rolling"
      max_surge: 1
      max_unavailable: 0
    }
    autoscaling: {
      enabled: true
      min_replicas: 3
      max_replicas: 20
      target_cpu_utilization: 70
    }
  }
  
  networking: {
    service_type: "loadbalancer"
    ports: [
      { port: 80, target_port: 8080, protocol: "tcp" }
    ]
    ingress: {
      enabled: true
      host: "app.example.com"
      tls: {
        enabled: true
        secret_name: "app-tls"
      }
    }
  }
  
  storage: {
    persistent_volumes: [
      {
        name: "app-data"
        size: "50Gi"
        access_mode: "ReadWriteMany"
        storage_class: "fast-ssd"
        mount_path: "/app/data"
      }
    ]
  }
  
  monitoring: {
    metrics: {
      enabled: true
      port: 9090
      path: "/metrics"
    }
    logging: {
      driver: "json-file"
      options: {
        max_size: "50m"
        max_file: "5"
      }
    }
  }
  
  security: {
    security_context: {
      run_as_user: 1000
      run_as_group: 1000
      read_only_root_filesystem: true
    }
  }
}
```

这个DSL设计为运行时建模提供了完整的配置语言，支持从简单的容器部署到复杂的微服务运行时、高可用运行时等各种运行时模式，同时保持了良好的可扩展性和可维护性。
