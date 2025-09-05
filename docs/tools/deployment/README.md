# 部署工具

## 📋 概述

本目录包含了正式验证框架的部署工具，用于自动化部署、配置管理和环境管理。

## 🛠️ 部署工具分类

### 1. Docker容器化

- [Dockerfile配置](docker/Dockerfile)
- [Docker Compose配置](docker/docker-compose.yml)
- [镜像构建脚本](docker/build.sh)
- [容器运行脚本](docker/run.sh)

### 2. Kubernetes编排

- [部署配置](kubernetes/deployment.yaml)
- [服务配置](kubernetes/service.yaml)
- [配置映射](kubernetes/configmap.yaml)
- [密钥管理](kubernetes/secret.yaml)

### 3. Helm包管理

- [Chart配置](helm/Chart.yaml)
- [模板文件](helm/templates/)
- [值文件](helm/values.yaml)
- [依赖管理](helm/requirements.yaml)

## 🚀 快速开始

### Docker部署

```bash
# 构建镜像
docker build -t formal-framework:latest .

# 运行容器
docker run -d -p 8080:8080 formal-framework:latest

# 使用Docker Compose
docker-compose up -d
```

### Kubernetes部署

```bash
# 部署到Kubernetes
kubectl apply -f kubernetes/

# 检查部署状态
kubectl get pods
kubectl get services

# 查看日志
kubectl logs -f deployment/formal-framework
```

### Helm部署

```bash
# 安装Helm Chart
helm install formal-framework ./helm

# 升级部署
helm upgrade formal-framework ./helm

# 卸载部署
helm uninstall formal-framework
```

## 🔧 部署配置

### Docker配置

```dockerfile
# Dockerfile
FROM node:18-alpine

WORKDIR /app

COPY package*.json ./
RUN npm ci --only=production

COPY . .

EXPOSE 8080

CMD ["npm", "start"]
```

```yaml
# docker-compose.yml
version: '3.8'

services:
  formal-framework:
    build: .
    ports:
      - "8080:8080"
    environment:
      - NODE_ENV=production
    volumes:
      - ./config:/app/config
    depends_on:
      - database
      - redis

  database:
    image: postgres:13
    environment:
      - POSTGRES_DB=formal_framework
      - POSTGRES_USER=admin
      - POSTGRES_PASSWORD=password
    volumes:
      - postgres_data:/var/lib/postgresql/data

  redis:
    image: redis:6-alpine
    volumes:
      - redis_data:/data

volumes:
  postgres_data:
  redis_data:
```

### Kubernetes配置

```yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: formal-framework
spec:
  replicas: 3
  selector:
    matchLabels:
      app: formal-framework
  template:
    metadata:
      labels:
        app: formal-framework
    spec:
      containers:
      - name: formal-framework
        image: formal-framework:latest
        ports:
        - containerPort: 8080
        env:
        - name: NODE_ENV
          value: "production"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
```

```yaml
# service.yaml
apiVersion: v1
kind: Service
metadata:
  name: formal-framework-service
spec:
  selector:
    app: formal-framework
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8080
  type: LoadBalancer
```

### Helm配置

```yaml
# Chart.yaml
apiVersion: v2
name: formal-framework
description: Formal Verification Framework
type: application
version: 1.0.0
appVersion: "1.0.0"
```

```yaml
# values.yaml
replicaCount: 3

image:
  repository: formal-framework
  tag: latest
  pullPolicy: IfNotPresent

service:
  type: LoadBalancer
  port: 80
  targetPort: 8080

resources:
  limits:
    cpu: 500m
    memory: 512Mi
  requests:
    cpu: 250m
    memory: 256Mi

nodeSelector: {}

tolerations: []

affinity: {}
```

## 📋 部署清单

### 环境准备

- [ ] 服务器资源准备
- [ ] 网络配置检查
- [ ] 存储空间准备
- [ ] 安全配置检查

### 应用部署

- [ ] 镜像构建和推送
- [ ] 配置文件准备
- [ ] 数据库初始化
- [ ] 服务启动验证

### 监控配置

- [ ] 监控系统部署
- [ ] 告警规则配置
- [ ] 日志收集配置
- [ ] 性能监控配置

### 安全配置

- [ ] 访问控制配置
- [ ] 数据加密配置
- [ ] 安全扫描配置
- [ ] 合规性检查

## 🔄 部署流程

### 1. 开发环境部署

```bash
# 开发环境部署脚本
#!/bin/bash
set -e

echo "开始开发环境部署..."

# 构建镜像
docker build -t formal-framework:dev .

# 启动服务
docker-compose -f docker-compose.dev.yml up -d

# 等待服务启动
sleep 30

# 验证部署
curl -f http://localhost:8080/health || exit 1

echo "开发环境部署完成！"
```

### 2. 测试环境部署

```bash
# 测试环境部署脚本
#!/bin/bash
set -e

echo "开始测试环境部署..."

# 部署到Kubernetes
kubectl apply -f kubernetes/test/

# 等待部署完成
kubectl wait --for=condition=available --timeout=300s deployment/formal-framework

# 运行测试
kubectl run test-pod --image=formal-framework:test --rm -i --restart=Never -- npm test

echo "测试环境部署完成！"
```

### 3. 生产环境部署

```bash
# 生产环境部署脚本
#!/bin/bash
set -e

echo "开始生产环境部署..."

# 使用Helm部署
helm upgrade --install formal-framework ./helm --values helm/values.prod.yaml

# 等待部署完成
kubectl wait --for=condition=available --timeout=600s deployment/formal-framework

# 验证部署
kubectl get pods
kubectl get services

echo "生产环境部署完成！"
```

## 📊 部署监控

### 部署状态监控

- **部署进度**：实时监控部署进度
- **资源使用**：监控资源使用情况
- **服务状态**：监控服务运行状态
- **错误日志**：监控部署错误

### 性能监控

- **响应时间**：监控服务响应时间
- **吞吐量**：监控服务处理能力
- **错误率**：监控服务错误率
- **资源使用**：监控资源使用效率

## 🔍 故障排除

### 常见问题

1. **部署失败**：检查配置文件和资源
2. **服务不可用**：检查网络和端口配置
3. **性能问题**：检查资源限制和配置
4. **数据问题**：检查数据库连接和配置

### 调试技巧

1. **查看日志**：检查应用和系统日志
2. **检查状态**：检查Pod和Service状态
3. **网络诊断**：检查网络连接和DNS
4. **资源检查**：检查CPU和内存使用

## 📚 学习资源

### 官方文档

- [Docker文档](https://docs.docker.com/)
- [Kubernetes文档](https://kubernetes.io/docs/)
- [Helm文档](https://helm.sh/docs/)

### 最佳实践

- [Docker最佳实践](https://docs.docker.com/develop/dev-best-practices/)
- [Kubernetes最佳实践](https://kubernetes.io/docs/concepts/configuration/overview/)
- [Helm最佳实践](https://helm.sh/docs/chart_best_practices/)

## 🔗 相关文档

- [工具链概览](../README.md)
- [验证脚本](../verification-scripts/README.md)
- [测试框架](../testing-frameworks/README.md)
- [监控工具](../monitoring/README.md)

---

*最后更新：2024-12-19*-
