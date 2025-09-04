# 云原生运行时端到端样例

本样例演示了完整的云原生运行时系统，包括部署、监控、测试和验证。

## 快速开始

### 1. 环境准备

```bash
# 安装必要工具
brew install kubectl helm docker kind
# 或者使用包管理器
sudo apt-get install kubectl helm docker.io

# 启动本地Kubernetes集群
kind create cluster --name formal-framework
```

### 2. 部署应用

```bash
# 克隆样例代码
git clone <repository-url>
cd cloud-native-runtime

# 部署基础组件
kubectl apply -f k8s/namespace.yaml
kubectl apply -f k8s/storage.yaml
kubectl apply -f k8s/monitoring.yaml

# 部署应用
kubectl apply -f k8s/application.yaml
```

### 3. 验证部署

```bash
# 检查Pod状态
kubectl get pods -n formal-framework

# 检查服务状态
kubectl get svc -n formal-framework

# 检查监控状态
kubectl get pods -n monitoring
```

## 架构说明

### 组件架构

```text
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Load Balancer │    │   Ingress       │    │   Application   │
│                 │    │   Controller    │    │   Pods          │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         └───────────────────────┼───────────────────────┘
                                 │
                    ┌─────────────────┐
                    │   Monitoring    │
                    │   Stack         │
                    └─────────────────┘
```

### 技术栈

- **容器运行时**: containerd
- **编排平台**: Kubernetes
- **服务网格**: Istio (可选)
- **监控**: Prometheus + Grafana
- **日志**: Fluentd + Elasticsearch
- **追踪**: Jaeger

## 部署清单

### 命名空间

```yaml
apiVersion: v1
kind: Namespace
metadata:
  name: formal-framework
  labels:
    name: formal-framework
    purpose: demonstration
```

### 存储配置

```yaml
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: fast-ssd
provisioner: k8s.io/minikube-hostpath
parameters:
  type: pd-ssd
---
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: app-storage
  namespace: formal-framework
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 10Gi
  storageClassName: fast-ssd
```

### 应用部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: sample-app
  namespace: formal-framework
spec:
  replicas: 3
  selector:
    matchLabels:
      app: sample-app
  template:
    metadata:
      labels:
        app: sample-app
    spec:
      containers:
      - name: app
        image: nginx:alpine
        ports:
        - containerPort: 80
        resources:
          requests:
            memory: "64Mi"
            cpu: "250m"
          limits:
            memory: "128Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /
            port: 80
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /
            port: 80
          initialDelaySeconds: 5
          periodSeconds: 5
        volumeMounts:
        - name: app-storage
          mountPath: /app/data
      volumes:
      - name: app-storage
        persistentVolumeClaim:
          claimName: app-storage
```

## 监控配置

### Prometheus 配置

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: prometheus-config
  namespace: monitoring
data:
  prometheus.yml: |
    global:
      scrape_interval: 15s
    scrape_configs:
    - job_name: 'kubernetes-pods'
      kubernetes_sd_configs:
      - role: pod
      relabel_configs:
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
        action: keep
        regex: true
```

### Grafana Dashboard

```json
{
  "dashboard": {
    "title": "Formal Framework Dashboard",
    "panels": [
      {
        "title": "Pod Status",
        "type": "stat",
        "targets": [
          {
            "expr": "count(kube_pod_status_phase{namespace=\"formal-framework\"}) by (phase)"
          }
        ]
      },
      {
        "title": "CPU Usage",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(container_cpu_usage_seconds_total{namespace=\"formal-framework\"}[5m])"
          }
        ]
      }
    ]
  }
}
```

## 测试验证

### 1. 功能测试

```bash
# 测试应用访问
curl http://localhost:30080

# 测试健康检查
curl http://localhost:30080/health

# 测试API端点
curl http://localhost:30080/api/v1/status
```

### 2. 性能测试

```bash
# 使用k6进行负载测试
k6 run k6/load-test.js

# 使用ab进行压力测试
ab -n 1000 -c 10 http://localhost:30080/
```

### 3. 监控验证

```bash
# 检查Prometheus指标
curl http://localhost:30090/api/v1/query?query=up

# 检查Grafana访问
open http://localhost:30000
```

## 故障排除

### 常见问题

1. **Pod启动失败**

   ```bash
   kubectl describe pod <pod-name> -n formal-framework
   kubectl logs <pod-name> -n formal-framework
   ```

2. **服务无法访问**

   ```bash
   kubectl get endpoints -n formal-framework
   kubectl get svc -n formal-framework
   ```

3. **监控数据缺失**

   ```bash
   kubectl get pods -n monitoring
   kubectl logs <prometheus-pod> -n monitoring
   ```

### 调试技巧

1. **启用详细日志**

   ```bash
   kubectl logs -f <pod-name> -n formal-framework
   ```

2. **进入容器调试**

   ```bash
   kubectl exec -it <pod-name> -n formal-framework -- /bin/sh
   ```

3. **检查资源使用**

   ```bash
   kubectl top pods -n formal-framework
   kubectl top nodes
   ```

## 扩展配置

### 自动扩缩容

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: sample-app-hpa
  namespace: formal-framework
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: sample-app
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
```

### 网络策略

```yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: sample-app-network-policy
  namespace: formal-framework
spec:
  podSelector:
    matchLabels:
      app: sample-app
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: formal-framework
    ports:
    - protocol: TCP
      port: 80
```

## 最佳实践

### 1. 资源管理

- 设置合理的资源请求和限制
- 使用HPA自动扩缩容
- 监控资源使用情况

### 2. 安全配置

- 使用RBAC控制访问权限
- 配置网络策略隔离流量
- 定期更新镜像版本

### 3. 监控告警

- 设置关键指标告警
- 配置告警通知机制
- 定期检查监控覆盖

### 4. 备份恢复

- 定期备份配置和数据
- 测试恢复流程
- 文档化操作步骤

## 相关资源

- [Kubernetes官方文档](https://kubernetes.io/docs/)
- [Prometheus官方文档](https://prometheus.io/docs/)
- [Grafana官方文档](https://grafana.com/docs/)
- [Istio官方文档](https://istio.io/docs/)
