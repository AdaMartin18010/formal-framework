# 故障排除指南

## 概述

本指南提供了正式验证框架常见问题的诊断和解决方案，帮助您快速定位和解决系统问题。

## 快速诊断

### 系统健康检查

```bash
# 检查系统整体状态
curl -f http://localhost:8080/health

# 检查Kubernetes集群状态
kubectl get nodes
kubectl get pods -n formal-framework

# 检查服务状态
kubectl get services -n formal-framework

# 检查部署状态
kubectl get deployments -n formal-framework
```

### 日志查看

```bash
# 查看应用日志
kubectl logs -f deployment/formal-framework-app -n formal-framework

# 查看验证服务日志
kubectl logs -f deployment/formal-framework-verification -n formal-framework

# 查看数据库日志
kubectl logs -f deployment/postgres -n formal-framework

# 查看Redis日志
kubectl logs -f deployment/redis -n formal-framework
```

## 常见问题分类

### 1. 部署问题

#### 问题：Pod启动失败

**症状**：

- Pod状态为CrashLoopBackOff
- Pod状态为Pending
- Pod状态为ImagePullBackOff

**诊断步骤**：

```bash
# 查看Pod详细信息
kubectl describe pod <pod-name> -n formal-framework

# 查看Pod日志
kubectl logs <pod-name> -n formal-framework

# 检查镜像是否存在
docker pull ghcr.io/formal-framework/app:latest
```

**解决方案**：

1. **ImagePullBackOff**

   ```bash
   # 检查镜像仓库访问权限
   kubectl create secret docker-registry ghcr-secret \
     --docker-server=ghcr.io \
     --docker-username=<username> \
     --docker-password=<token> \
     --docker-email=<email> \
     -n formal-framework
   
   # 更新部署配置
   kubectl patch deployment formal-framework-app -n formal-framework -p '{"spec":{"template":{"spec":{"imagePullSecrets":[{"name":"ghcr-secret"}]}}}}'
   ```

2. **CrashLoopBackOff**

   ```bash
   # 检查应用配置
   kubectl get configmap app-config -n formal-framework -o yaml
   
   # 检查环境变量
   kubectl exec -it <pod-name> -n formal-framework -- env
   
   # 检查应用启动日志
   kubectl logs <pod-name> -n formal-framework --previous
   ```

3. **Pending状态**

   ```bash
   # 检查节点资源
   kubectl describe nodes
   
   # 检查存储类
   kubectl get storageclass
   
   # 检查持久卷
   kubectl get pv
   kubectl get pvc -n formal-framework
   ```

#### 问题：服务无法访问

**症状**：

- 服务状态为Pending
- 无法通过服务IP访问
- 负载均衡器无法工作

**诊断步骤**：

```bash
# 检查服务端点
kubectl get endpoints -n formal-framework

# 检查服务选择器
kubectl get service formal-framework-app-service -n formal-framework -o yaml

# 检查Pod标签
kubectl get pods -n formal-framework --show-labels
```

**解决方案**：

```bash
# 修复服务选择器
kubectl patch service formal-framework-app-service -n formal-framework -p '{"spec":{"selector":{"app":"formal-framework-app"}}}'

# 重新创建服务
kubectl delete service formal-framework-app-service -n formal-framework
kubectl apply -f service.yaml
```

### 2. 数据库问题

#### 问题：数据库连接失败

**症状**：

- 应用日志显示数据库连接错误
- 数据库Pod无法启动
- 连接超时

**诊断步骤**：

```bash
# 检查数据库Pod状态
kubectl get pods -l app=postgres -n formal-framework

# 检查数据库服务
kubectl get service postgres -n formal-framework

# 测试数据库连接
kubectl exec -it <postgres-pod> -n formal-framework -- psql -U postgres -d formal_framework
```

**解决方案**：

1. **数据库Pod无法启动**

   ```bash
   # 检查数据库配置
   kubectl describe pod <postgres-pod> -n formal-framework
   
   # 检查存储卷
   kubectl get pvc -n formal-framework
   
   # 重新创建数据库
   kubectl delete deployment postgres -n formal-framework
   kubectl apply -f postgres-deployment.yaml
   ```

2. **连接超时**

   ```bash
   # 检查网络策略
   kubectl get networkpolicy -n formal-framework
   
   # 检查防火墙规则
   kubectl exec -it <app-pod> -n formal-framework -- telnet postgres 5432
   
   # 更新连接字符串
   kubectl patch secret app-secrets -n formal-framework -p '{"data":{"database-url":"<new-connection-string>"}}'
   ```

#### 问题：数据一致性问题

**症状**：

- 数据验证失败
- 数据不一致错误
- 事务回滚

**诊断步骤**：

```bash
# 运行数据一致性检查
python tools/verification-scripts/data-consistency-checker.py \
  --services http://localhost:8080 \
  --database test.db

# 检查数据库日志
kubectl logs -f deployment/postgres -n formal-framework

# 检查应用日志
kubectl logs -f deployment/formal-framework-app -n formal-framework
```

**解决方案**：

```bash
# 运行数据修复脚本
kubectl exec -it <postgres-pod> -n formal-framework -- psql -U postgres -d formal_framework -c "
  UPDATE accounts SET balance = (
    SELECT COALESCE(SUM(amount), 0) 
    FROM transactions 
    WHERE account_id = accounts.id AND status = 'BOOKED'
  );
"

# 重新同步数据
kubectl exec -it <app-pod> -n formal-framework -- python scripts/sync-data.py
```

### 3. 性能问题

#### 问题：响应时间过长

**症状**：

- API响应时间超过阈值
- 用户投诉系统缓慢
- 监控显示高延迟

**诊断步骤**：

```bash
# 检查CPU使用率
kubectl top pods -n formal-framework

# 检查内存使用率
kubectl top pods -n formal-framework --containers

# 检查网络延迟
kubectl exec -it <app-pod> -n formal-framework -- ping postgres

# 运行性能测试
python tools/verification-scripts/performance-validator.py \
  --url http://localhost:8080 \
  --requests 1000 \
  --workers 10
```

**解决方案**：

1. **CPU使用率过高**

   ```bash
   # 增加副本数
   kubectl scale deployment formal-framework-app --replicas=5 -n formal-framework
   
   # 调整资源限制
   kubectl patch deployment formal-framework-app -n formal-framework -p '{
     "spec": {
       "template": {
         "spec": {
           "containers": [{
             "name": "app",
             "resources": {
               "limits": {"cpu": "1000m", "memory": "1Gi"},
               "requests": {"cpu": "500m", "memory": "512Mi"}
             }
           }]
         }
       }
     }
   }'
   ```

2. **内存使用率过高**

   ```bash
   # 检查内存泄漏
   kubectl exec -it <app-pod> -n formal-framework -- python scripts/memory-profiler.py
   
   # 重启应用
   kubectl rollout restart deployment/formal-framework-app -n formal-framework
   
   # 调整JVM参数（如果使用Java）
   kubectl patch deployment formal-framework-app -n formal-framework -p '{
     "spec": {
       "template": {
         "spec": {
           "containers": [{
             "name": "app",
             "env": [{"name": "JAVA_OPTS", "value": "-Xmx1g -Xms512m"}]
           }]
         }
       }
     }
   }'
   ```

3. **数据库性能问题**

   ```bash
   # 检查慢查询
   kubectl exec -it <postgres-pod> -n formal-framework -- psql -U postgres -d formal_framework -c "
     SELECT query, mean_time, calls 
     FROM pg_stat_statements 
     ORDER BY mean_time DESC 
     LIMIT 10;
   "
   
   # 创建索引
   kubectl exec -it <postgres-pod> -n formal-framework -- psql -U postgres -d formal_framework -c "
     CREATE INDEX CONCURRENTLY idx_transactions_account_id 
     ON transactions(account_id);
   "
   
   # 分析表统计信息
   kubectl exec -it <postgres-pod> -n formal-framework -- psql -U postgres -d formal_framework -c "
     ANALYZE;
   "
   ```

#### 问题：高错误率

**症状**：

- 监控显示错误率超过阈值
- 用户报告功能异常
- 日志中出现大量错误

**诊断步骤**：

```bash
# 检查错误日志
kubectl logs -f deployment/formal-framework-app -n formal-framework | grep ERROR

# 检查Prometheus指标
curl http://localhost:9090/api/v1/query?query=rate(http_requests_total{status=~"5.."}[5m])

# 运行健康检查
python tools/verification-scripts/invariant-checker.py \
  --url http://localhost:8080
```

**解决方案**：

```bash
# 检查应用配置
kubectl get configmap app-config -n formal-framework -o yaml

# 检查环境变量
kubectl exec -it <app-pod> -n formal-framework -- env

# 重启应用
kubectl rollout restart deployment/formal-framework-app -n formal-framework

# 回滚到上一个版本
kubectl rollout undo deployment/formal-framework-app -n formal-framework
```

### 4. 监控问题

#### 问题：监控数据缺失

**症状**：

- Grafana面板显示无数据
- Prometheus无法抓取指标
- 告警无法触发

**诊断步骤**：

```bash
# 检查Prometheus状态
kubectl get pods -l app=prometheus -n formal-framework

# 检查Prometheus配置
kubectl get configmap prometheus-config -n formal-framework -o yaml

# 检查目标状态
curl http://localhost:9090/api/v1/targets

# 检查指标端点
curl http://localhost:8080/metrics
```

**解决方案**：

1. **Prometheus无法启动**

   ```bash
   # 检查存储卷
   kubectl get pvc -n formal-framework
   
   # 检查配置文件
   kubectl describe configmap prometheus-config -n formal-framework
   
   # 重新创建Prometheus
   kubectl delete deployment prometheus -n formal-framework
   kubectl apply -f prometheus-deployment.yaml
   ```

2. **指标端点无法访问**

   ```bash
   # 检查网络策略
   kubectl get networkpolicy -n formal-framework
   
   # 检查服务发现
   kubectl get endpoints -n formal-framework
   
   # 更新Prometheus配置
   kubectl patch configmap prometheus-config -n formal-framework -p '{
     "data": {
       "prometheus.yml": "<updated-config>"
     }
   }'
   ```

#### 问题：告警无法触发

**症状**：

- 告警规则配置正确但不触发
- AlertManager无法发送通知
- 告警状态异常

**诊断步骤**：

```bash
# 检查告警规则
curl http://localhost:9090/api/v1/rules

# 检查AlertManager状态
kubectl get pods -l app=alertmanager -n formal-framework

# 检查告警配置
kubectl get configmap alertmanager-config -n formal-framework -o yaml
```

**解决方案**：

```bash
# 重新加载告警规则
kubectl exec -it <prometheus-pod> -n formal-framework -- curl -X POST http://localhost:9090/-/reload

# 检查告警表达式
kubectl exec -it <prometheus-pod> -n formal-framework -- curl "http://localhost:9090/api/v1/query?query=up"

# 重启AlertManager
kubectl rollout restart deployment/alertmanager -n formal-framework
```

### 5. 网络问题

#### 问题：服务间通信失败

**症状**：

- 服务无法相互访问
- 网络超时错误
- DNS解析失败

**诊断步骤**：

```bash
# 检查服务DNS
kubectl exec -it <app-pod> -n formal-framework -- nslookup postgres

# 检查网络连接
kubectl exec -it <app-pod> -n formal-framework -- telnet postgres 5432

# 检查网络策略
kubectl get networkpolicy -n formal-framework
```

**解决方案**：

```bash
# 修复网络策略
kubectl apply -f - <<EOF
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: allow-app-to-db
  namespace: formal-framework
spec:
  podSelector:
    matchLabels:
      app: formal-framework-app
  policyTypes:
  - Egress
  egress:
  - to:
    - podSelector:
        matchLabels:
          app: postgres
    ports:
    - protocol: TCP
      port: 5432
EOF

# 检查防火墙规则
kubectl exec -it <app-pod> -n formal-framework -- iptables -L
```

## 自动化诊断脚本

### 系统诊断脚本

```bash
#!/bin/bash
# system-diagnosis.sh

echo "=== 正式验证框架系统诊断 ==="
echo "开始时间: $(date)"
echo ""

# 检查Kubernetes集群状态
echo "1. 检查Kubernetes集群状态"
kubectl cluster-info
kubectl get nodes
echo ""

# 检查命名空间状态
echo "2. 检查命名空间状态"
kubectl get namespace formal-framework
echo ""

# 检查Pod状态
echo "3. 检查Pod状态"
kubectl get pods -n formal-framework
echo ""

# 检查服务状态
echo "4. 检查服务状态"
kubectl get services -n formal-framework
echo ""

# 检查部署状态
echo "5. 检查部署状态"
kubectl get deployments -n formal-framework
echo ""

# 检查资源使用情况
echo "6. 检查资源使用情况"
kubectl top pods -n formal-framework
echo ""

# 检查存储状态
echo "7. 检查存储状态"
kubectl get pvc -n formal-framework
echo ""

# 检查网络策略
echo "8. 检查网络策略"
kubectl get networkpolicy -n formal-framework
echo ""

# 检查配置映射
echo "9. 检查配置映射"
kubectl get configmaps -n formal-framework
echo ""

# 检查密钥
echo "10. 检查密钥"
kubectl get secrets -n formal-framework
echo ""

echo "=== 诊断完成 ==="
echo "结束时间: $(date)"
```

### 性能诊断脚本

```bash
#!/bin/bash
# performance-diagnosis.sh

echo "=== 性能诊断 ==="
echo "开始时间: $(date)"
echo ""

# 检查CPU使用率
echo "1. 检查CPU使用率"
kubectl top pods -n formal-framework --sort-by=cpu
echo ""

# 检查内存使用率
echo "2. 检查内存使用率"
kubectl top pods -n formal-framework --sort-by=memory
echo ""

# 检查网络延迟
echo "3. 检查网络延迟"
kubectl exec -it $(kubectl get pods -n formal-framework -l app=formal-framework-app -o jsonpath='{.items[0].metadata.name}') -n formal-framework -- ping -c 3 postgres
echo ""

# 检查磁盘使用率
echo "4. 检查磁盘使用率"
kubectl exec -it $(kubectl get pods -n formal-framework -l app=postgres -o jsonpath='{.items[0].metadata.name}') -n formal-framework -- df -h
echo ""

# 检查数据库连接数
echo "5. 检查数据库连接数"
kubectl exec -it $(kubectl get pods -n formal-framework -l app=postgres -o jsonpath='{.items[0].metadata.name}') -n formal-framework -- psql -U postgres -d formal_framework -c "SELECT count(*) FROM pg_stat_activity;"
echo ""

# 检查慢查询
echo "6. 检查慢查询"
kubectl exec -it $(kubectl get pods -n formal-framework -l app=postgres -o jsonpath='{.items[0].metadata.name}') -n formal-framework -- psql -U postgres -d formal_framework -c "SELECT query, mean_time, calls FROM pg_stat_statements ORDER BY mean_time DESC LIMIT 5;"
echo ""

echo "=== 性能诊断完成 ==="
echo "结束时间: $(date)"
```

## 预防措施

### 1. 监控告警设置

```yaml
# 关键指标告警
alerts:
  - alert: HighCPUUsage
    expr: 100 - (avg by(instance) (rate(node_cpu_seconds_total{mode="idle"}[5m])) * 100) > 80
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "CPU使用率过高"
      description: "节点 {{ $labels.instance }} CPU使用率为 {{ $value }}%"

  - alert: HighMemoryUsage
    expr: (1 - (node_memory_MemAvailable_bytes / node_memory_MemTotal_bytes)) * 100 > 85
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "内存使用率过高"
      description: "节点 {{ $labels.instance }} 内存使用率为 {{ $value }}%"

  - alert: PodCrashLooping
    expr: rate(kube_pod_container_status_restarts_total[15m]) > 0
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "Pod崩溃循环"
      description: "Pod {{ $labels.pod }} 在15分钟内重启了 {{ $value }} 次"
```

### 2. 健康检查配置

```yaml
# 应用健康检查
livenessProbe:
  httpGet:
    path: /health
    port: 8080
  initialDelaySeconds: 30
  periodSeconds: 10
  timeoutSeconds: 5
  failureThreshold: 3

readinessProbe:
  httpGet:
    path: /ready
    port: 8080
  initialDelaySeconds: 5
  periodSeconds: 5
  timeoutSeconds: 3
  failureThreshold: 3
```

### 3. 资源限制设置

```yaml
# 资源限制
resources:
  limits:
    cpu: 500m
    memory: 512Mi
  requests:
    cpu: 250m
    memory: 256Mi
```

## 联系支持

如果以上解决方案无法解决您的问题，请联系技术支持：

- **GitHub Issues**: <https://github.com/formal-framework/formal-framework/issues>
- **邮件支持**: <support@formal-framework.com>
- **文档**: <https://docs.formal-framework.com>
- **社区论坛**: <https://community.formal-framework.com>

在联系支持时，请提供以下信息：

1. 问题描述
2. 错误日志
3. 系统环境信息
4. 复现步骤
5. 已尝试的解决方案
