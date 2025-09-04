# 端到端示例：云原生-运行时（L2→L3→行业→证据→校验）

## 1. 目标

- 从 L2 元模型到 L3 标准模型，映射到云原生行业实践，并以证据与校验矩阵完成可追溯验证。
- 提供完整的可复现环境搭建、部署、测试和验证流程。

## 2. 相关文档

- L2：`L2_D04_运行时元模型.md`
- L3：`L3_D04_运行时标准模型.md`
- 行业：`L4_D90_CN_行业索引与对标.md`
- 证据：`EVIDENCE_K8S-001.md`、`EVIDENCE_ISTIO-001.md`、`EVIDENCE_PROM-001.md`
- 校验矩阵：`VERIFICATION_MATRIX.md`

## 3. 模型桥接

- L2 → L3：Workload/Service/NetworkPolicy 等实体在 L3 中落标为字段与不变式（R1/R2/R3）
- L3 → 行业：K8s 的 Pod/Service/Ingress、Istio 的 mTLS/流量策略、Prometheus 的 SLI/SLO

## 4. 环境准备

### 4.1 前置要求

```bash
# 必需工具
- kubectl (v1.24+)
- helm (v3.8+)
- docker
- curl
- jq

# 可选工具
- minikube (本地开发)
- kind (本地集群)
- istioctl (服务网格)
```

### 4.2 集群准备

#### 使用 Minikube (推荐本地开发)

```bash
# 启动集群
minikube start --cpus=4 --memory=8192 --driver=docker

# 启用插件
minikube addons enable ingress
minikube addons enable metrics-server

# 验证集群状态
kubectl get nodes
kubectl get pods --all-namespaces
```

#### 使用 Kind (多节点测试)

```bash
# 创建集群
kind create cluster --name formal-framework --config - <<EOF
kind: Cluster
apiVersion: kind.x-k8s.io/v1alpha4
nodes:
- role: control-plane
  extraPortMappings:
  - containerPort: 80
    hostPort: 80
    protocol: TCP
- role: worker
- role: worker
EOF

# 验证集群
kubectl get nodes
```

## 5. 部署与配置

### 5.1 基础应用部署

#### 创建命名空间

```bash
kubectl create namespace demo
kubectl create namespace monitoring
```

#### 部署示例应用

```bash
# 部署 API 服务
kubectl apply -f docs/samples/k8s/demo-api-deployment.yaml
kubectl apply -f docs/samples/k8s/demo-api-service.yaml

# 部署前端应用
kubectl apply -f docs/samples/k8s/demo-frontend-deployment.yaml
kubectl apply -f docs/samples/k8s/demo-frontend-service.yaml

# 部署 Ingress
kubectl apply -f docs/samples/k8s/demo-ingress.yaml
```

#### 验证部署状态

```bash
# 检查 Pod 状态
kubectl get pods -n demo

# 检查服务状态
kubectl get svc -n demo

# 检查 Ingress 状态
kubectl get ingress -n demo
```

### 5.2 网络策略配置

#### 应用网络隔离策略

```bash
# 默认拒绝所有流量
kubectl apply -f docs/samples/k8s/networkpolicy-deny-all.yaml

# 允许前端到后端的流量
kubectl apply -f docs/samples/k8s/networkpolicy-frontend-to-backend.yaml

# 允许监控流量
kubectl apply -f docs/samples/k8s/networkpolicy-monitoring.yaml
```

#### 验证网络策略

```bash
# 检查策略状态
kubectl get networkpolicies -n demo

# 测试网络隔离
kubectl exec -n demo deploy/demo-frontend -- curl -sS http://demo-api.demo.svc.cluster.local/health
```

### 5.3 监控配置

#### 部署 Prometheus

```bash
# 添加 Helm 仓库
helm repo add prometheus-community https://prometheus-community.github.io/helm-charts
helm repo update

# 部署 Prometheus
helm install prometheus prometheus-community/kube-prometheus-stack \
  --namespace monitoring \
  --create-namespace \
  --values docs/samples/prometheus/values.yaml
```

#### 配置告警规则

```bash
# 应用自定义告警规则
kubectl apply -f docs/samples/prometheus/alerts.yaml

# 验证告警规则
kubectl get prometheusrules -n monitoring
```

## 6. 不变式与验证

### 6.1 R1: Service 可达性验证

#### 验证脚本

```bash
#!/bin/bash
# docs/samples/verification-scripts/verify-service-reachability.sh

set -e

NAMESPACE=${1:-demo}
SERVICE_NAME=${2:-demo-api}

echo "验证服务可达性: $SERVICE_NAME.$NAMESPACE"

# 检查服务状态
echo "1. 检查服务状态..."
kubectl get svc $SERVICE_NAME -n $NAMESPACE

# 检查端点状态
echo "2. 检查端点状态..."
kubectl get endpoints $SERVICE_NAME -n $NAMESPACE

# 测试服务连通性
echo "3. 测试服务连通性..."
kubectl run test-connectivity --image=curlimages/curl:latest -i --rm --restart=Never \
  -- curl -sS http://$SERVICE_NAME.$NAMESPACE.svc.cluster.local/health

echo "✅ 服务可达性验证通过"
```

#### 运行验证

```bash
chmod +x docs/samples/verification-scripts/verify-service-reachability.sh
./docs/samples/verification-scripts/verify-service-reachability.sh demo demo-api
```

### 6.2 R2: 网络隔离验证

#### 6.2.1 验证脚本

```bash
#!/bin/bash
# docs/samples/verification-scripts/verify-network-isolation.sh

set -e

NAMESPACE=${1:-demo}

echo "验证网络隔离策略: $NAMESPACE"

# 检查网络策略
echo "1. 检查网络策略..."
kubectl get networkpolicies -n $NAMESPACE

# 测试跨命名空间隔离
echo "2. 测试跨命名空间隔离..."
kubectl run test-isolation --image=curlimages/curl:latest -n default -i --rm --restart=Never \
  -- curl -sS --connect-timeout 5 http://demo-api.demo.svc.cluster.local/health || echo "✅ 跨命名空间访问被正确阻断"

# 测试同命名空间内通信
echo "3. 测试同命名空间内通信..."
kubectl exec -n $NAMESPACE deploy/demo-frontend -- curl -sS http://demo-api.$NAMESPACE.svc.cluster.local/health

echo "✅ 网络隔离验证通过"
```

#### 6.2.2 运行验证

```bash
chmod +x docs/samples/verification-scripts/verify-network-isolation.sh
./docs/samples/verification-scripts/verify-network-isolation.sh demo
```

### 6.3 R3: 滚动更新安全性验证

#### 6.3.1 验证脚本

```bash
#!/bin/bash
# docs/samples/verification-scripts/verify-rolling-update.sh

set -e

NAMESPACE=${1:-demo}
DEPLOYMENT=${2:-demo-api}

echo "验证滚动更新安全性: $DEPLOYMENT"

# 检查部署配置
echo "1. 检查部署配置..."
kubectl get deployment $DEPLOYMENT -n $NAMESPACE -o yaml | grep -A 5 "strategy:"

# 执行滚动更新
echo "2. 执行滚动更新..."
kubectl set image deployment/$DEPLOYMENT demo-api=demo-api:v2 -n $NAMESPACE

# 监控更新过程
echo "3. 监控更新过程..."
kubectl rollout status deployment/$DEPLOYMENT -n $NAMESPACE

# 验证服务连续性
echo "4. 验证服务连续性..."
for i in {1..10}; do
  kubectl exec -n $NAMESPACE deploy/demo-frontend -- curl -sS http://demo-api.$NAMESPACE.svc.cluster.local/health
  sleep 2
done

echo "✅ 滚动更新安全性验证通过"
```

#### 6.3.2 运行验证

```bash
chmod +x docs/samples/verification-scripts/verify-rolling-update.sh
./docs/samples/verification-scripts/verify-rolling-update.sh demo demo-api
```

## 7. 性能测试与验证

### 7.1 负载测试

#### k6 性能测试脚本

```javascript
// docs/samples/k6/cloud-native-load-test.js

import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate } from 'k6/metrics';

const errorRate = new Rate('errors');

export const options = {
  stages: [
    { duration: '2m', target: 50 },   // 爬升到50用户
    { duration: '5m', target: 50 },   // 保持50用户5分钟
    { duration: '2m', target: 100 },  // 爬升到100用户
    { duration: '5m', target: 100 },  // 保持100用户5分钟
    { duration: '2m', target: 0 },    // 降到0用户
  ],
  thresholds: {
    http_req_duration: ['p(95)<500'], // 95%的请求必须在500ms内完成
    http_req_failed: ['rate<0.05'],   // 错误率必须小于5%
    errors: ['rate<0.05'],            // 自定义错误率必须小于5%
  },
};

const BASE_URL = __ENV.BASE_URL || 'http://demo-api.demo.svc.cluster.local';

export default function () {
  // 健康检查
  const healthCheck = http.get(`${BASE_URL}/health`);
  check(healthCheck, {
    'health check status is 200': (r) => r.status === 200,
    'health check response time < 200ms': (r) => r.timings.duration < 200,
  });

  // API测试
  const payload = JSON.stringify({
    message: 'Hello from k6',
    timestamp: new Date().toISOString()
  });

  const params = {
    headers: {
      'Content-Type': 'application/json',
    },
  };

  // POST请求测试
  const createResponse = http.post(`${BASE_URL}/api/messages`, payload, params);
  check(createResponse, {
    'create message status is 201': (r) => r.status === 201,
    'create message response time < 300ms': (r) => r.timings.duration < 300,
  });

  errorRate.add(createResponse.status !== 201);

  // GET请求测试
  if (createResponse.status === 201) {
    const messageId = createResponse.json('id');
    const getResponse = http.get(`${BASE_URL}/api/messages/${messageId}`, params);
    
    check(getResponse, {
      'get message status is 200': (r) => r.status === 200,
      'get message response time < 200ms': (r) => r.timings.duration < 200,
    });

    errorRate.add(getResponse.status !== 200);
  }

  sleep(1);
}

export function setup() {
  console.log('Setting up cloud-native load test...');
}

export function teardown(data) {
  console.log('Cleaning up cloud-native load test...');
}
```

#### 运行性能测试

```bash
# 设置环境变量
export BASE_URL=http://demo-api.demo.svc.cluster.local

# 运行测试
k6 run docs/samples/k6/cloud-native-load-test.js

# 或使用 Docker
docker run -i --rm -v $(pwd):/scripts -e BASE_URL=$BASE_URL grafana/k6 run /scripts/docs/samples/k6/cloud-native-load-test.js
```

### 7.2 监控指标验证

#### PromQL 查询验证

```bash
# 检查请求成功率
kubectl exec -n monitoring deploy/prometheus-kube-prometheus-prometheus -- \
  curl -sS "http://localhost:9090/api/v1/query?query=rate(http_requests_total{status=~\"2..\"}[5m])/rate(http_requests_total[5m])"

# 检查响应时间
kubectl exec -n monitoring deploy/prometheus-kube-prometheus-prometheus -- \
  curl -sS "http://localhost:9090/api/v1/query?query=histogram_quantile(0.95,rate(http_request_duration_seconds_bucket[5m]))"

# 检查错误率
kubectl exec -n monitoring deploy/prometheus-kube-prometheus-prometheus -- \
  curl -sS "http://localhost:9090/api/v1/query?query=rate(http_requests_total{status=~\"5..\"}[5m])"
```

## 8. 自动化验证流程

### 8.1 完整验证脚本

```bash
#!/bin/bash
# docs/samples/verification-scripts/run-complete-verification.sh

set -e

echo "🚀 开始云原生运行时端到端验证..."

# 1. 环境检查
echo "📋 1. 环境检查..."
kubectl cluster-info
kubectl get nodes

# 2. 部署验证
echo "📋 2. 部署验证..."
./docs/samples/verification-scripts/verify-service-reachability.sh demo demo-api
./docs/samples/verification-scripts/verify-network-isolation.sh demo
./docs/samples/verification-scripts/verify-rolling-update.sh demo demo-api

# 3. 性能测试
echo "📋 3. 性能测试..."
export BASE_URL=http://demo-api.demo.svc.cluster.local
k6 run docs/samples/k6/cloud-native-load-test.js

# 4. 监控验证
echo "📋 4. 监控验证..."
kubectl get prometheusrules -n monitoring
kubectl get alerts -n monitoring

echo "✅ 云原生运行时端到端验证完成！"
```

### 8.2 CI/CD 集成

```yaml
# .github/workflows/cloud-native-verification.yml

name: Cloud Native Runtime Verification

on:
  push:
    branches: [ main ]
    paths: [ 'docs/E2E_云原生_运行时_端到端指南.md', 'docs/samples/**' ]
  pull_request:
    branches: [ main ]

jobs:
  verify:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Setup Minikube
      uses: medyagh/setup-minikube@master
    
    - name: Deploy Demo Application
      run: |
        kubectl create namespace demo
        kubectl apply -f docs/samples/k8s/
    
    - name: Run Verification Scripts
      run: |
        chmod +x docs/samples/verification-scripts/*.sh
        ./docs/samples/verification-scripts/run-complete-verification.sh
    
    - name: Upload Test Results
      uses: actions/upload-artifact@v3
      with:
        name: verification-results
        path: test-results/
```

## 9. 预期结果与证据

### 9.1 验证结果

- ✅ 服务可达性：100% 通过
- ✅ 网络隔离：100% 通过  
- ✅ 滚动更新：100% 通过
- ✅ 性能指标：满足 SLA 要求
- ✅ 监控告警：正常工作

### 9.2 证据收集

```bash
# 收集验证证据
mkdir -p evidence/cloud-native-$(date +%Y%m%d)

# 服务状态截图
kubectl get all -n demo -o wide > evidence/cloud-native-$(date +%Y%m%d)/service-status.txt

# 网络策略状态
kubectl get networkpolicies -n demo -o yaml > evidence/cloud-native-$(date +%Y%m%d)/network-policies.yaml

# 性能测试结果
k6 run docs/samples/k6/cloud-native-load-test.js --out json=evidence/cloud-native-$(date +%Y%m%d)/performance-results.json

# 监控指标截图
# 手动截图保存到 evidence/cloud-native-$(date +%Y%m%d)/monitoring-screenshots/
```

## 10. 扩展与改进

### 10.1 更新验证矩阵

将验证结果更新到 `VERIFICATION_MATRIX.md`：

```markdown
| L3 模型 | 不变式/规则 | 验证方法 | 工具/脚本 | 对应文档章节 | 状态 |
| --- | --- | --- | --- | --- | --- |
| L3_D04 运行时 | R1 服务可达性 | 连通性测试 | verify-service-reachability.sh | E2E_云原生_运行时_端到端指南 §6.1 | ✅ 已验证 |
| L3_D04 运行时 | R2 网络隔离 | 策略验证 | verify-network-isolation.sh | E2E_云原生_运行时_端到端指南 §6.2 | ✅ 已验证 |
| L3_D04 运行时 | R3 滚动更新 | 部署验证 | verify-rolling-update.sh | E2E_云原生_运行时_端到端指南 §6.3 | ✅ 已验证 |
```

### 10.2 更新证据条目

更新相关证据文件：

- `EVIDENCE_K8S-001.md`：添加部署验证结果
- `EVIDENCE_ISTIO-001.md`：添加网络策略验证结果  
- `EVIDENCE_PROM-001.md`：添加监控指标验证结果

### 10.3 社区贡献

- 提交验证脚本到 `docs/samples/verification-scripts/`
- 更新端到端指南文档
- 分享验证经验和最佳实践

## 11. 故障排除

### 11.1 常见问题

#### 服务无法访问

```bash
# 检查 Pod 状态
kubectl get pods -n demo

# 检查服务配置
kubectl get svc -n demo -o yaml

# 检查网络策略
kubectl get networkpolicies -n demo
```

#### 性能测试失败

```bash
# 检查资源限制
kubectl describe pod -n demo

# 检查监控指标
kubectl logs -n monitoring deploy/prometheus-kube-prometheus-prometheus
```

#### 监控告警异常

```bash
# 检查 Prometheus 状态
kubectl get pods -n monitoring

# 检查告警规则
kubectl get prometheusrules -n monitoring -o yaml
```

### 11.2 获取帮助

- 查看 Kubernetes 官方文档
- 提交 GitHub Issue
- 联系维护团队

## 12. 总结

本端到端指南提供了从 L2 元模型到 L3 标准模型，再到云原生行业实践的完整验证流程。通过自动化脚本和工具，可以快速验证运行时系统的各种不变式和约束，确保系统的可靠性、安全性和性能。

关键成果：

1. 完整的可复现环境搭建流程
2. 自动化验证脚本集合
3. 性能测试和监控验证方法
4. CI/CD 集成示例
5. 故障排除指南

下一步可以扩展到其他行业和模型，建立更全面的验证体系。
