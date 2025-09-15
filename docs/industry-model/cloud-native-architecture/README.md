# 云原生行业模型 - 案例库（骨架占位）

> 说明：以下为最小案例骨架（占位）。待补充 evidence:* 与对齐链接。

## 案例一：Kubernetes 集群编排（基础）

### 场景与目标

- 单集群基础工作负载编排，服务暴露与健康检查

### 术语与概念对齐（行业↔通用）

- Pod/Service/Ingress ↔ `L3_D04_运行时标准模型.md` · `L3_D01_交互标准模型.md`

### 结构与约束

- Workload/Service/Network/Storage 基本对象与不变式

### 接口与 DSL 片段

```yaml
# 占位
```

### 验证与度量

- 可用性/健康检查/资源配额

### 证据与引用

- evidence:CN-K8S-BASE

## 案例二：Service Mesh 流量治理（Istio）

### 场景与目标

- 蓝绿/金丝雀发布，mTLS，熔断与限流

### 术语与概念对齐

- VirtualService/DestinationRule/Gateway ↔ `L3_D04_运行时标准模型.md` ServiceMesh

### 结构与约束

- 流量策略一致性、证书与安全策略

### 接口与 DSL 片段

```yaml
# 占位
```

### 验证与度量

- 错误率、延迟、成功率 SLO

### 证据与引用

- evidence:CN-ISTIO-TRAFFIC

## 案例三：GitOps 持续交付（ArgoCD）

### 场景与目标

- 期望状态、同步策略、回滚与门禁

### 术语与概念对齐

- Desired/Sync/PR Gate ↔ `L3_D05_部署标准模型.md` GitOps

### 结构与约束

- 不变式：ImmutableArtifact/QualityGateEnforcement

### 接口与 DSL 片段

```yaml
# 占位
```

### 验证与度量

- 同步成功率、回滚时间、漂移检测

### 证据与引用

- evidence:CN-ARGO-GITOPS

## 案例四：可观测性一体化（Prometheus+OTel）

### 场景与目标

- 指标/追踪/日志统一语义与告警

### 术语与概念对齐

- Metric/Alert/Trace/Dashboard ↔ `L3_D06_监控标准模型.md`

### 结构与约束

- LabelCardinalityBound/RunbookPresence/MetricNaming

### 接口与 DSL 片段

```yaml
# 占位
```

### 验证与度量

- 告警噪声、SLO 覆盖率、追踪采样率

### 证据与引用

- evidence:CN-OBS-OTEL
