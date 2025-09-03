# 端到端示例：云原生-运行时（L2→L3→行业→证据→校验）

## 1. 目标

- 从 L2 元模型到 L3 标准模型，映射到云原生行业实践，并以证据与校验矩阵完成可追溯验证。

## 2. 相关文档

- L2：`L2_D04_运行时元模型.md`
- L3：`L3_D04_运行时标准模型.md`
- 行业：`L4_D90_CN_行业索引与对标.md`
- 证据：`EVIDENCE_K8S-001.md`、`EVIDENCE_ISTIO-001.md`、`EVIDENCE_PROM-001.md`
- 校验矩阵：`VERIFICATION_MATRIX.md`

## 3. 模型桥接

- L2 → L3：Workload/Service/NetworkPolicy 等实体在 L3 中落标为字段与不变式（R1/R2/R3）
- L3 → 行业：K8s 的 Pod/Service/Ingress、Istio 的 mTLS/流量策略、Prometheus 的 SLI/SLO

## 4. 不变式与验证

- R1 ServiceReachability：VIP→Pod 连通性（探测脚本占位）
- R2 NetworkIsolation：跨命名空间未授权流量阻断（策略与测试占位）
- R3 RollingSafety：max_unavailable 与 readiness gate（滚更脚本占位）

## 5. 工具与命令示例

- 连通性/性能：
  - `kubectl -n default apply -f docs/samples/k8s/deploy.yaml`
  - `kubectl -n default apply -f docs/samples/k8s/service.yaml`
  - `kubectl -n default exec deploy/demo-api -- curl -sS http://demo-api.default.svc.cluster.local/health`
  - `BASE_URL=http://demo-api.default.svc.cluster.local/health k6 run docs/samples/k6/http_load_test.js`
- 替代（nginx，minikube/kind 兼容）：
  - `kubectl apply -f docs/samples/k8s/nginx-deploy.yaml`
  - `kubectl apply -f docs/samples/k8s/nginx-service.yaml`
  - `bash docs/samples/k8s/port-forward.sh` → `curl -sS http://127.0.0.1:8080/`
- 策略与证书：
  - `kubectl apply -f docs/samples/k8s/networkpolicy-deny-all.yaml`
  - `istioctl x describe pod <pod> -n <ns>`
- 告警与SLO：
  - PromQL：`rate(http_requests_total{status=~"5.."}[5m])`
  - `alerts.yaml`：`docs/samples/prometheus/alerts.yaml`
  - Runbook：`docs/runbooks/demo-api-high-error-rate.md`

## 6. 预期结果与证据

- 产出更新相应 evidence 文件，附运行截图/链接（占位）

## 7. 扩展

- 将验证样例补充回 `L3_D04_运行时标准模型.md` 与 `VERIFICATION_MATRIX.md`
