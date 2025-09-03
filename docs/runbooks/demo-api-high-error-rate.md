# Runbook: demo-api High 5xx Error Rate

## 触发条件

- Prometheus 告警 HighErrorRate 触发：5xx 比例 > 5% 持续 10 分钟

## 排查步骤（占位）

1. 查看最近发布：`kubectl rollout history deploy/demo-api`
2. 检查Pod日志：`kubectl logs deploy/demo-api -c api --tail=200`
3. 检查依赖服务与网络策略：`kubectl get networkpolicy -A`
4. 短期缓解：开启限流/回滚 `docs/samples/k8s/rolling_update.sh`

## 验证恢复

- 观测 SLO 指标回落至阈值内；相关告警自动恢复
