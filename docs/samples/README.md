# Samples 使用说明（占位）

## 环境变量

- 复制 `env.example` 为 `.env` 并按需修改
- 加载：`set -a; source .env; set +a`

## 快速开始（minikube/kind）

- minikube：`minikube start`，或 kind：`kind create cluster`
- 部署 nginx：
  - `kubectl apply -f k8s/nginx-deploy.yaml`
  - `kubectl apply -f k8s/nginx-service.yaml`
- 访问方式：
  - NodePort：`http://$(minikube ip):30080/`
  - 或端口转发：`bash k8s/port-forward.sh` → `http://127.0.0.1:8080/`

## K8s（自建 API 样例）

1. `kubectl apply -f k8s/deploy.yaml`
2. `kubectl apply -f k8s/service.yaml`
3. `kubectl apply -f k8s/networkpolicy-deny-all.yaml`
4. `bash k8s/rolling_update.sh ${NEW_TAG:-vNEXT}`

## Prometheus 本地启动

- 进入 `prometheus/` 目录：
  - `docker compose up -d`
  - 打开 Prometheus：`http://localhost:9090`
  - 打开 Alertmanager：`http://localhost:9093`
- 修改抓取目标：编辑 `prometheus/prometheus.yml` 的 `targets` 指向本地/转发端口
- 加载告警：本目录已挂载 `alerts.yaml`

## 校验步骤

- PromQL 示例：`rate(http_requests_total{status=~"5.."}[5m])`
- 触发告警：压测 `k6/run.sh`，观察 Prometheus/Alertmanager 与 Runbook

## k6 压测

- `bash k6/run.sh` 或 `BASE_URL=$BASE_URL k6 run k6/http_load_test.js`

## OpenBanking

- Postman/Newman：`newman run fin/openbanking.postman_collection.json --env-var base_url=$BASE_URL --env-var token=$TOKEN`（占位）
- SQL 对账：使用 `fin/reconciliation.sql` 在测试库执行

## IoT 本地验证（EMQX）

- 启动 EMQX：`cd iot && docker compose -f emqx-docker-compose.yml up -d`
- 订阅：`python mqtt_sub.py`
- 发布：`python mqtt_pub.py`

## AI 推理本地验证（FastAPI）

- 启动：`cd ai && bash run.sh`
- 调用：`curl -X POST http://127.0.0.1:8000/infer -H 'Content-Type: application/json' -d '{"text":"hello"}'`
