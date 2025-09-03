# 文档主索引（分层×领域×行业）

说明：统一导航，快速定位 L1-L4 层次与行业文档。新增条目请遵循 `docs/FILE_NUMBERING_AND_TEMPLATE.md`。

## 索引

- 编号与模板：`FILE_NUMBERING_AND_TEMPLATE.md`，`QUALITY_STANDARDS.md`，`CITATION_STANDARDS.md`，`CODE_REVIEW_GUIDE.md`，`EXPERT_REVIEW_SYSTEM.md`，`TEMPLATE_证据条目.md`，`TEMPLATE_映射矩阵.md`
- L1 理论基础：集合论、图论、范畴论、类型论、逻辑
- L2 元模型：交互、数据、功能、运行时、部署、监控、控制调度、测试、CI/CD、分布式模式
- L3 标准模型：对应 L2 的标准化模型
- L4 行业应用：云原生、金融、物联网、AI 基础设施、Web3
- 校验矩阵：`VERIFICATION_MATRIX.md`
- 端到端指南：`E2E_云原生_运行时_端到端指南.md`，`E2E_金融_OpenBanking_API_端到端指南.md`
- Samples：`samples/README.md`（使用说明）

## L1 理论基础

- L1_理论基础_README.md

## L2 元模型

- L2_元模型_README.md
- L2_D01_交互元模型.md
- L2_D02_数据元模型.md
- L2_D04_运行时元模型.md
- L2_D07_控制调度元模型.md

## L3 标准模型

- L3_标准模型_README.md
- L3_D01_交互标准模型.md
- L3_D02_数据标准模型.md
- L3_D04_运行时标准模型.md
- L3_D05_部署标准模型.md
- L3_D06_监控标准模型.md
- L3_D07_控制调度标准模型.md
- L3_D08_测试标准模型.md
- L3_D09_CICD标准模型.md
- L3_D10_分布式模式标准模型.md

## L4 行业应用（计划项）

- L4_D90_CN_行业索引与对标.md（云原生）
- L4_D91_FIN_行业索引与对标.md（金融）
- L4_D92_IOT_行业索引与对标.md（物联网）
- L4_D93_AI_行业索引与对标.md（AI 基础设施）
- L4_D94_W3_行业索引与对标.md（Web3）

## 证据示例

- EVIDENCE_K8S-001.md
- EVIDENCE_ISTIO-001.md
- EVIDENCE_PROM-001.md
- EVIDENCE_FIN-API-001.md
- EVIDENCE_FIN-PCI-001.md
- EVIDENCE_FIN-CORE-001.md
- EVIDENCE_IOT-001.md
- EVIDENCE_IOT-002.md
- EVIDENCE_AI-001.md
- EVIDENCE_AI-002.md
- EVIDENCE_W3-001.md
- EVIDENCE_W3-002.md

## Samples

- K8s：
  - `docs/samples/k8s/deploy.yaml`
  - `docs/samples/k8s/service.yaml`
  - `docs/samples/k8s/networkpolicy-deny-all.yaml`
  - `docs/samples/k8s/rolling_update.sh`
  - `docs/samples/k8s/nginx-deploy.yaml`
  - `docs/samples/k8s/nginx-service.yaml`
  - `docs/samples/k8s/port-forward.sh`
- Prometheus：
  - `docs/samples/prometheus/alerts.yaml`
  - `docs/samples/prometheus/prometheus.yml`
  - `docs/samples/prometheus/alertmanager.yml`
  - `docs/samples/prometheus/docker-compose.yml`
- k6：
  - `docs/samples/k6/http_load_test.js`
  - `docs/samples/k6/run.sh`
- OpenBanking：
  - `docs/samples/fin/openbanking.postman_collection.json`
  - `docs/samples/fin/reconciliation.sql`
  - `docs/samples/fin/mock-api.js`
  - `docs/samples/fin/run-mock.sh`
- IoT：
  - `docs/samples/iot/emqx-docker-compose.yml`
  - `docs/samples/iot/mqtt_pub.py`
  - `docs/samples/iot/mqtt_sub.py`
- AI：
  - `docs/samples/ai/fastapi_infer.py`
  - `docs/samples/ai/run.sh`
