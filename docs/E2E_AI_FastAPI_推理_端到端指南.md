# 端到端示例：AI-FastAPI 推理（L2→L3→行业→证据→校验）

## 1. 目标

- 本地 FastAPI 推理服务 + k6 压测，映射到 L3 运行时/监控不变式与证据联动。

## 2. 相关文档

- L3：`L3_D04_运行时标准模型.md`、`L3_D06_监控标准模型.md`
- 行业：`L4_D93_AI_行业索引与对标.md`
- 样例：`docs/samples/ai/`、`docs/samples/k6/`
- 证据：`EVIDENCE_AI-001.md`、`EVIDENCE_AI-002.md`
- 矩阵：`VERIFICATION_MATRIX.md`

## 3. 步骤

1) 启动服务：`cd docs/samples/ai && bash run.sh`
2) 功能验证：`curl -X POST http://127.0.0.1:8000/infer -H 'Content-Type: application/json' -d '{"text":"hello"}'`
3) 压测：`BASE_URL=http://127.0.0.1:8000/infer k6 run docs/samples/k6/http_load_test.js`

## 4. 校验

- 延迟/吞吐：P95/P99、QPS（占位）
- 对应不变式：L3_D04 可达性与伸缩、L3_D06 SLO 告警（占位）

## 5. 结果与证据（占位）

- 截图：`images/ai-infer-k6.png`
- 指标：QPS≥X，P99≤Y ms（占位）
