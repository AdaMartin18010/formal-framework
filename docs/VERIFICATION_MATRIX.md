# 模型↔验证 校验矩阵（L3 ↔ Verification Sorting）

说明：将 L3 标准模型中的关键不变式，映射到 verification-sorting 文档中的验证策略与章节，支持可追溯验证。

| L3 模型 | 不变式/规则 | 验证方法 | 工具/脚本 | 对应文档章节 |
| --- | --- | --- | --- | --- |
| L3_D01 交互 | I1 版本兼容 | 类型论/契约测试 | contract-tests (pytest), schema-diff（newman run fin/openbanking.postman_collection.json） | FORMAL_VERIFICATION_SORTING.md §3/§5 |
| L3_D01 交互 | I2 鉴权强制 | 逻辑验证/安全测试 | zap/postman/newman（curl -H "Authorization: Bearer token" <http://127.0.0.1:3000/accounts）> | TESTING_VERIFICATION_SORTING.md §3/§5 |
| L3_D02 数据 | D1 主键唯一 | 逻辑验证/静态分析 | db-constraint-check, sql-tests | FORMAL_VERIFICATION_SORTING.md §3.5 |
| L3_D02 数据 | D2 外键完整 | 模型检查/一致性校验 | fk-check, migration-tests（psql -f fin/reconciliation.sql） | FORMAL_VERIFICATION_SORTING.md §3.2 |
| L3_D04 运行时 | R2 网络隔离 | 图论/策略模型检查 | kubectl/istioctl + policy-test（kubectl apply -f k8s/networkpolicy-deny-all.yaml） | QUALITY_VERIFICATION_SORTING.md §3/§4 |
| L3_D05 部署 | DEP2 门禁 | CI 门禁/测试覆盖率 | Sonar/Codecov/Gate scripts | TESTING_VERIFICATION_SORTING.md §6 |
| L3_D06 监控 | MON1 SLO告警 | 断言/性能测试 | promql, alert-tests（docker compose up -d; open <http://localhost:9090）> | TESTING_VERIFICATION_SORTING.md §3.5 |
| L3_D07 控制调度 | CS1 可调度性 | 可调度性分析/模型检查 | schedulability-analyzer | FORMAL_VERIFICATION_SORTING.md §3.2 |
| L3_D07 控制调度 | CS2 互斥 | 静态分析/运行时断言 | lock-checker, race-detector | TESTING_VERIFICATION_SORTING.md §3 |
| L3_D08 测试 | TST2 覆盖率 | 静态+动态分析 | Jacoco/Coverage.py | TESTING_VERIFICATION_SORTING.md §3 |
| L3_D09 CI/CD | CI1 阻断 | 流水线模拟/模型检查 | GH Actions/GitLab rules | FORMAL_VERIFICATION_SORTING.md §4 |
| L3_D10 分布式 | DP1 线性一致 | 模型检查/TLA+/性质证明 | TLA+/Apalache | FORMAL_VERIFICATION_SORTING.md §3.2 |
| L3_D04 运行时 | 可达性（IoT） | 运行/订阅/发布验证 | EMQX + mqtt_pub.py/mqtt_sub.py | TESTING_VERIFICATION_SORTING.md §3 |
| L3_D04/06 运行时/监控 | 性能（AI） | 压测/告警验证 | FastAPI + k6 + PromQL | TESTING_VERIFICATION_SORTING.md §3.5 |

证据挂接：

- PROM-001 → L3_D06 MON1；K8S-001 → L3_D04 R3；ISTIO-001 → L3_D04 R2；FIN-CORE-001 → L3_D02 D2
- AI-002 → L3_D02 数据一致性；W3-002 → L3_D10 吞吐/最终性；IOT-002 → L3_D04/L3_D07 边云稳定
