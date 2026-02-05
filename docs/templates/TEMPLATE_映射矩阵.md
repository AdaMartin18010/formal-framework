# L4 行业标准/项目映射矩阵模板

> 本模板供各 L4 行业索引文档（如 L4_D90_CN、L4_D91_FIN、L4_D92_IOT、L4_D93_AI、L4_D94_W3）复用，用于填写「标准/项目与本框架模型」的映射矩阵。  
> **使用方式**：复制下表到对应 L4 文档的「标准/项目映射矩阵」小节，按行业替换领域/能力、国际标准/项目、关键术语与证据条目。

## 矩阵结构说明

| 列名 | 含义 | 填写说明 |
|------|------|----------|
| 领域/能力 | 行业子域或能力项 | 如：容器编排、服务网格、Open Banking API、支付合规 |
| 国际标准/项目 | 标准编号或开源/商业项目名 | 如：Kubernetes、ISO/IEC 27001、OpenAPI、PCI-DSS |
| 本框架模型(Lx_Dyy_Mzz) | 对应的 L2/L3 文档或组合 | 如：L3_D04_运行时标准模型、L3_D01 + L3_D05 |
| 关键术语 | 该领域在本框架中的关键术语 | 如：Pod/Service/Ingress、Consent/Token/Scope |
| 证据条目 | evidence:ID | 对应 docs/evidence/ 下的证据条目 ID，如 evidence:K8S-001 |
| 备注 | 可选说明 | 如：生产验证、合规门禁、SLO 监控 |

## 标准/项目映射矩阵（填空模板）

| 领域/能力 | 国际标准/项目 | 本框架模型(Lx_Dyy_Mzz) | 关键术语 | 证据条目 | 备注 |
| --- | --- | --- | --- | --- | --- |
| （填写） | （填写） | L3_Dxx_… / L2_Dxx_… | （填写） | evidence:XXX-001 | （填写） |
| （填写） | （填写） | （填写） | （填写） | （填写） | （填写） |

## 示例（云原生）

| 领域/能力 | 国际标准/项目 | 本框架模型(Lx_Dyy_Mzz) | 关键术语 | 证据条目 | 备注 |
| --- | --- | --- | --- | --- | --- |
| 容器编排 | Kubernetes | L3_D04_运行时标准模型 | Pod/Service/Ingress | evidence:K8S-001 | 生产验证 |
| 服务网格 | Istio | L3_D04 + L3_D01 | mTLS/Sidecar/Traffic Policy | evidence:ISTIO-001 | 金融生产 |
| 可观测 | Prometheus | L3_D06_监控标准模型 | Metric/Alert/Rule | evidence:PROM-001 | SLO 监控 |

## 示例（金融）

| 领域/能力 | 国际标准/项目 | 本框架模型(Lx_Dyy_Mzz) | 关键术语 | 证据条目 | 备注 |
| --- | --- | --- | --- | --- | --- |
| Open Banking API | OpenAPI/OBIE | L3_D01_交互标准模型 | Consent/Token/Scope | evidence:FIN-API-001 | 对账/审计 |
| 支付合规 | PCI-DSS | L3_D05_部署 + L3_D08_质量 | PAN/Tokenization/PCI Scope | evidence:FIN-PCI-001 | 扫描/审计 |

## 参见

- [evidence/README](../evidence/README.md) — 证据条目索引与待补充优先级
- [AUTHORITY_ALIGNMENT_INDEX 第 5 节](../reference/AUTHORITY_ALIGNMENT_INDEX.md#5-行业与-l4-索引映射) — 行业与 L4 索引映射
- [alignment-L2-L3-matrix](../formal-model/alignment-L2-L3-matrix.md) — L2↔L3 映射总表
