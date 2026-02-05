# 证据条目索引 (Evidence Index)

本目录存放形式化框架中引用的标准、课程、应用与案例的证据条目（evidence）。每条目对应 `evidence:ID`，在行业 README、L4 索引等文档中被引用。

**一致性状态**：当前所有被引用的 evidence ID 均在本目录下有对应 .md 文件（完整或占位），季度检查可达到 100% 证据引用与文件一致。见 `python scripts/quarterly_doc_check.py --root docs --evidence-scan`。

## 已完整填写的证据条目

| ID | 标题 | 分类 |
|----|------|------|
| CN-K8S-BASE | Kubernetes 基础编排 | 应用 |
| CN-ISTIO-TRAFFIC | Istio 服务网格流量治理 | 应用 |
| CN-ARGO-GITOPS | Argo CD GitOps 持续交付 | 应用 |
| CN-OBS-OTEL | 可观测性一体化（Prometheus+OTel） | 应用 |
| CN-SERVERLESS-LAMBDA | Serverless（AWS Lambda） | 应用 |
| CN-SERVERLESS-KNATIVE | Serverless（Knative） | 应用 |
| CN-API-KONG | API 网关（Kong） | 应用 |
| CN-API-ENVOY | API 网关与代理（Envoy） | 应用 |
| AI-SERVING-VERSIONS | TensorFlow Serving 模型服务 | 应用 |
| FIN-PAY-GW | 支付网关与 PCI-DSS | 标准 |
| FIN-OPENBANKING-001 | Open Banking | 应用/标准 |
| IOT-DEVICE-ACCESS | 设备接入（Eclipse Mosquitto 等） | 应用 |
| IOT-SMARTFACTORY-001 | 智能工厂案例 | 应用 |
| W3-CONSENSUS-POS | 以太坊 2.0 共识（PoS） | 标准/应用 |
| W3-UNISWAP-001 | Uniswap 等 DeFi 协议 | 应用 |
| STD-12207 | ISO/IEC/IEEE 12207 软件生命周期过程 | 标准 |
| STD-15288 | ISO/IEC/IEEE 15288 系统生命周期过程 | 标准 |
| STD-27001 | ISO/IEC 27001 信息安全管理体系 | 标准 |
| STD-42010 | ISO/IEC/IEEE 42010 架构描述 | 标准 |
| STD-1012 | IEEE 1012 系统/软件/硬件验证和确认 (2024) | 标准 |
| STD-24748 | ISO/IEC/IEEE 24748-2 15288 应用指南 (2024) | 标准 |
| STD-TLA | TLA+ 行为与时序逻辑规约 | 标准/方法 |
| STD-ALLOY | Alloy 关系逻辑与轻量形式化分析 | 标准/方法 |
| STD-29119-5 | IEEE/ISO 29119-5 软件测试 — 关键词驱动测试 (2024) | 标准 |
| STD-24641 | ISO/IEC/IEEE 24641 MBSSE 方法与工具 (2023) | 标准 |
| K8S-001 | Kubernetes 容器编排（L4 引用条目） | 应用 |
| ISTIO-001 | Istio 服务网格（L4 引用条目） | 应用 |
| COURSE-ETH-DS | ETH Zürich Distributed Systems 课程 | 课程 |

## 待补充（占位）证据条目

以下条目已创建文件并标注「待补充」，引用处可正常链接，内容将后续完善：

- **云原生/CN**：ARGO-001、CN-ARGO、CN-OTEL、KNA-001、PROM-001
- **AI**：AI-AIRFLOW-001、AI-EVIDENTLY-001、AI-FEAST-001、AI-FEAST-CONSISTENCY、AI-GE-001、AI-KF、AI-KUBEFLOW-001、AI-MLFLOW、AI-MLFLOW-001、AI-PIPELINE-KF、AI-REGISTRY-001、AI-SERVING-001
- **金融**：FIN-API-001、FIN-CBDC-001、FIN-CORE-001、FIN-DLT-001、FIN-PCI-001、FIN-QUORUM-001、FIN-RISK-REALTIME、FIN-TRADE-MATCH
- **IoT**：IOT-AGRICULTURE-001、IOT-DATA-COLLECT、IOT-EDGEX-001、IOT-EDGE-RT、IOT-EMQX-001、IOT-IOTDB-001、IOT-KUBEEDGE-001、IOT-LWM2M-001、IOT-MOSQUITTO-001、IOT-OPCUA-001、IOT-SMARTCITY-001、IOT-THINGSBOARD-001
- **Web3**：W3-BRIDGE-001、W3-CHAINLINK-001、W3-CHAINLINK-NETWORK-001、W3-CROSS-CHAIN、W3-DEFI-001、W3-DID-001、W3-ETHEREUM-001、W3-ETHEREUM-ECOSYSTEM-001、W3-IPFS-001、W3-POLKADOT-001、W3-SC-VERIFY、W3-SOLANA-001
- **标准/课程**：STD-ASYNCAPI、STD-OAS31、STD-OCI
- **占位说明**：PLACEHOLDER（模板）、ID（标识符说明）

## 待补充证据优先级列表

按「标准/课程优先、L4 与行业 README 引用频率」排序，供每季度证据条目补全任务认领。每季度建议从高优先级中认领 2–4 条补全，符合 [CITATION_STANDARDS](../CITATION_STANDARDS.md) 与 [QUALITY_STANDARDS](../QUALITY_STANDARDS.md)。

| 优先级 | 证据 ID（示例） | 说明 |
|--------|-----------------|------|
| **高** | STD-ASYNCAPI、STD-OAS31、STD-OCI、STD-29119-5、STD-24641 | 标准类，被 AUTHORITY_ALIGNMENT_INDEX 或 L3 引用 |
| **高** | K8S-001、CN-ARGO、ISTIO-001、PROM-001、CN-OTEL | 云原生 L4_D90 / 行业 README 高引用 |
| **高** | AI-MLFLOW-001、AI-KUBEFLOW-001、AI-FEAST-001、AI-REGISTRY-001 | AI 基础设施 L4_D93 / 行业 README 高引用 |
| **高** | FIN-PCI-001、FIN-CORE-001、FIN-API-001 | 金融 L4_D91 合规与核心引用 |
| **中** | IOT-EDGEX-001、IOT-KUBEEDGE-001、IOT-OPCUA-001 | 物联网 L4_D92 常用项目 |
| **中** | W3-ETHEREUM-001、W3-CHAINLINK-001、W3-DID-001 | Web3 L4_D94 常用项目 |
| **中** | 其余待补充条目 | 按行业或专题需要认领 |

维护说明：可根据 L4 索引与各行业 README 中 evidence 引用次数定期调整上表顺序；新标准（如 STD-29119-5、STD-24641）若引入则加入高优先级。与 [RECURSIVE_IMPROVEMENT_KANBAN](../RECURSIVE_IMPROVEMENT_KANBAN.md) 每季度「证据优先级认领」任务配合使用。

## 模板与规范

- 新建证据条目请使用 [../templates/TEMPLATE_证据条目.md](../templates/TEMPLATE_证据条目.md)。
- 引用与可信度要求见 [../CITATION_STANDARDS.md](../CITATION_STANDARDS.md)。
