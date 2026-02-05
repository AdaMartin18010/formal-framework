# 快速导航系统 (Quick Navigation System)

**本节要点**：（1）按目标选路径表；（2）L2/L3/L4 文档列表与 L2↔L3 映射总表入口；（3）核心概念、行业模型与工具资源索引。  
**预计阅读时间**：全文约 15–20 分钟；仅查「按目标选路径」与 L2/L3 表约 5 分钟。

## 🚀 快速开始

### 按目标选路径

| 目标 | 推荐路径 | 入口文档 |
|------|----------|----------|
| 只想做云原生架构 / 容器与编排 | 云原生专项路径 | [LEARNING_PATHS 云原生专项](LEARNING_PATHS.md#云原生专项)、[L3_D04](L3_D04_运行时标准模型.md)、[L3_D05](L3_D05_部署标准模型.md)、[L3_D06](L3_D06_监控标准模型.md)、[L3_D09](L3_D09_CICD标准模型.md)、[云原生 README](industry-model/cloud-native-architecture/README.md) |
| 做形式化验证 / 定理证明 / 规约 | 进阶路径·形式化验证 | [LEARNING_PATHS 进阶路径](LEARNING_PATHS.md#进阶路径-intermediate-path)、[形式化验证](formal-model/core-concepts/formal-verification.md)、[L3_D08](L3_D08_测试标准模型.md) |
| 做数据/功能/交互建模入门 | 初学者路径 | [LEARNING_PATHS 初学者路径](LEARNING_PATHS.md#初学者路径-beginner-path)、[L2 元模型](L2_D01_交互元模型.md)～[L2_D08](L2_D08_测试元模型.md)、[L3 标准模型](L3_D01_交互标准模型.md) |
| 做金融/支付/风控合规 | 金融专项路径 | [LEARNING_PATHS 金融专项](LEARNING_PATHS.md#金融专项)、[L4_D91](L4_D91_FIN_行业索引与对标.md)、[金融 README](industry-model/finance-architecture/README.md) |
| 做 IoT/边缘/设备接入 | 物联网专项路径 | [LEARNING_PATHS 物联网专项](LEARNING_PATHS.md#物联网专项)、[L4_D92](L4_D92_IOT_行业索引与对标.md)、[L3_D07](L3_D07_控制调度标准模型.md)、[物联网 README](industry-model/iot-architecture/README.md) |
| 做 AI/ML 基础设施与 MLOps | AI 基础设施专项路径 | [LEARNING_PATHS AI 专项](LEARNING_PATHS.md#ai-基础设施专项)、[L4_D93](L4_D93_AI_行业索引与对标.md)、[AI README](industry-model/ai-infrastructure-architecture/README.md) |
| 做 Web3/智能合约/链上应用 | Web3 专项路径 | [LEARNING_PATHS Web3 专项](LEARNING_PATHS.md#web3-专项)、[L4_D94](L4_D94_W3_行业索引与对标.md)、[L3_D10](L3_D10_分布式模式标准模型.md)、[Web3 README](industry-model/web3-architecture/README.md) |

各路径与权威对标（课程/认证/标准）见 [AUTHORITY_ALIGNMENT_INDEX 第 3–5 节](reference/AUTHORITY_ALIGNMENT_INDEX.md)（名校课程、CNCF、行业与 L4 索引映射）。

**学完 X 再学 Y（建议顺序）**：先完成 [LEARNING_PATHS](LEARNING_PATHS.md) 阶段1（数据→功能→交互）再进入阶段2（测试/部署/监控）或行业专项；学完阶段2 后再用阶段3（DSL、验证）；进阶路径建议在初学者路径或行业专项阶段1 之后进行。详见 [LEARNING_PATHS 前置依赖关系图](LEARNING_PATHS.md#前置依赖关系图)。

**为何用 L2→L3→L4**：L2 提供与实现无关的基础概念，L3 绑定具体标准与实现形态，L4 做行业映射与案例；先 L2 再 L3 再 L4 可统一术语、便于对标并降低认知负荷。完整说明见 [README §2 核心模型体系](README.md#2-核心模型体系)。

### 新用户入门路径

- [📖 项目总览](README.md) - 了解整体架构和核心价值（建议分 2 次阅读：第一次至第 2 节「核心模型体系」，约 15 分钟）
- [🎯 快速开始指南](QUICK_START_GUIDE.md) - 快速上手使用
- [📚 学习路径](LEARNING_PATHS.md) - 按阶段学习；[复习检查点清单](learning/REVIEW_CHECKLIST.md) - 可勾选复习与自测
- [❓ 常见问题](FAQ.md) - 解决常见疑问
- [🔧 故障排除](TROUBLESHOOTING_GUIDE.md) - 解决技术问题

## 📚 核心文档体系

### L2 元模型 (基础概念)

| 文档 | 描述 | 状态 |
|------|------|------|
| [L2_D01_交互元模型](L2_D01_交互元模型.md) | API、协议、消息基础抽象 | ✅ 85% |
| [L2_D02_数据元模型](L2_D02_数据元模型.md) | 数据建模基础概念 | ✅ 80% |
| [L2_D03_功能元模型](L2_D03_功能元模型.md) | 功能建模核心要素 | ✅ 75% |
| [L2_D04_运行时元模型](L2_D04_运行时元模型.md) | 运行时环境建模 | ✅ 70% |
| [L2_D05_部署元模型](L2_D05_部署元模型.md) | 部署配置建模 | ✅ 65% |
| [L2_D06_监控元模型](L2_D06_监控元模型.md) | 监控体系建模 | ✅ 60% |
| [L2_D07_控制调度元模型](L2_D07_控制调度元模型.md) | 控制调度建模 | ✅ 70% |
| [L2_D08_测试元模型](L2_D08_测试元模型.md) | 测试体系建模 | ✅ 65% |

### L3 标准模型 (具体实现)

| 文档 | 描述 | 状态 |
|------|------|------|
| [L3_D01_交互标准模型](L3_D01_交互标准模型.md) | API、协议、消息标准 | ✅ 90% |
| [L3_D02_数据标准模型](L3_D02_数据标准模型.md) | 数据存储、查询标准 | ✅ 85% |
| [L3_D03_功能标准模型](L3_D03_功能标准模型.md) | 业务逻辑、规则引擎标准 | ✅ 95% |
| [L3_D04_运行时标准模型](L3_D04_运行时标准模型.md) | 容器、编排标准 | ✅ 80% |
| [L3_D05_部署标准模型](L3_D05_部署标准模型.md) | 部署、配置标准 | ✅ 75% |
| [L3_D06_监控标准模型](L3_D06_监控标准模型.md) | 监控、告警标准 | ✅ 70% |
| [L3_D07_控制调度标准模型](L3_D07_控制调度标准模型.md) | 调度、控制标准 | ✅ 65% |
| [L3_D08_测试标准模型](L3_D08_测试标准模型.md) | 测试、验证标准 | ✅ 85% |
| [L3_D09_CICD标准模型](L3_D09_CICD标准模型.md) | CI/CD流水线标准 | ✅ 80% |
| [L3_D10_分布式模式标准模型](L3_D10_分布式模式标准模型.md) | 分布式系统模式 | ✅ 80% |

### L4 行业索引 (应用案例)

| 文档 | 描述 | 状态 |
|------|------|------|
| [L4_D90_CN_行业索引与对标](L4_D90_CN_行业索引与对标.md) | 云原生行业对标 | ✅ 85% |
| [L4_D91_FIN_行业索引与对标](L4_D91_FIN_行业索引与对标.md) | 金融行业对标 | ✅ 80% |
| [L4_D92_IOT_行业索引与对标](L4_D92_IOT_行业索引与对标.md) | 物联网行业对标 | ✅ 80% |
| [L4_D93_AI_行业索引与对标](L4_D93_AI_行业索引与对标.md) | AI基础设施对标 | ✅ 85% |
| [L4_D94_W3_行业索引与对标](L4_D94_W3_行业索引与对标.md) | Web3行业对标 | ✅ 80% |

### L2↔L3 映射总表

- [📐 L2↔L3 映射总表](formal-model/alignment-L2-L3-matrix.md) - L2 元模型与 L3 标准模型的对象/属性/不变式对齐关系；审阅与维护 L2、L3 时请参见本表。更多入口见 [项目总览](README.md#-快速导航)。

## 🏗️ 核心概念体系

### 形式化建模基础

- [🌳 抽象语法树](formal-model/core-concepts/abstract-syntax-tree.md) - AST理论与应用
- [🤖 自动推理](formal-model/core-concepts/automated-reasoning.md) - 自动推理机制
- [⚙️ 代码生成](formal-model/core-concepts/code-generation.md) - 代码生成理论与技术
- [🔗 概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md) - 概念索引与关联
- [📝 领域特定语言](formal-model/core-concepts/domain-specific-language.md) - DSL设计
- [📊 形式化建模](formal-model/core-concepts/formal-modeling.md) - 形式化建模基础
- [✅ 形式化验证](formal-model/core-concepts/formal-verification.md) - 形式化验证方法
- [🏭 行业映射](formal-model/core-concepts/industry-mapping.md) - 行业映射关系
- [🕸️ 知识图谱](formal-model/core-concepts/knowledge-graph.md) - 知识图谱构建
- [🔄 模型驱动工程](formal-model/core-concepts/model-driven-engineering.md) - MDE理论与技术
- [🔄 模型转换](formal-model/core-concepts/model-transformation.md) - 模型转换技术
- [🔄 递归建模](formal-model/core-concepts/recursive-modeling.md) - 递归建模理论
- [🔍 语义分析](formal-model/core-concepts/semantic-analysis.md) - 语义分析技术

## 🏭 行业应用模型

### 云原生架构

- [☁️ 云原生概述](industry-model/cloud-native-architecture/README.md)
- [🌐 API网关](industry-model/cloud-native-architecture/api-gateway/)
- [🐳 容器编排](industry-model/cloud-native-architecture/container-orchestration/)
- [👁️ 可观测性](industry-model/cloud-native-architecture/observability/)
- [⚡ Serverless](industry-model/cloud-native-architecture/serverless/)
- [🕸️ 服务网格](industry-model/cloud-native-architecture/service-mesh/)

### AI基础设施

- [🤖 AI基础设施概述](industry-model/ai-infrastructure-architecture/README.md)
- [📊 数据管道](industry-model/ai-infrastructure-architecture/data-pipeline/)
- [🔄 分布式训练](industry-model/ai-infrastructure-architecture/distributed-training/)
- [🏪 特征库](industry-model/ai-infrastructure-architecture/feature-store/)
- [🔧 MLOps](industry-model/ai-infrastructure-architecture/mlops/)
- [🚀 模型服务](industry-model/ai-infrastructure-architecture/model-serving/)

### 金融架构

- [💰 金融架构概述](industry-model/finance-architecture/README.md)
- [🏦 核心银行](industry-model/finance-architecture/core-banking/)
- [💳 支付系统](API_DOCUMENTATION.md)
- [📈 风险管理](industry-model/finance-architecture/risk-management/)
- [📊 数据分析](industry-model/finance-architecture/data-analytics/)

### 物联网架构

- [🌐 物联网概述](industry-model/iot-architecture/README.md)
- [📱 设备接入](industry-model/iot-architecture/device-access/)
- [⚡ 边缘计算](industry-model/iot-architecture/edge-computing/)
- [📊 数据收集](industry-model/iot-architecture/data-collection/)

### Web3架构

- [🔗 Web3概述](industry-model/web3-architecture/README.md)
- [⛓️ 区块链基础](API_DOCUMENTATION.md)
- [🤝 智能合约](API_DOCUMENTATION.md)
- [🌉 跨链桥接](API_DOCUMENTATION.md)

## 🛠️ 工具与资源

### 文档管理工具

- [📋 文档索引生成器](../scripts/generate_doc_index.py)
- [📝 证据条目管理器](../scripts/evidence_manager.py)
- [📊 质量度量系统](../scripts/quality_metrics.py)
- [📄 证据条目模板生成器](../scripts/generate_evidence_template.py)
- [🔧 文档管理综合工具](../scripts/doc_manager.py)

### 项目管理文档

- [📈 项目状态](PROJECT_STATUS.md)
- [🗺️ 项目路线图](ROADMAP.md)
- [📋 实现指南](implementation-guide.md)
- [📊 文档完成度检查](DOCUMENT_COMPLETION_CHECK.md)
- [📝 变更日志](CHANGELOG.md)

### 社区与贡献

- [👥 社区准则](COMMUNITY_GUIDELINES.md)
- [🤝 贡献指南](CONTRIBUTING.md)
- [📄 许可证](LICENSE.md)
- [❓ 常见问题](FAQ.md)
- [🔧 故障排除](TROUBLESHOOTING_GUIDE.md)

## 🎯 按角色导航

### 👨‍💻 开发者

1. [快速开始指南](QUICK_START_GUIDE.md)
2. [API文档](API_DOCUMENTATION.md)
3. [代码示例](formal-model/core-concepts/code-generation.md)
4. [测试指南](formal-model/testing-model/theory.md)

### 🏗️ 架构师

1. [项目总览](README.md)
2. [L2元模型](L2_D01_交互元模型.md) - [L2_D08_测试元模型](L2_D08_测试元模型.md)
3. [L3标准模型](L3_D01_交互标准模型.md) - [L3_D10_分布式模式标准模型](L3_D10_分布式模式标准模型.md)
4. [行业应用](industry-model/)

### 🎓 研究者

1. [理论基础](formal-model/core-concepts/formal-modeling.md)
2. [形式化验证](formal-model/core-concepts/formal-verification.md)
3. [自动推理](formal-model/core-concepts/automated-reasoning.md)
4. [递归建模](formal-model/core-concepts/recursive-modeling.md)

### 🏭 行业专家

1. [行业映射](formal-model/core-concepts/industry-mapping.md)
2. [L4行业索引](L4_D90_CN_行业索引与对标.md) - [L4_D94_W3_行业索引与对标](L4_D94_W3_行业索引与对标.md)
3. [行业模型](industry-model/)
4. [最佳实践](practice-guides/)

## 🔍 搜索与索引

### 按概念查文档

下表便于按概念快速定位到 L2/L3、formal-model 理论及行业文档。完整概念与自测问句见 [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md)。

| 概念 | L2 元模型 | L3 标准模型 | formal-model 理论 | 行业文档示例 |
|------|-----------|-------------|-------------------|--------------|
| 交互 / API / 契约 | [L2_D01](L2_D01_交互元模型.md) | [L3_D01](L3_D01_交互标准模型.md) | [interaction-model/theory](formal-model/interaction-model/theory.md) | [云原生 API 网关](industry-model/cloud-native-architecture/api-gateway/) |
| 数据 | [L2_D02](L2_D02_数据元模型.md) | [L3_D02](L3_D02_数据标准模型.md) | [data-model/theory](formal-model/data-model/theory.md) | [金融核心银行](industry-model/finance-architecture/core-banking/)、[AI 特征库](industry-model/ai-infrastructure-architecture/feature-store/) |
| 功能 / 工作流 / 规则 | [L2_D03](L2_D03_功能元模型.md) | [L3_D03](L3_D03_功能标准模型.md) | [functional-model/theory](formal-model/functional-model/theory.md) | [Web3 智能合约](industry-model/web3-architecture/) |
| 运行时 / 容器 / 编排 | [L2_D04](L2_D04_运行时元模型.md) | [L3_D04](L3_D04_运行时标准模型.md) | [runtime-model/theory](formal-model/runtime-model/theory.md) | [云原生容器编排](industry-model/cloud-native-architecture/container-orchestration/)、[AI 分布式训练](industry-model/ai-infrastructure-architecture/distributed-training/) |
| 部署 / 发布 | [L2_D05](L2_D05_部署元模型.md) | [L3_D05](L3_D05_部署标准模型.md) | [deployment-model/theory](formal-model/deployment-model/theory.md) | [云原生 GitOps](industry-model/cloud-native-architecture/) |
| 监控 / 可观测性 | [L2_D06](L2_D06_监控元模型.md) | [L3_D06](L3_D06_监控标准模型.md) | [monitoring-model/theory](formal-model/monitoring-model/theory.md) | [云原生可观测性](industry-model/cloud-native-architecture/observability/) |
| 控制调度 | [L2_D07](L2_D07_控制调度元模型.md) | [L3_D07](L3_D07_控制调度标准模型.md) | — | [物联网边缘](industry-model/iot-architecture/edge-computing/) |
| 测试 / 验证 | [L2_D08](L2_D08_测试元模型.md) | [L3_D08](L3_D08_测试标准模型.md) | [testing-model/theory](formal-model/testing-model/theory.md) | [金融合规测试](industry-model/finance-architecture/) |
| CI/CD | — | [L3_D09](L3_D09_CICD标准模型.md) | [cicd-model/theory](formal-model/cicd-model/theory.md) | [云原生](industry-model/cloud-native-architecture/)、[AI MLOps](industry-model/ai-infrastructure-architecture/mlops/) |
| 分布式模式 | — | [L3_D10](L3_D10_分布式模式标准模型.md) | [distributed-pattern-model/theory](formal-model/distributed-pattern-model/theory.md) | [云原生服务网格](industry-model/cloud-native-architecture/service-mesh/)、[Web3](industry-model/web3-architecture/README.md) |

### 关键词索引

- **AST**: [抽象语法树](formal-model/core-concepts/abstract-syntax-tree.md)
- **DSL**: [领域特定语言](formal-model/core-concepts/domain-specific-language.md)
- **MDE**: [模型驱动工程](formal-model/core-concepts/model-driven-engineering.md)
- **API**: [交互建模](formal-model/interaction-model/theory.md)
- **数据**: [数据建模](formal-model/data-model/theory.md)
- **功能**: [功能建模](formal-model/functional-model/theory.md)
- **测试**: [测试建模](formal-model/testing-model/theory.md)
- **CI/CD**: [CI/CD建模](formal-model/cicd-model/theory.md)
- **分布式**: [分布式模式](formal-model/distributed-pattern-model/theory.md)

### 技术栈索引

- **云原生**: [云原生架构](industry-model/cloud-native-architecture/)
- **AI/ML**: [AI基础设施](industry-model/ai-infrastructure-architecture/)
- **金融**: [金融架构](industry-model/finance-architecture/)
- **IoT**: [物联网架构](industry-model/iot-architecture/)
- **Web3**: [Web3架构](industry-model/web3-architecture/)

## 📊 文档统计

- **总文档数**: 60+
- **总字数**: 300,000+
- **总行数**: 15,000+
- **完成度**: 85-95%
- **工具脚本**: 5个专业工具
- **证据条目**: 9个完整示例

## 🚀 快速链接

- [📖 项目主页](README.md)
- [🎯 快速开始](QUICK_START_GUIDE.md)
- [❓ 常见问题](FAQ.md)
- [🔧 故障排除](TROUBLESHOOTING_GUIDE.md)
- [📊 项目状态](PROJECT_STATUS.md)
- [🗺️ 路线图](ROADMAP.md)
- [🤝 贡献指南](CONTRIBUTING.md)
- [👥 社区准则](COMMUNITY_GUIDELINES.md)

---

*最后更新: 2024-12-19*
*维护者: Formal Framework Team*
