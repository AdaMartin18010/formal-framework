# 形式化框架学习路径 (Learning Paths)

> **最后更新**: 2025-02-02  
> **维护者**: Formal Framework Team

**本节要点**：（1）初学者 / 进阶 / 专家 / 行业专项四条路径及阶段划分；（2）每阶段检查点与间隔复习建议；（3）课程与 L2/L3 知识域对照及学完后可对接的权威资源。  
**预计阅读时间**：全文约 40–55 分钟；仅读「学习路径选择」+ 一条路径的总结约 10 分钟。  
**单次阅读建议**：请勿一次读完全文；每次连续学习 **25–40 分钟**，每个「阶段」拆成 **2–4 次**完成（每次 1–2 个知识点），完成当次后做该段的「检查点」自测再继续。

## 概述

本文档为形式化框架项目提供系统化的学习路径指南，帮助不同背景的学习者找到合适的学习起点和路径。本路径与 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 双向对应：各阶段总结中的「本阶段与权威对标」列出 1–2 条课程/标准，权威索引提供完整列表与链接；更新时请两处同步维护。

**阅读与复习建议**（降低认知负荷、配合间隔重复）：

- **单次学习建议时长**：每段连续学习 25–40 分钟为宜，避免一次读完整个阶段。
- **分段阅读**：每个「阶段」可拆成 2–4 次完成，每次 1–2 个知识点；完成一次后做该段的「检查点」自测，再进入下一段。
- **复习节奏**：阶段结束后按「复习检查点」回顾；建议间隔 1 天、1 周各回顾一次关键概念（可结合 [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md) 与 [术语表](knowledge-standards/glossary/GLOSSARY.md)）。可勾选清单见 [learning/REVIEW_CHECKLIST](learning/REVIEW_CHECKLIST.md)。学习科学依据与主动回忆、间隔重复的简要说明见 [learning/LEARNING_AND_REVIEW_TIPS](learning/LEARNING_AND_REVIEW_TIPS.md)。

### 5 分钟版（快速选路径）

| 路径 | 适合人群 | 入口 | 本路径与权威对标 |
|------|----------|------|------------------|
| 初学者 | 无形式化基础、需建立 L2/L3 概念 | 阶段1 → 形式化建模、数据/功能/交互理论 | [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节：Stanford CS 103/210、MIT 6.042、Berkeley CS 70/169、CMU 15-413 |
| 进阶 | 有基础、深入验证与建模 | 阶段1 → AST、自动推理、时序逻辑、程序验证 | 第 3 节：Stanford CS 256/357S、CMU 15-414/15-311、Berkeley EECS 219C、UW CSE 507、清华形式化；第 2 节：IEEE 1012、TLA+、Alloy |
| 专家 | 标准制定、工具开发、理论研究 | 理论研究 → 标准制定参与 → 工具开发 | 学术会议（CAV、FM、ICSE）；ISO/IEC JTC1/SC7、OMG |
| 行业专项 | 云原生/AI/金融/IoT/Web3 | 阶段1 后 → 对应 L3 + 行业 README | 第 4–5 节：CNCF 认证、各 L4 索引与行业标准 |

## 前置依赖关系图

建议按箭头顺序学习；行业专项可在阶段1 完成后分支到对应 L3 与行业 README。

```mermaid
flowchart LR
  subgraph core [核心建模]
    Data[数据模型]
    Func[功能模型]
    Interact[交互模型]
  end
  Data --> Func
  Func --> Interact
  Interact --> Runtime[运行时模型]
  Runtime --> Deploy[部署模型]
  Deploy --> Monitor[监控模型]
  Monitor --> Test[测试模型]
  Test --> CICD[CI/CD模型]
  CICD --> Dist[分布式模式模型]
  Dist --> Industry[行业模型]
```

与权威课程对应见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节；形式化语言按场景选型见 [FORMAL_SPEC_LANGUAGES](reference/FORMAL_SPEC_LANGUAGES.md) §2.1。

- **初学者**：按 数据 → 功能 → 交互 → 测试/部署/监控 顺序；详见下方「初学者路径」。
- **行业专项**：完成阶段1（数据、功能、交互）后，可跳至 [云原生专项](#云原生专项)、[AI 基础设施专项](#ai-基础设施专项) 等。

## 学习路径选择

根据您的背景和目标，选择合适的学习路径：

- **初学者路径**：适合没有形式化方法基础的开发者
- **进阶路径**：适合有一定理论基础，希望深入学习的研究者
- **专家路径**：适合形式化方法专家，希望参与标准制定和工具开发

## 初学者路径 (Beginner Path)

### 目标

掌握形式化方法的基本概念，能够理解和使用形式化模型进行简单的系统建模。

### 前置要求

- 基本的编程经验（任一编程语言）
- 基础的数学知识（集合、逻辑）
- 软件工程基础知识

### 学习路径

#### 阶段1：基础概念（2-3周）

**目标**：理解形式化方法的基本概念和思想

**本节要点**：形式化建模思想；L2 元模型中数据/功能/交互三块的关系；模型与代码/部署的对应。  
**前置概念**：无（建议具备基本编程与集合/逻辑常识）。  
**间隔复习**：学完本阶段后先回顾「形式化建模基础」再进入阶段2；阶段2 中遇到 L3 时回头对照 L2 对应元模型。

1. **形式化建模基础**
   - 📖 [形式化建模](formal-model/core-concepts/formal-modeling.md)
   - ⏱️ 学习时间：3-4小时
   - ✅ 检查点：能够理解形式化建模的基本思想

2. **数据模型**
   - 📖 [数据模型理论](formal-model/data-model/theory.md)
   - ⏱️ 学习时间：2-3小时
   - ✅ 检查点：能够设计简单的数据模型

3. **功能模型**
   - 📖 [功能模型理论](formal-model/functional-model/theory.md)
   - ⏱️ 学习时间：2-3小时
   - ✅ 检查点：能够设计简单的业务逻辑模型

4. **交互模型**
   - 📖 [交互模型理论](formal-model/interaction-model/theory.md)
   - ⏱️ 学习时间：2-3小时
   - ✅ 检查点：能够设计简单的API模型

**阶段1总结**：
- 总学习时间：约10-13小时
- 完成标志：能够理解L2元模型的基本概念
- **为何本顺序**：数据 → 功能 → 交互，因交互层契约依赖数据实体与功能行为，先建数据与功能再定义接口与消息更易保持一致。
- **掌握度标志**：能向他人用 3 句话解释「形式化建模 + 数据/功能/交互三块分别解决什么」；或能完成 [REVIEW_CHECKLIST](learning/REVIEW_CHECKLIST.md) 阶段1 所有检查点且不需回看。
- **本阶段与权威对标**：对应 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节中 Stanford CS 103、MIT 6.042、Berkeley CS 70（数学与逻辑基础）及 L2 元模型概念。

**阶段1 复习检查点**（自测后进入阶段2）：
- 能否用一句话说明「形式化建模」在本框架中的含义？→ 回顾 [形式化建模](formal-model/core-concepts/formal-modeling.md)
- 数据、功能、交互三个元模型分别解决什么问题？→ 回顾 [数据](formal-model/data-model/theory.md)、[功能](formal-model/functional-model/theory.md)、[交互](formal-model/interaction-model/theory.md) 理论
- L2 与「代码/部署」的对应关系是否清晰？→ 见 [docs/README](README.md) 模型体系与递归扩展路径

**间隔归来建议**：若间隔 3–7 天后回来继续学习，建议先完成上列 3 条复习检查点中至少 2 条自测（先写再对），再进入阶段2。

#### 阶段2：实践应用（2-3周）

**本节要点**：测试/部署/监控模型在 L3 中的位置；行业案例如何映射到 L3。  
**前置概念**：阶段1 完成（数据、功能、交互模型）。  
**本阶段对应文档建议**：阅读 L3 长文档（如 [L3_D08](L3_D08_测试标准模型.md)、[L3_D05](L3_D05_部署标准模型.md)、[L3_D06](L3_D06_监控标准模型.md)）时，可按各文档顶部「单次阅读建议」分 2–4 次完成，每次 1–2 节。  
**间隔复习**：学完「行业案例学习」后，可先做一次小结：六个云原生案例分别对应哪些 L3 模型，再进入阶段3。

1. **测试模型**
   - 📖 [测试模型理论](formal-model/testing-model/theory.md)
   - ⏱️ 学习时间：2小时
   - ✅ 检查点：能够设计测试用例模型

2. **部署模型**
   - 📖 [部署模型理论](formal-model/deployment-model/theory.md)
   - ⏱️ 学习时间：2-3小时
   - ✅ 检查点：能够设计部署配置模型

3. **监控模型**
   - 📖 [监控模型理论](formal-model/monitoring-model/theory.md)
   - ⏱️ 学习时间：2-3小时
   - ✅ 检查点：能够设计监控指标模型

4. **行业案例学习**
   - 📖 [云原生架构案例](industry-model/cloud-native-architecture/)（建议分 2 次阅读：第一次至「本行业与通用模型对照」与案例一、二；第二次案例三至六）
   - ⏱️ 学习时间：3-4小时
   - ✅ 检查点：能够理解行业模型的应用

**阶段2总结**：
- 总学习时间：约9-12小时
- 完成标志：能够应用形式化模型解决实际问题
- **为何本顺序**：测试/部署/监控在 L3 中依赖阶段1 的数据/功能/交互；先掌握核心建模再学运维与质量保障，符合「设计→实现→验证→部署」的工程顺序。
- **掌握度标志**：能说出测试/部署/监控在 L3 中对应的文档，并能举一个行业模型映射到通用模型的例子；或完成 REVIEW_CHECKLIST 阶段2 所有检查点且不需回看。
- **本阶段与权威对标**：对应 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节中 Stanford CS 210、CMU 15-413、Berkeley CS 169（软件工程与实践）及 L3 标准模型、行业案例。

**阶段2 复习检查点**（自测后进入阶段3）：
- 测试、部署、监控模型在 L3 中分别对应哪些文档？→ 回顾 [L3_D08](L3_D08_测试标准模型.md)、[L3_D05](L3_D05_部署标准模型.md)、[L3_D06](L3_D06_监控标准模型.md)
- 云原生六个案例各自对应哪些 L3 模型？→ 见 [云原生 README](industry-model/cloud-native-architecture/README.md) 案例与 L3 映射
- 能否举一个「行业模型映射到通用模型」的例子？→ 见 [docs/README 第 5 节](README.md#5-行业映射关系)

**间隔归来建议**：若间隔 3–7 天后回来继续学习，建议先完成上列 3 条复习检查点中至少 2 条自测（先写再对），再进入阶段3。

#### 阶段3：工具使用（1-2周）

**本节要点**：DSL 与 AST 的关系；验证在质量门禁中的角色。  
**前置概念**：阶段1、阶段2；建议已接触过至少一个行业案例。  
**间隔复习**：学完本阶段后可回顾 [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md) 与 [术语表](knowledge-standards/glossary/GLOSSARY.md)，再选择进阶或行业专项路径。

1. **DSL设计**
   - 📖 [领域特定语言](formal-model/core-concepts/domain-specific-language.md)
   - ⏱️ 学习时间：3-4小时
   - ✅ 检查点：能够设计简单的DSL

2. **模型验证**
   - 📖 [形式化验证基础](formal-model/core-concepts/formal-verification.md)
   - ⏱️ 学习时间：2-3小时
   - ✅ 检查点：能够使用基本验证工具

**阶段3总结**：
- 总学习时间：约5-7小时
- 完成标志：能够使用工具进行建模和验证
- **为何本顺序**：DSL 与验证建立在阶段1–2 的模型概念之上；先有模型再谈语言与验证工具，便于理解工具在质量门禁中的角色。
- **掌握度标志**：能说明 DSL 与 AST 的关系、验证在质量门禁中的角色；或完成 REVIEW_CHECKLIST 阶段3 所有检查点且不需回看。
- **本阶段与权威对标**：对应 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 2–3 节中 DSL/验证相关课程（如 MIT 6.035、Berkeley CS 164）及 [FORMAL_SPEC_LANGUAGES](reference/FORMAL_SPEC_LANGUAGES.md)。

**阶段3 复习检查点**（自测后选择进阶或行业专项）：
- DSL 与 AST 的关系是什么？→ 回顾 [领域特定语言](formal-model/core-concepts/domain-specific-language.md)、[形式化验证基础](formal-model/core-concepts/formal-verification.md)
- 验证在质量门禁中扮演什么角色？→ 见 [QUALITY_STANDARDS](QUALITY_STANDARDS.md)、[EXPERT_REVIEW_SYSTEM](EXPERT_REVIEW_SYSTEM.md)
- 建议再浏览一遍 [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md) 与 [术语表](knowledge-standards/glossary/GLOSSARY.md)，再选进阶或行业专项路径。

**间隔归来建议**：若间隔 3–7 天后回来，建议先完成上列前 2 条自测（先写再对），再选择进阶路径或行业专项路径。

### 初学者路径总结

- **总学习时间**：约24-32小时（3-4周）
- **完成标志**：能够独立完成简单的形式化建模任务
- **下一步**：进入进阶路径或**行业专项路径**（见下）或在实际项目中应用
- **推荐复习间隔**：阶段内每 1 天回顾当日要点；阶段结束后 1 周、1 月各做一次总复习（可结合检查点与 [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md)）。
- **学完后可对接的权威资源**：课程见 [权威对标总索引](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节（如 Stanford CS 103/210、MIT 6.042/6.170、Berkeley CS 70/169、CMU 15-413）；认证与培训见第 4 节（CNCF 等）。

## 行业专项路径 (Industry-Focused Paths)

在完成**阶段1（基础概念）**后，可按行业兴趣选择以下路径之一；每条路径先读对应 L3 文档，再读该行业 README 与指定案例。

### 云原生专项

- **前置**：阶段1；建议先读 [L3_D04 运行时标准模型](L3_D04_运行时标准模型.md)、[L3_D01 交互标准模型](L3_D01_交互标准模型.md)、[L3_D05 部署标准模型](L3_D05_部署标准模型.md)、[L3_D06 监控标准模型](L3_D06_监控标准模型.md)、[L3_D09 CI/CD 标准模型](L3_D09_CICD标准模型.md)。
- **阅读顺序**：[云原生行业模型 README](industry-model/cloud-native-architecture/README.md) → 案例一（K8s）→ 案例二（Service Mesh）→ 案例三（GitOps）→ 案例四（可观测性）→ 案例五（Serverless）→ 案例六（API 网关）。
- **5 分钟版**：README 中「本行业与通用模型对照小结」表 + 「与 CNCF 课程/认证知识域映射」表。
- **权威对标**：[AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 中 CNCF 认证与课程。

### AI 基础设施专项

- **前置**：阶段1；建议先读 [L3_D02 数据标准模型](L3_D02_数据标准模型.md)、[L3_D04 运行时标准模型](L3_D04_运行时标准模型.md)、[L3_D06 监控标准模型](L3_D06_监控标准模型.md)、[L3_D09 CI/CD 标准模型](L3_D09_CICD标准模型.md)。
- **阅读顺序**：[AI 基础设施行业模型 README](industry-model/ai-infrastructure-architecture/README.md) 及各子模块 theory/dsl-draft。
- **5 分钟版**：README 中「本行业与通用模型对照」或架构总览表 + [权威对标总索引](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 5 节「行业与 L4 索引映射」中 AI 基础设施行及 L4_D93 对应认证/标准。
- **权威对标**：[AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 中 AI/ML 相关标准与项目；[L4_D93_AI_行业索引与对标](L4_D93_AI_行业索引与对标.md)。

### 金融专项

- **前置**：阶段1；建议先读 [L3_D01 交互标准模型](L3_D01_交互标准模型.md)、[L3_D02 数据标准模型](L3_D02_数据标准模型.md)、[L3_D03 功能标准模型](L3_D03_功能标准模型.md)、[L3_D08 测试标准模型](L3_D08_测试标准模型.md)。
- **阅读顺序**：[金融行业模型 README](industry-model/finance-architecture/README.md) 及核心银行/支付/风控等子模块。
- **5 分钟版**：README 中「本行业与通用模型对照」或行业对标小结表 + [权威对标总索引](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 5 节「行业与 L4 索引映射」中金融行及 L4_D91 对应标准（PCI-DSS、Open Banking、巴塞尔）。
- **权威对标**：[AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)；[L4_D91_FIN_行业索引与对标](L4_D91_FIN_行业索引与对标.md)；PCI-DSS、Open Banking、巴塞尔等。

### 物联网专项

- **前置**：阶段1；建议先读 [L3_D04 运行时标准模型](L3_D04_运行时标准模型.md)、[L3_D07 控制调度标准模型](L3_D07_控制调度标准模型.md)、[L3_D06 监控标准模型](L3_D06_监控标准模型.md)。
- **阅读顺序**：[物联网行业模型 README](industry-model/iot-architecture/README.md) 及设备接入/边缘计算等子模块。
- **5 分钟版**：README 中「本行业与通用模型对照」或技术栈表 + [权威对标总索引](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 5 节「行业与 L4 索引映射」中物联网行及 L4_D92 对应项目（EdgeX、KubeEdge、OPC UA、LwM2M）。
- **权威对标**：[AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)；[L4_D92_IOT_行业索引与对标](L4_D92_IOT_行业索引与对标.md)；EdgeX、KubeEdge、OPC UA 等。

### Web3 专项

- **前置**：阶段1；建议先读 [L3_D01 交互标准模型](L3_D01_交互标准模型.md)、[L3_D03 功能标准模型](L3_D03_功能标准模型.md)、[L3_D10 分布式模式标准模型](L3_D10_分布式模式标准模型.md)。
- **阅读顺序**：[Web3 行业模型 README](industry-model/web3-architecture/README.md) 及智能合约/共识等子模块。
- **5 分钟版**：README 中「本行业与通用模型对照」或架构小结表 + [权威对标总索引](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 5 节「行业与 L4 索引映射」中 Web3 行及 L4_D94 对应项目（Ethereum、Solidity、Chainlink、Polkadot、IPFS、DID/VC）。
- **权威对标**：[AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)；[L4_D94_W3_行业索引与对标](L4_D94_W3_行业索引与对标.md)；Ethereum、Solidity、Chainlink 等。

**行业专项路径 — 复习节奏建议**：每完成约 2 个案例或 1 个子模块后，建议回头回顾该行业「前置」中列出的 L3 文档（如云原生回顾 L3_D04/L3_D01/L3_D05/L3_D06/L3_D09），以巩固通用模型与行业映射关系。

**本路径与权威对标对应表**：学完任一条行业专项路径后，可对照 [AUTHORITY_ALIGNMENT_INDEX 第 3 节（名校课程）](reference/AUTHORITY_ALIGNMENT_INDEX.md#3-名校课程与教材)、[第 4 节（云原生与 CNCF）](reference/AUTHORITY_ALIGNMENT_INDEX.md#4-云原生与-cncf-资源)、[第 5 节（行业与 L4 索引映射）](reference/AUTHORITY_ALIGNMENT_INDEX.md#5-行业与-l4-索引映射) 核对课程/认证/标准与 L2/L3 知识点的对应，便于「学完即可对标」。

## 进阶路径 (Intermediate Path)

**形式化验证方向主推课程**（与 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节一致）：Stanford CS 357S（2024-2025 Winter，SAT/SMT、定理证明、fuzzing）、CMU 15-414（Spring 2024，Why3、演绎验证）；选课时可优先对照上述课程大纲。

### 目标

深入理解形式化方法的理论基础，掌握高级建模技术和验证方法。

### 前置要求

- 完成初学者路径或同等水平
- 扎实的数学基础（离散数学、逻辑学）
- 对形式化方法有浓厚兴趣

### 学习路径

#### 阶段1：理论基础深化（3-4周）

**目标**：深入理解形式化方法的数学基础

1. **抽象语法树**
   - 📖 [抽象语法树理论](formal-model/core-concepts/abstract-syntax-tree.md)
   - ⏱️ 学习时间：3-4小时
   - ✅ 检查点：能够设计和实现AST

2. **自动推理**
   - 📖 [自动推理机制](formal-model/core-concepts/automated-reasoning.md)
   - ⏱️ 学习时间：4-5小时
   - ✅ 检查点：能够理解SAT/SMT求解器原理

3. **时序逻辑**
   - 📖 [时序逻辑理论](formal-model/core-concepts/temporal-logic.md)
   - ⏱️ 学习时间：4-5小时
   - ✅ 检查点：能够使用LTL/CTL描述系统性质

4. **程序验证**
   - 📖 [程序验证理论](formal-model/core-concepts/program-verification.md)
   - ⏱️ 学习时间：5-6小时
   - ✅ 检查点：能够使用Hoare逻辑进行程序证明

**阶段1总结**：
- 总学习时间：约16-20小时
- 完成标志：掌握形式化方法的理论基础
- **为何本顺序**：AST 与自动推理为时序逻辑与程序验证提供语法与推理基础；先打牢基础再学 LTL/CTL 与 Hoare 逻辑。
- **掌握度标志**：能设计 AST、理解 SAT/SMT 原理、用 LTL/CTL 描述性质或用 Hoare 逻辑做程序证明；或完成进阶路径阶段1 检查点且不需回看。
- **本阶段与权威对标**：形式化语言按场景选型（结构/数据→Alloy、并发/分布式→TLA+、规约与证明→Why3/Z/VDM）见 [FORMAL_SPEC_LANGUAGES](reference/FORMAL_SPEC_LANGUAGES.md) §2.1，便于后续阶段「学完即可选型」；课程与 L2/L3 知识点见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节。

**阶段1 复习检查点**（自测后进入阶段2）：AST 与 DSL 的关系？SAT/SMT 在本框架中对应哪些验证活动？LTL/CTL 与 L2 行为规约的对应？形式化语言选型（Alloy/TLA+/Why3）各适用什么场景？→ 见 [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md)、[FORMAL_SPEC_LANGUAGES](reference/FORMAL_SPEC_LANGUAGES.md) §2.1。

**间隔归来建议**：若间隔 3–7 天后回来继续学习，建议先完成上列复习检查点中至少 2 条自测（先写再对），再进入阶段2。

#### 阶段2：高级建模技术（3-4周）

**目标**：掌握复杂系统的建模技术

1. **模型驱动工程**
   - 📖 [模型驱动工程](formal-model/core-concepts/model-driven-engineering.md)
   - ⏱️ 学习时间：4-5小时
   - ✅ 检查点：能够设计MDE流程

2. **模型转换**
   - 📖 [模型转换](formal-model/core-concepts/model-transformation.md)
   - ⏱️ 学习时间：3-4小时
   - ✅ 检查点：能够实现模型转换规则

3. **递归建模**
   - 📖 [递归建模](formal-model/core-concepts/recursive-modeling.md)
   - ⏱️ 学习时间：4-5小时
   - ✅ 检查点：能够设计递归模型结构

4. **知识图谱**
   - 📖 [知识图谱](formal-model/core-concepts/knowledge-graph.md)
   - ⏱️ 学习时间：3-4小时
   - ✅ 检查点：能够构建知识图谱

**阶段2总结**：
- 总学习时间：约14-18小时
- 完成标志：掌握高级建模技术
- **为何本顺序**：MDE、模型转换与递归建模依赖阶段1 的形式化基础；知识图谱作为综合应用放在最后。
- **掌握度标志**：能设计 MDE 流程、实现模型转换规则、设计递归模型结构或构建知识图谱；或完成进阶路径阶段2 检查点且不需回看。
- **本阶段与权威对标**：L2/L3 映射与行业模型见 [alignment-L2-L3-matrix](formal-model/alignment-L2-L3-matrix.md)；课程与标准见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节、第 2 节。

**阶段2 复习检查点**（自测后进入阶段3）：MDE 与 L2/L3 的对应？模型转换在 theory-enhancement 中的位置？→ 见 [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md)、[alignment-L2-L3-matrix](formal-model/alignment-L2-L3-matrix.md)。

**间隔归来建议**：若间隔 3–7 天后回来继续学习，建议先完成上列复习检查点中至少 2 条自测（先写再对），再进入阶段3。

#### 阶段3：验证工具精通（2-3周）

**目标**：精通形式化验证工具的使用

1. **模型检验工具**
   - 📖 [时序逻辑工具指南](formal-model/core-concepts/temporal-logic.md#tla工具使用)
   - 🔧 TLA+ Toolbox实践
   - 🔧 SPIN工具实践
   - ⏱️ 学习时间：4-5小时
   - ✅ 检查点：能够使用工具验证系统性质

2. **定理证明工具**
   - 📖 [程序验证工具](formal-model/core-concepts/program-verification.md#定理证明工具)
   - 🔧 Coq实践
   - 🔧 Isabelle实践
   - ⏱️ 学习时间：5-6小时
   - ✅ 检查点：能够使用工具证明程序正确性

3. **行业模型深入**
   - 📖 [金融架构](industry-model/finance-architecture/)
   - 📖 [IoT架构](industry-model/iot-architecture/)
   - 📖 [Web3架构](industry-model/web3-architecture/)
   - ⏱️ 学习时间：6-8小时
   - ✅ 检查点：能够设计行业特定模型

**阶段3总结**：
- 总学习时间：约15-19小时
- 完成标志：精通验证工具使用
- **为何本顺序**：模型检验与定理证明工具对应阶段1 的时序逻辑与程序验证；行业模型深入将 L2/L3 应用到具体领域，放在最后综合运用。
- **掌握度标志**：能使用 TLA+/SPIN 或 Coq/Isabelle 验证或证明，或设计行业特定模型；或完成进阶路径阶段3 检查点且不需回看。
- **本阶段与权威对标**：形式化语言按场景选型（结构/数据→Alloy、并发/分布式→TLA+、规约与证明→Why3/Z/VDM）及与课程对应见 [FORMAL_SPEC_LANGUAGES](reference/FORMAL_SPEC_LANGUAGES.md) §2.1，便于「学完即可选型」；主推课程（Stanford CS 357S、CMU 15-414 等）见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节。

**阶段3 复习检查点**（自测后选择专家路径或项目）：TLA+ 与 Alloy 的选型场景？Why3 与 CMU 15-414 的对应？→ 见 [FORMAL_SPEC_LANGUAGES](reference/FORMAL_SPEC_LANGUAGES.md) §2.1、[AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节。

**间隔归来建议**：若间隔 3–7 天后回来，建议先完成上列复习检查点中至少 2 条自测（先写再对），再进入专家路径或实际项目。

### 进阶路径总结

- **总学习时间**：约45-57小时（8-11周）
- **完成标志**：能够独立进行复杂系统的形式化建模和验证
- **下一步**：进入专家路径或参与实际项目
- **学完后可对接的权威资源**：形式化验证与综合见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节（**主推**：Stanford CS 357S、CMU 15-414；另 Stanford CS 256、Berkeley EECS 219C、UW CSE 507、清华形式化建模等）；标准见第 2 节（IEEE 1012、TLA+、Alloy 等）。

## 专家路径 (Expert Path)

### 目标

成为形式化方法领域的专家，能够参与标准制定、工具开发和理论研究。

### 前置要求

- 完成进阶路径或同等水平
- 深厚的数学和逻辑学基础
- 丰富的实践经验
- 对形式化方法有深入研究兴趣

### 学习路径

#### 阶段1：理论研究（4-6周）

**目标**：深入理解形式化方法的理论前沿

1. **形式化方法前沿**
   - 📖 阅读顶级会议论文（FM、ICSE、ASE等）
   - 📖 研究最新形式化方法
   - ⏱️ 学习时间：10-15小时
   - ✅ 检查点：能够理解前沿理论

2. **标准制定参与**
   - 📖 [ISO/IEC标准对齐](knowledge-standards/)
   - 📖 [IEEE标准对齐](knowledge-standards/)
   - ⏱️ 学习时间：8-10小时
   - ✅ 检查点：能够参与标准讨论
   - **说明**：标准制定参与需结合 [ISO/IEC JTC1/SC7](https://www.iso.org/committee/45144.html)、[OMG](https://www.omg.org/) 等实际流程与参与路径，避免仅停留在「对齐标准」而忽视实际参与方式。具体参与方式（如 SC7 通过各国标准 body 以 P-member/O-member 参与、OMG 会员与技术提案流程）见 [reference/README](reference/README.md) 中的「标准参与方式」；权威机构入口见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 2.1 节。

3. **工具开发**
   - 📖 研究现有工具源码
   - 📖 设计新工具架构
   - ⏱️ 学习时间：15-20小时
   - ✅ 检查点：能够开发形式化工具

**阶段1总结**：
- 总学习时间：约33-45小时
- 完成标志：掌握理论前沿和工具开发
- **为何本顺序**：理论研究与标准对齐为工具开发提供目标与约束；先理解前沿与标准再开发工具，便于与社区与规范一致。

**阶段1 复习检查点**（自测后进入阶段2）：近期 FM/CAV/ICSE 中与 L2/L3 相关的议题？ISO/IEC JTC1/SC7、OMG 与本框架的对应？→ 见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)。

**间隔归来建议**：若间隔 3–7 天后回来继续学习，建议先完成上列复习检查点中至少 2 条自测（先写再对），再进入阶段2。

#### 阶段2：实践创新（4-6周）

**目标**：在实际项目中创新应用形式化方法

1. **复杂系统建模**
   - 📖 设计大型系统的形式化模型
   - 📖 实现模型验证流程
   - ⏱️ 学习时间：20-30小时
   - ✅ 检查点：能够建模复杂系统

2. **方法创新**
   - 📖 研究新的建模方法
   - 📖 提出改进方案
   - ⏱️ 学习时间：15-20小时
   - ✅ 检查点：能够提出创新方法

3. **社区贡献**
   - 📖 参与开源项目
   - 📖 撰写技术文章
   - 📖 指导初学者
   - ⏱️ 学习时间：持续
   - ✅ 检查点：能够贡献社区

**阶段2总结**：
- 总学习时间：约35-50小时
- 完成标志：能够创新应用形式化方法
- **为何本顺序**：复杂系统建模将阶段1 的理论与工具落地；方法创新与社区贡献在实践基础上更有针对性。

**阶段2 复习检查点**（自测后进入阶段3）：本阶段建模与 L3 各标准模型的对应？创新点如何与 evidence、权威标准对齐？→ 见 [alignment-L2-L3-matrix](formal-model/alignment-L2-L3-matrix.md)、[evidence/README](evidence/README.md)。

**间隔归来建议**：若间隔 3–7 天后回来继续学习，建议先完成上列复习检查点中至少 2 条自测（先写再对），再进入阶段3。

#### 阶段3：知识传播（持续）

**目标**：传播形式化方法知识，推动领域发展

1. **教学与培训**
   - 📖 设计培训课程
   - 📖 进行技术分享
   - ⏱️ 学习时间：持续
   - ✅ 检查点：能够有效教学

2. **标准制定**
   - 📖 参与国际标准制定
   - 📖 推动行业标准
   - ⏱️ 学习时间：持续
   - ✅ 检查点：能够影响标准制定

3. **研究发表**
   - 📖 发表研究论文
   - 📖 参与学术会议
   - ⏱️ 学习时间：持续
   - ✅ 检查点：能够发表研究成果

**阶段3总结**：
- 总学习时间：持续
- 完成标志：成为领域专家
- **为何本顺序**：教学与标准制定、研究发表建立在阶段1–2 的理论与实践之上；知识传播是专家路径的持续出口。

**阶段3 复习检查点**（持续）：近期 12207/15288/42010 等标准修订？CNCF 或课程大纲变更？→ 见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)、[PENDING_TRACKING_STANDARDS_COURSES](reference/PENDING_TRACKING_STANDARDS_COURSES.md)。

**间隔归来建议**：本阶段为持续学习；若间隔较长时间后回来，建议先完成上列复习检查点（核对标准/会议动态），再继续实践创新或知识传播。

### 专家路径总结

- **总学习时间**：约68-95小时（12-18周）+ 持续学习
- **完成标志**：成为形式化方法领域的专家
- **下一步**：持续研究和创新
- **学完后可对接的权威资源**：学术会议（CAV、FM、ICSE）；标准参与（ISO/IEC JTC1/SC7、OMG）；教材与论文见下方「学习资源」及 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)。

## 课程与 L2/L3 知识域对照表

按主题选课时可参考下表（完整课程列表与链接见 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节）：

| 知识域 | 本框架映射 | 推荐课程/认证示例 |
|--------|------------|-------------------|
| 形式化验证、规约、定理证明 | L2 形式化、L3_D08 测试 | Stanford CS 256/357S、CMU 15-414、Berkeley EECS 219C、UW CSE 507 |
| 逻辑、类型论、DSL | L2 各元模型、theory-enhancement | CMU 15-311/15-312、Stanford CS 242、MIT 6.035、Berkeley CS 164 |
| 分布式、一致性、容错 | L3_D10 分布式模式、L4 各行业 | ETH Distributed Systems、[evidence/COURSE-ETH-DS](evidence/COURSE-ETH-DS.md) |
| 软件工程、CI/CD、实践 | L3 各标准模型、L3_D09 | Stanford CS 210、CMU 15-413、Berkeley CS 169、上交软件工程 |
| 云原生、容器、可观测性 | L4_D90、L3_D04/D05/D06/D09 | CNCF 认证（CKA、CKAD、PCA、ICA、CGOA）、CNCF Training |

## 学习资源

### 推荐书籍

1. **形式化方法基础**
   - *Formal Methods: An Introduction* by D. Gries
   - *Logic in Computer Science* by M. Huth and M. Ryan

2. **程序验证**
   - *The Science of Programming* by D. Gries
   - *Software Abstractions* by D. Jackson

3. **模型检验**
   - *Principles of Model Checking* by C. Baier and J. Katoen
   - *Model Checking* by E. M. Clarke et al.

### 在线资源

1. **课程**
   - Stanford CS256: Formal Methods for Reactive Systems
   - CMU 15-414: Automated Program Verification
   - MIT 6.883: Program Analysis

2. **工具文档**
   - [TLA+官方文档](https://lamport.azurewebsites.net/tla/tla.html)
   - [Coq官方文档](https://coq.inria.fr/)
   - [SPIN官方文档](http://spinroot.com/spin/Doc/)

3. **中文与国内课程（权威对标）**
   - 完整课程列表与大纲链接见 [权威对标总索引](reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节。
   - 清华大学：软件工程建模与形式化方法（M510006B / 软件学院）；软件分析与验证、模型驱动的软件开发等。
   - 上海交通大学：软件工程原理与实践（架构与工程实践）。
   - 华盛顿大学：CSE 507 Computer-Aided Reasoning for Software Engineering（SAT/SMT、定理证明、模型检验）。

### 社区资源

1. **论坛**
   - [TLA+ Google Group](https://groups.google.com/forum/#!forum/tlaplus)
   - [Coq Discourse](https://coq.discourse.group/)

2. **会议**
   - FM (Formal Methods)
   - CAV (Computer Aided Verification)
   - ICSE (International Conference on Software Engineering)

## 学习建议

### 通用建议

1. **循序渐进**：按照学习路径逐步深入
2. **理论实践结合**：理论学习后立即实践
3. **持续复习**：定期回顾已学内容
4. **社区参与**：积极参与社区讨论

### 针对不同路径的建议

#### 初学者

- 不要急于求成，扎实掌握基础
- 多做练习，加深理解
- 遇到问题及时寻求帮助

#### 进阶学习者

- 深入理解理论，不要停留在表面
- 多使用工具，积累实践经验
- 阅读相关论文，了解前沿

#### 专家

- 关注理论前沿，持续学习
- 积极参与标准制定和工具开发
- 传播知识，推动领域发展

## 学习检查清单

### 初学者检查清单

- [ ] 理解形式化建模的基本概念
- [ ] 能够设计简单的数据模型
- [ ] 能够设计简单的功能模型
- [ ] 能够使用基本的验证工具
- [ ] 能够理解行业模型的应用

### 进阶检查清单

- [ ] 掌握形式化方法的理论基础
- [ ] 能够使用时序逻辑描述系统性质
- [ ] 能够使用Hoare逻辑进行程序证明
- [ ] 能够使用模型检验工具
- [ ] 能够设计复杂的系统模型

### 专家检查清单

- [ ] 理解形式化方法的前沿理论
- [ ] 能够开发形式化工具
- [ ] 能够参与标准制定
- [ ] 能够指导他人学习
- [ ] 能够发表研究成果

## 局限与边界

- **本框架侧重**：软件工程与系统建模的形式化与行业映射，提供可验证、可追溯的知识规范与模型设计；**不替代**具体实现、代码生成或运行时系统。
- **形式化覆盖**：以 L2/L3 规格、不变式、验证与行业对标为主；**不覆盖**所有形式化理论（如深度类型论、同伦论、范畴论高阶应用等）。
- **学习路径目标**：以「能用、能教、能对标」为主——能运用模型进行设计与评审、能向他人解释、能与权威标准/课程对照；**不追求**数学完备性或定理证明的全面形式化。

## 相关文档

- [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md)
- [术语表](knowledge-standards/glossary/GLOSSARY.md)
- [概念关系图谱](knowledge-standards/concept-maps/CONCEPT_MAPS.md)

---

**维护说明**：本学习路径应定期更新，根据学习者的反馈和项目发展调整路径内容。
