# 复习检查点清单 (Review Checklist)

> 按学习路径与阶段整理的可勾选复习清单，配合间隔重复（如 1 天、1 周回顾）使用。完成一项后勾选 `- [x]`，便于自测与巩固。

**本节要点**：（1）初学者 / 进阶 / 行业专项各阶段的可勾选检查点；（2）链回概念索引与术语表；（3）与 [LEARNING_PATHS](../LEARNING_PATHS.md) 对应。  
**预计使用时间**：每次复习 5–15 分钟；建议与 [概念索引](../knowledge-standards/concept-index/CONCEPT_INDEX.md)、[术语表](../knowledge-standards/glossary/GLOSSARY.md) 配合使用。

## 使用说明

- **间隔建议**：阶段内每 1 天回顾当日要点；阶段结束后 1 周、1 月各做一次总复习。
- **主动回忆（先写再对）**：每条检查点建议**先写下你的答案（1 句话）**，再点开链接核对，效果优于直接重读；自测后可对照下方「参考一句话」或文档中的定义。**以下各阶段检查点均建议先写再对**（先凭记忆写一句再点开链接核对）。
- **可选工具**：建议与 **Anki**、**RemNote** 等间隔重复工具配合：将下方检查点问句制成卡片，按 1d/7d/30d 复习。可将「概念→复习问句」导出为 CSV 或 Markdown 列表，便于自制牌组；本清单中标注「先写再对」的条目尤其适合作为卡片正面（问句）与背面（参考一句话或链接）。

---

## 初学者路径 — 复习检查点

### 阶段1：基础概念

- [ ] 能用一句话说明「形式化建模」在本框架中的含义 → [形式化建模](../formal-model/core-concepts/formal-modeling.md)（先写一句再核对）
- [ ] 能说明数据、功能、交互三个元模型分别解决什么问题 → [数据](../formal-model/data-model/theory.md)、[功能](../formal-model/functional-model/theory.md)、[交互](../formal-model/interaction-model/theory.md)（先写再对）
- [ ] 能说明 L2 与「代码/部署」的对应关系 → [README 模型体系](../README.md#4-各模型关系与递归扩展路径)（先写再对）
- [ ] 核心术语能对应 [术语表](../knowledge-standards/glossary/GLOSSARY.md) 中的定义

**参考一句话（自测后核对）**：形式化建模＝用数学化规格与不变式描述系统，便于验证与追溯。数据元模型管实体/存储/迁移，功能元模型管业务逻辑/规则/工作流，交互元模型管 API/协议/消息/契约。L2 是抽象层，L3 是标准实现层，代码与部署对应 L3 及行业模型的具体化。

### 阶段2：实践应用

- [ ] 能说出测试、部署、监控模型在 L3 中分别对应的文档 → [L3_D08](../L3_D08_测试标准模型.md)、[L3_D05](../L3_D05_部署标准模型.md)、[L3_D06](../L3_D06_监控标准模型.md)（先写再对）
- [ ] 能举出云原生案例与 L3 模型的对应关系 → [云原生 README](../industry-model/cloud-native-architecture/README.md)（先写再对）
- [ ] 能举一个「行业模型映射到通用模型」的例子 → [README 第 5 节](../README.md#5-行业映射关系)（先写再对）
- [ ] 关键概念能在 [概念索引](../knowledge-standards/concept-index/CONCEPT_INDEX.md) 中快速定位（先写再对）

**参考一句话（自测后核对）**：测试→L3_D08、部署→L3_D05、监控→L3_D06。云原生案例例：K8s 对应 L3_D04 运行时/编排，Istio 对应 L3_D04+L3_D01 服务网格。行业映射例：云原生 API 网关 = 通用交互模型（L3_D01）在云原生行业的实例。

### 阶段3：工具使用

- [ ] 能说明 DSL 与 AST 的关系 → [领域特定语言](../formal-model/core-concepts/domain-specific-language.md)、[形式化验证](../formal-model/core-concepts/formal-verification.md)（先写再对）
- [ ] 能说明验证在质量门禁中的角色 → [QUALITY_STANDARDS](../QUALITY_STANDARDS.md)、[EXPERT_REVIEW_SYSTEM](../EXPERT_REVIEW_SYSTEM.md)（先写再对）
- [ ] 已浏览 [概念索引](../knowledge-standards/concept-index/CONCEPT_INDEX.md) 与 [术语表](../knowledge-standards/glossary/GLOSSARY.md)，可进入进阶或行业专项（先写再对）

**参考一句话（自测后核对）**：DSL 定义领域语法，解析后得到 AST；AST 是形式化验证与代码生成的输入结构。验证在质量门禁中用于检查规格/不变式/覆盖率等，未通过可阻断发布或要求修复。

**本路径与权威对标**：见 [AUTHORITY_ALIGNMENT_INDEX 第 3 节](../reference/AUTHORITY_ALIGNMENT_INDEX.md)（如 Stanford CS 103/210、MIT 6.042、Berkeley CS 70/169、CMU 15-413）；认证与培训见第 4 节（CNCF 等）。

---

## 进阶路径 — 复习检查点

### 阶段1：理论基础深化

- [ ] 能设计与实现 AST → [抽象语法树](../formal-model/core-concepts/abstract-syntax-tree.md)（先写再对）
- [ ] 能理解 SAT/SMT 求解器原理 → [自动推理](../formal-model/core-concepts/automated-reasoning.md)（先写再对）
- [ ] 能用 LTL/CTL 描述系统性质 → [时序逻辑](../formal-model/core-concepts/temporal-logic.md)（先写再对）
- [ ] 能用 Hoare 逻辑进行程序证明 → [程序验证](../formal-model/core-concepts/program-verification.md)（先写再对）

**间隔归来建议**：若间隔数日后回来，建议先完成上列至少 2 条自测（先写再对），再进入阶段2。形式化语言选型见 [FORMAL_SPEC_LANGUAGES](../reference/FORMAL_SPEC_LANGUAGES.md) §2.1。

### 阶段2：高级建模技术

- [ ] 能设计 MDE 流程 → [模型驱动工程](../formal-model/core-concepts/model-driven-engineering.md)（先写再对）
- [ ] 能实现模型转换规则 → [模型转换](../formal-model/core-concepts/model-transformation.md)（先写再对）
- [ ] 能设计递归模型结构 → [递归建模](../formal-model/core-concepts/recursive-modeling.md)（先写再对）
- [ ] 能构建知识图谱 → [知识图谱](../formal-model/core-concepts/knowledge-graph.md)（先写再对）

**间隔归来建议**：若间隔数日后回来，建议先完成上列至少 2 条自测（先写再对），再进入阶段3。L2/L3 映射见 [alignment-L2-L3-matrix](../formal-model/alignment-L2-L3-matrix.md)。

### 阶段3：验证工具精通

- [ ] 能使用 TLA+/SPIN 等工具验证系统性质（先写再对）
- [ ] 能使用 Coq/Isabelle 等定理证明工具（先写再对）
- [ ] 能设计行业特定模型（金融/IoT/Web3）（先写再对）

**间隔归来建议**：若间隔数日后回来，建议先完成 TLA+ 与 Alloy 选型、Why3 与课程对应等自测（先写再对），再进入专家路径或项目。选型与课程见 [FORMAL_SPEC_LANGUAGES](../reference/FORMAL_SPEC_LANGUAGES.md) §2.1、[AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节。

**本路径与权威对标**：见 [AUTHORITY_ALIGNMENT_INDEX 第 3 节](../reference/AUTHORITY_ALIGNMENT_INDEX.md)（Stanford CS 256/357S、CMU 15-414/15-311、Berkeley EECS 219C、UW CSE 507、清华形式化建模等）；标准见第 2 节（IEEE 1012、TLA+、Alloy 等）。

---

## 行业专项路径 — 复习检查点

### 云原生专项

- [ ] 能说出本行业与通用模型对照小结（见 [云原生 README](../industry-model/cloud-native-architecture/README.md)）（先写再对）
- [ ] 能对应 CNCF 课程/认证知识域与 L3_D04/D05/D06/D09（先写再对）
- [ ] 六个案例（K8s、Service Mesh、GitOps、可观测性、Serverless、API 网关）与 L3 映射清晰（先写再对）

### AI 基础设施专项

- [ ] 能说出本行业与通用模型对照（见 [AI README](../industry-model/ai-infrastructure-architecture/README.md)）（先写再对）
- [ ] 能对应 L4_D93 与 AI/ML 标准、认证（先写再对）

### 金融 / 物联网 / Web3 专项

- [ ] 能说出本行业与通用模型对照及 L4 索引中的权威对标（L4_D91/D92/D94）（先写再对）
- [ ] 能对应相关标准（PCI-DSS、EdgeX、Ethereum 等）与 L3 模型（先写再对）

**行业路径与权威对标**：见 [AUTHORITY_ALIGNMENT_INDEX 第 4–5 节](../reference/AUTHORITY_ALIGNMENT_INDEX.md)（CNCF 认证、各 L4 索引文档）。

---

## 专家路径 — 复习检查点

与 [LEARNING_PATHS 专家路径](../LEARNING_PATHS.md#专家路径-expert-path) 对应；各阶段均建议**先写再对**。

### 阶段1：理论研究

- [ ] 能说出近期 FM/CAV/ICSE 中与 L2/L3 相关的议题 → [AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md)（先写再对）
- [ ] 能说明 ISO/IEC JTC1/SC7、OMG 与本框架的对应关系（先写再对）

**间隔归来建议**：若间隔数日后回来，建议先完成上列至少 1 条自测（先写再对），再进入阶段2。

### 阶段2：实践创新

- [ ] 能说明本阶段建模与 L3 各标准模型的对应 → [alignment-L2-L3-matrix](../formal-model/alignment-L2-L3-matrix.md)（先写再对）
- [ ] 能说明创新点如何与 evidence、权威标准对齐 → [evidence/README](../evidence/README.md)、[AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md)（先写再对）

**间隔归来建议**：若间隔数日后回来，建议先完成上列至少 1 条自测（先写再对），再进入阶段3。

### 阶段3：知识传播

- [ ] 能说出近期 12207/15288/42010 等标准修订或 CNCF/课程大纲变更要点 → [AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md)、[PENDING_TRACKING_STANDARDS_COURSES](../reference/PENDING_TRACKING_STANDARDS_COURSES.md)（先写再对）

**间隔归来建议**：本阶段为持续任务；建议每季度或半年做一次上述自测（先写再对），保持与权威对齐。

**本路径与权威对标**：见 [AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) 全文；待跟踪标准/课程见 [PENDING_TRACKING_STANDARDS_COURSES](../reference/PENDING_TRACKING_STANDARDS_COURSES.md)。

---

## 相关文档

- [LEARNING_PATHS](../LEARNING_PATHS.md) — 完整学习路径与阶段说明
- [概念索引](../knowledge-standards/concept-index/CONCEPT_INDEX.md) — 概念定义与自测问句
- [术语表](../knowledge-standards/glossary/GLOSSARY.md) — 术语定义与引用
- [AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) — 学完后可对接的课程与标准
