# 形式化规格语言与工具族一览

> 本文档汇总常用形式化规格语言及工具与本框架 L2 规格/不变式的对应关系，便于选型与对标。完整标准与证据见 [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md) 与 [evidence](../evidence/)。

**本节要点**：（1）Z、VDM、TLA+、Alloy、Why3 等语言/工具的定位；（2）与本框架 L2 规格、不变式、验证的对应；（3）形式化验证分支（定理证明、模型检验、SMT）与 L3_D08、theory-enhancement 的对应；（4）**按场景选型**（结构/数据→Alloy、并发/分布式→TLA+、规约与证明→Why3/Z/VDM）及与课程的对应，见 §2.1。  
**预计阅读时间**：全文约 12–18 分钟；仅读 §1–§2.1 约 8 分钟。

## 1. 形式化规格语言与 L2 对应

| 语言/工具 | 标准/来源 | 侧重 | 与本框架 L2 对应 |
|-----------|------------|------|------------------|
| **Z Notation** | ISO/IEC 13568:2002 | 前置/后置条件、不变式、状态与操作 | L2 各元模型中的前置条件、不变式、状态迁移 |
| **VDM** | ISO/IEC 13817 | 数据与功能规格、不变式、精化 | L2_D02 数据、L2_D03 功能；不变式与精化 |
| **TLA+** | Lamport | 时序逻辑、并发与分布式行为规约 | L2/L3 行为规约、并发、分布式；theory-enhancement/formal-verification |
| **Alloy** | 关系逻辑、轻量建模与分析 | 结构、关系、约束、反例查找 | L2 关系与结构、轻量形式化、DSL 分析 |
| **Why3** | 演绎验证、程序规约与证明 | 规约、验证条件、定理证明 | L2/L3 形式化验证、规约；与 CMU 15-414 等课程对应 |

### 1.1 TLA+ 业界采用与 2024 调查要点

- **业界采用**：AWS 自 2011 年起将 TLA+ 用于复杂系统与公有云服务设计；Intel 在硬件设计中使用 TLA+，有项目在实现前发现数百个缺陷；Microsoft 亦有内部采用。TLA+ Foundation（非营利）成员包括 AWS、Oracle 等，推动工业与学术界采用。
- **2024 社区调查要点**：用户动机中约 53.7% 为对形式化方法的普遍兴趣，36.1% 通过学术/研究接触，25% 因 TLA+ 的缺陷发现能力；约 90% 用户反馈提升了对系统的理解；主要挑战包括学习曲线陡峭、调试能力有限、建模抽象难度及与其他工具的集成。详见 [evidence/STD-TLA](../evidence/STD-TLA.md)。

## 2. 形式化验证分支与 L3_D08、theory-enhancement 对应

| 验证分支 | 典型方法与工具 | 本框架映射 |
|----------|----------------|------------|
| **定理证明** | Coq、Isabelle、Lean、Why3 | [formal-model 验证框架](../formal-model/verification-framework.md)、[theory-enhancement/formal-verification](../formal-model/theory-enhancement/formal-verification-theory.md)；L3_D08 验证与确认 |
| **模型检验** | TLA+、SPIN、NuSMV、UPPAAL | L2/L3 行为规约与不变式；L3_D08 测试与验证 |
| **SMT/决策过程** | Z3、CVC4、SAT 求解器 | 约束求解、程序验证、与 IEEE 1012 V&V 对应；见 [evidence:STD-1012](../evidence/STD-1012.md) |

**Why3 与课程**：CMU 15-414（Bug Catching: Automated Program Verification）以 Why3 为演绎验证平台，与本表规约与 L3_D08 验证对应。

### 2.1 按场景选型与学习路径

按领域与目标选择语言/工具，便于快速掌握并与本框架 L2/L3 对齐：

| 场景/领域 | 推荐语言/工具 | 对应课程（示例） | 本框架映射 |
|-----------|----------------|------------------|------------|
| **结构/数据/架构** | Alloy（关系、约束、反例查找） | Berkeley EECS 219C、UW CSE 507 | L2 关系与结构、DSL 分析、L3_D02 数据 |
| **并发/分布式/状态** | TLA+（时序逻辑、行为规约） | Stanford CS 256（LTL/CTL）、[evidence/STD-TLA](../evidence/STD-TLA.md) | L2/L3 行为规约、L3_D10 分布式模式 |
| **规约与演绎证明** | Why3、Z、VDM | CMU 15-414（Why3）、[AUTHORITY_ALIGNMENT_INDEX 第 3 节](AUTHORITY_ALIGNMENT_INDEX.md#3-名校课程与教材) | L2 不变式与前置条件、L3_D08 验证与确认 |

学习路径建议：先确定场景（结构 vs 行为 vs 证明），再选上表对应语言与 [LEARNING_PATHS 进阶路径·形式化验证](../LEARNING_PATHS.md#进阶路径-intermediate-path) 中阶段 1–3 结合；课程大纲与 L2/L3 知识点对照见 [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md) 第 3 节及 [AUTHORITY_STANDARD_COURSE_L2L3_MATRIX](AUTHORITY_STANDARD_COURSE_L2L3_MATRIX.md)。

## 3. 与本框架文档的交叉引用

- **L2 元模型**：各 L2 文档中的「形式化不变式」「约束」可与上表语言表达的规格对照。
- **L3_D08 测试标准模型**：验证与确认过程与 IEEE 1012、定理证明/模型检验/SMT 方法对应。
- **theory-enhancement**： [formal-verification-theory](../formal-model/theory-enhancement/formal-verification-theory.md)、[logic-foundation](../formal-model/theory-enhancement/logic-foundation.md)、[type-theory-foundation](../formal-model/theory-enhancement/type-theory-foundation.md) 等提供理论基础。

## 4. 参见

- [权威对标总索引](AUTHORITY_ALIGNMENT_INDEX.md) 第 2 节（国际标准与规范）
- [evidence](../evidence/) 中 STD-*、STD-TLA、STD-ALLOY 等条目
- [LEARNING_PATHS 进阶路径·形式化验证](../LEARNING_PATHS.md#进阶路径-intermediate-path)
