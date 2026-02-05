# 知识图谱、本体与形式化（可选扩展）

> **定位**：本节为**可选扩展**，不替代本框架主链路（L2→L3→L4 与 [FORMAL_SPEC_LANGUAGES](FORMAL_SPEC_LANGUAGES.md)）。供对知识工程、本体与形式化推理结合感兴趣的研究者与架构师参考。

## 1. 概述

知识图谱与本体（ontology）在系统工程与形式化方法中日益用于结构化领域词汇、关系与约束。将此类方法与本框架 L2/L3 概念映射结合，可作为可选扩展：在保持「规格与不变式」主链路的前提下，为概念、术语与证据提供可查询、可推理的补充结构。

## 2. 与本框架的对应关系

- **L2/L3 概念与术语**：本框架 [CONCEPT_INDEX](../knowledge-standards/concept-index/CONCEPT_INDEX.md)、[GLOSSARY](../knowledge-standards/glossary/GLOSSARY.md) 已提供概念与术语的结构化索引；本体或知识图谱可对上述概念、前置关系、相关概念进行形式化描述，便于机器可读与推理。
- **行业与通用模型映射**：各行业 README 中的「行业↔通用模型对齐」表、[alignment-L2-L3-matrix](../formal-model/alignment-L2-L3-matrix.md) 中的对象/属性/不变式对应，可视为一种关系结构；本体或知识图可显式建模「行业概念 → L3 模型」「L3 模型 → L2 元模型」等关系。
- **证据与引用**：[evidence](../evidence/README.md) 条目与标准/课程/应用的映射可纳入图中，支持按标准、行业、L2/L3 维度查询。

## 3. 相关标准与工作（选列）

以下为可延伸阅读的方向，不要求本框架实现或依赖：

- **Ontology-based knowledge graphs for systems engineering**：近年研究将本体用于系统工程工作流与制品的形式化表示，支持版本化、查询与推理，与 L2/L3 模型驱动视角可对照。
- **OML (Ontological Modeling Language) v2**：基于 OWL2/SWRL 的系统工程本体建模语言，提供形式化词汇与描述逻辑语义，可与本框架的领域词汇与约束对齐做对比研究。
- **ULKB Logic 等**：结合高阶逻辑与知识图谱的推理框架（如基于 SMT 求解器与 SPARQL），与 [theory-enhancement](../formal-model/theory-enhancement/) 中的自动推理、形式化验证有概念上的联系。

## 4. 使用建议

- **主链路优先**：学习与审稿时以 [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md)、[FORMAL_SPEC_LANGUAGES](FORMAL_SPEC_LANGUAGES.md)、L2/L3/L4 文档为主。
- **扩展研究**：若需将概念索引、术语表或证据条目导出为机器可读结构（如 RDF、OWL 或图数据库），可参考本节与上述工作，并保持与现有 CONCEPT_INDEX、GLOSSARY、evidence 结构一致。

## 5. 参见

- [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md) — 标准与课程对标
- [FORMAL_SPEC_LANGUAGES](FORMAL_SPEC_LANGUAGES.md) — 形式化规格语言与 L2 对应
- [概念索引](../knowledge-standards/concept-index/CONCEPT_INDEX.md)、[术语表](../knowledge-standards/glossary/GLOSSARY.md) — 本框架概念与术语结构
