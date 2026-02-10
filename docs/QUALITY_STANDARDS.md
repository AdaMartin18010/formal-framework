# 质量规范 (Quality Standards)

> 本文档定义形式化框架文档与模型产物的质量基线，用于评审、门禁与持续改进。

**本节要点**：（1）DRAFT/RC/FINAL 完成度等级与门禁；（2）结构、语言、图表与链接、证据引用要求；（3）与 EXPERT_REVIEW_SYSTEM、CODE_REVIEW_GUIDE 的关系。  
**预计阅读时间**：全文约 8–12 分钟。

## 1. 文档完成度等级

| 等级 | 说明 | 门禁要求 |
|------|------|----------|
| **DRAFT** | 初稿，具备最小可读结构 | 目标、术语表或初步引用、存在空白占位可接受 |
| **RC** (Release Candidate) | 候选发布 | 完成术语/结构/方法/DSL/验证/案例/引用（适用维度）；通过至少一次专家评审；主要空白已补齐 |
| **FINAL** | 发布版 | 双评审（学术+工程）通过；引用合规；结论可追溯；案例与度量齐备；对齐行业对标表 |

## 2. 结构一致性

- **理论/行业文档**应包含（在适用范围内）：术语与概念对齐、结构与约束、方法或算法要点、接口或 DSL 片段、验证与度量、案例或应用、开放问题与局限、引用与参考。
- **证据条目**须符合 [TEMPLATE_证据条目](templates/TEMPLATE_证据条目.md) 的章节结构。
- **L2/L3/L4** 文档的命名、层级与交叉引用遵循 [docs/README.md](README.md) 中定义的体系。

## 3. 语言与表述

- 术语与 [knowledge-standards/glossary/GLOSSARY.md](knowledge-standards/glossary/GLOSSARY.md) 及 [knowledge-standards/concept-index/CONCEPT_INDEX.md](knowledge-standards/concept-index/CONCEPT_INDEX.md) 一致；冲突时注明别名或同义项。
- **核心术语首次出现**：文档中核心术语（如形式化建模、数据模型、交互模型、L2/L3 等）在首次出现时，建议链接到 [术语表](knowledge-standards/glossary/GLOSSARY.md) 或 [概念索引](knowledge-standards/concept-index/CONCEPT_INDEX.md)，便于读者追溯定义、降低认知负荷。审稿或质量门禁时可选用**术语链检查**（抽查核心术语首现是否已链向术语表/概念索引），见 [DOCUMENT_COMPLETION_CHECK 质量门禁项](DOCUMENT_COMPLETION_CHECK.md)。
- 表述清晰、无歧义；中英术语首次出现时可并列（如「服务网格 (Service Mesh）」）。
- 避免未定义的缩写；通用缩写（如 API、DSL、L2/L3/L4）可在术语表中统一说明。

## 4. 图表与链接

- **Mermaid/表格**：符合项目 Mermaid 规范（节点 ID 无空格、无 HTML 标签、子图使用显式 ID 与标签）；长表提供简要摘要或目录。
- **图表/公式与正文邻近**（降低外在认知负荷）：图表、公式与对应解释应同屏或紧邻放置，避免「图在文远」、读者来回跳转；新写或修订长文档时遵守，以利于工作记忆与图式构建。依据见 [learning/LEARNING_AND_REVIEW_TIPS](learning/LEARNING_AND_REVIEW_TIPS.md) 认知负荷理论。
- **内部链接**：文内链接、锚点、交叉引用有效；定期由 [scripts/internal_link_checker.py](../scripts/internal_link_checker.py) 校验。
- **外部链接**：权威引用尽量使用稳定 URL；若为可变动链接，在证据条目中记录版本与日期。

## 5. 证据与引用

- 新增标准/课程/应用映射时，须创建或更新对应 `evidence:*` 条目（见 [CITATION_STANDARDS.md](CITATION_STANDARDS.md)）。
- 关键结论须具备高可信引用；未满足时文档不得标为 RC/FINAL。

## 6. 与评审和代码审查的关系

- **专家评审**：见 [EXPERT_REVIEW_SYSTEM.md](EXPERT_REVIEW_SYSTEM.md)；RC 至少一次、FINAL 双评审。
- **代码/配置审查**：见 [CODE_REVIEW_GUIDE.md](CODE_REVIEW_GUIDE.md)；若变更影响文档或脚本，需同步检查本规范。
- **PR 检查清单**：建议在 PR 模板中纳入「结构完整」「引用合规」「术语一致」「链接有效」「图表规范」「证据条目」「完成度等级」等项，并可结合 markdownlint/linkcheck 自动化。

---

**维护**：与 CITATION_STANDARDS、EXPERT_REVIEW_SYSTEM、CODE_REVIEW_GUIDE 及 [community-framework.md](community-framework.md) 第 3.0 节同步。  
**最后更新**：按项目 CHANGELOG 维护。
