# 递归完善看板说明 (Recursive Improvement Kanban)

本文档说明如何将**季度/年度检查**与**递归完善计划**产生的任务纳入看板并持续推进。

## 1. 任务来源

- **季度/年度脚本**：运行 `python scripts/quarterly_doc_check.py --root docs --evidence-scan --output docs/quarterly_report.md`，根据报告中的「缺失文件」「标准文档存在性」创建任务。
- **链接校验**：每季度运行 `python scripts/internal_link_checker.py --root docs`（可选 `--output report.md` 生成报告），根据报告对断链创建修复任务或标记已废弃并更新引用。
- **人工/社区**：内容空白、术语表补充、LEARNING_PATHS 更新、权威对标索引更新等。

## 2. 任务发布方式

- **GitHub Issues**：使用 [季度/年度文档完善任务](../.github/ISSUE_TEMPLATE/quarterly-doc-task.md) 模板创建 Issue，标签可用 `documentation`、`quality`。
- **看板**：在 GitHub Projects 或 Trello/飞书/钉钉看板中建立「递归完善」看板，列：待认领 / 进行中 / 评审中 / 已完成。将上述 Issue 同步到看板。

## 3. 认领与完成流程

1. 维护者或社区成员从「待认领」中认领任务，将状态改为「进行中」并 assign 自己。
2. 按 [CONTRIBUTING](../CONTRIBUTING.md) 与 [QUALITY_STANDARDS](QUALITY_STANDARDS.md) 完成修改，提交 PR。
3. 评审通过后合并，将任务移至「已完成」；若需修订则退回「进行中」。

## 4. 周期建议

- **季度**：运行 `quarterly_doc_check.py` 与 `internal_link_checker.py`，更新 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)，生成并发布新任务。
- **半年**：回顾 [docs/README](README.md) 第 23–31 节递归完善计划，补充内容空白与薄弱点。
- **年度**：体系大梳理（L2–L3–L4 总览、形式化成熟度、与最新标准/课程全面对照），更新 ROADMAP 与项目状态。

## 4.1 周期性任务模板（可持续推进）

以下任务可定期创建为 Issue 并同步到看板，建议标签：`documentation`、`quality`、`authority-alignment`（权威对标类）。内容与证据补全须满足 [QUALITY_STANDARDS](QUALITY_STANDARDS.md)、[CITATION_STANDARDS](CITATION_STANDARDS.md)；评审按 [EXPERT_REVIEW_SYSTEM](EXPERT_REVIEW_SYSTEM.md) 执行。

| 周期 | 任务名称 | 产出/验收 | 建议标签 |
| ---- | -------- | ---------- | -------- |
| 每季度 | 权威对标刷新 | 检查 ISO/IEC/IEEE、CNCF 认证页与 2–3 门名校课程链接；更新 AUTHORITY_ALIGNMENT_INDEX 版本/日期；补充 CNCF 新认证（如 CAPA、OTCA、CNPA、CNPE）与 L3 映射；补充 1–2 所名校课程映射（若新发现） | `authority-alignment`、`documentation` |
| 每季度 | 证据条目补全 | 至少完成 2–4 个「待补充」证据条目的实质内容（优先 STD-*、COURSE-* 及 L4 高引用）；符合 CITATION_STANDARDS | `documentation`、`quality` |
| 每季度 | 断链修复 | 运行 internal_link_checker；根据报告创建/认领任务，**优先处理高流量文档**（[QUICK_NAVIGATION](QUICK_NAVIGATION.md)、[README](README.md)、[LEARNING_PATHS](LEARNING_PATHS.md)、[AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)、各 [L4 索引](L4_D90_CN_行业索引与对标.md)）中的无效链接，再扩展至其他文档；修复或标记已废弃并更新引用 | `quality`、`documentation` |
| 每半年 | 学习路径与认知优化 | 审阅 [LEARNING_PATHS](LEARNING_PATHS.md) 与 1–2 条行业路径；增加或统一「5 分钟版」、复习检查点、自测问句；确保与 AUTHORITY_ALIGNMENT_INDEX 双向链接；可选补充「间隔归来建议」、扩展 [CONCEPT_INDEX 自测问句汇总](knowledge-standards/concept-index/CONCEPT_INDEX.md#自测问句汇总便于检索与主动回忆)（为高引用概念补自测问句）；可选更新 [learning/REVIEW_CHECKLIST](learning/REVIEW_CHECKLIST.md) | `documentation`、`authority-alignment` |
| 每半年 | 长文档可读性 | 为 3–5 个高流量长文档补全「本节要点」「预计阅读时间」、可选「5 分钟版」及**「单次阅读建议：建议分 2–4 次阅读，每次 1–2 节」**（超过约 40 分钟阅读时长的文档）；认知负荷自查（分段、图表邻近） | `documentation`、`quality` |
| 每半年 | 概念与术语 | 为 2–3 个高引用但无概念页的概念新增概念页或强化术语表；**术语首现链抽查**（高流量文档如 README、LEARNING_PATHS、AUTHORITY_ALIGNMENT_INDEX、L4、L3_D01/D08 中核心术语首次出现是否链向术语表/概念索引）与补全 | `documentation`、`quality` |
| 每半年 | theory-enhancement 与 core-concepts 双向链 | 在 theory-enhancement 各文档末尾「相关概念」或「参见」中补全对应 [core-concepts](formal-model/core-concepts/) 条目的反向链；抽查并修复缺失 | `documentation`、`quality` |
| 每年 | 标准与课程全面对照 | 完整过一遍 12207、15288、25010、27001、42010、1012、29119-5、24641 及 2–3 所名校形式化/软件工程课程大纲；更新 AUTHORITY_ALIGNMENT_INDEX 与 evidence；修订 ROADMAP 与项目状态 | `authority-alignment`、`documentation` |
| 每年 | 权威对齐年度对照表 | 生成一版「标准/课程 ↔ L2/L3 知识点」对照表（可从 AUTHORITY_ALIGNMENT_INDEX 与 [alignment-L2-L3-matrix](formal-model/alignment-L2-L3-matrix.md) 导出），供审稿与培训使用 | `authority-alignment`、`documentation` |
| 每年 | 权威来源扩展 | 从 [FMTea 课程数据库](https://fme-teaching.github.io/courses/) 补充 1–2 门欧洲/亚洲与 L2/L3 强相关课程；CS2023 形式化方法白皮书与框架对齐说明核查；SWEBOK v4、DIS 42024、P12207 发布后入表并建 evidence | `authority-alignment`、`documentation` |
| 每半年/每年 | 待跟踪标准/课程维护 | 更新 [reference/PENDING_TRACKING_STANDARDS_COURSES](reference/PENDING_TRACKING_STANDARDS_COURSES.md)（P12207、DIS 42024、24748-3、MIT 形式化相关等）；已发布/已确认项迁入 AUTHORITY_ALIGNMENT_INDEX 并建 evidence | `authority-alignment`、`documentation` |
| 每半年 | 学习与复习建议审阅 | 审阅 [learning/LEARNING_AND_REVIEW_TIPS](learning/LEARNING_AND_REVIEW_TIPS.md)，确保与 REVIEW_CHECKLIST、CONCEPT_INDEX 一致；必要时补充认知负荷、间隔重复、主动回忆的引用或说明 | `documentation` |
| 每季度 | 证据优先级认领 | 从 [evidence/README 待补充证据优先级列表](evidence/README.md#待补充证据优先级列表) 中认领 2–4 条补全，优先 STD-*、COURSE-* 与 L4 高引用 | `documentation`、`quality` |

使用方式：按周期从表中复制任务名称与验收标准，用 [.github/ISSUE_TEMPLATE/quarterly-doc-task.md](../.github/ISSUE_TEMPLATE/quarterly-doc-task.md) 或等价模板创建 Issue，加入看板列「待认领」，认领后移至「进行中」，完成后经评审移至「已完成」。证据条目补全时优先从 evidence/README 的「待补充证据优先级列表」认领。**断链修复时**：运行 `python scripts/internal_link_checker.py --root docs`（可选 `--output report.md`），根据报告优先修复 README、QUICK_NAVIGATION、LEARNING_PATHS、AUTHORITY_ALIGNMENT_INDEX、各 L4 索引中的无效链接（见 [internal_link_validation_report](internal_link_validation_report.md)）。

## 5. 与全面改进方案的任务对应

本看板可用于承接「权威对齐、认知与学习、链接与补充」三类任务（参见项目全面分析与改进方案）：

- **权威对齐**：使用标签 `authority-alignment`；任务示例：更新 AUTHORITY_ALIGNMENT_INDEX、补充 evidence、L2/L3 权威对标小节。
- **认知与学习**：使用标签 `documentation`；任务示例：LEARNING_PATHS 前置依赖图与掌握度标志、**为何先 X 后 Y**（各阶段总结中增加顺序理由，如数据→功能→交互 因契约依赖实体与行为）、**间隔归来建议**（各阶段末「若间隔 N 天后回来先做哪几条自测」）、**自测问句扩展**（CONCEPT_INDEX 高引用概念补自测问句并维护[自测问句汇总](knowledge-standards/concept-index/CONCEPT_INDEX.md#自测问句汇总便于检索与主动回忆)）、[learning/LEARNING_AND_REVIEW_TIPS](learning/LEARNING_AND_REVIEW_TIPS.md) 学习与复习建议、REVIEW_CHECKLIST 先写再对、**长文档分次阅读建议**（L3 长文档顶部「建议分 2–4 次阅读，每次 1–2 节」）、**形式化语言选型**（[FORMAL_SPEC_LANGUAGES](reference/FORMAL_SPEC_LANGUAGES.md) §2.1 按场景选型与课程对应）、**交错学习策略说明**（进阶路径中可选，已见于 [LEARNING_PATHS](LEARNING_PATHS.md) 与 [REVIEW_CHECKLIST](learning/REVIEW_CHECKLIST.md)）。
- **链接与补充**：使用标签 `quality`、`documentation`；任务示例：修复 CONCEPT_INDEX 悬空链接、行业 README 本行业证据条目、**术语首现链抽查**（高流量文档中核心术语首次出现链向术语表/概念索引）与补全；断链修复时**优先高流量文档**（README、QUICK_NAVIGATION、LEARNING_PATHS、AUTHORITY_ALIGNMENT_INDEX、各 L4 索引），再扩展至占位链接等。

按周期（月/季/半年/年）从上述三类中拆解具体 Issue 并纳入看板列「待认领」→「进行中」→「已完成」。

### 5.1 内容补充任务（来自 DOCUMENT_COMPLETION_CHECK）

以下任务来源于 [DOCUMENT_COMPLETION_CHECK](DOCUMENT_COMPLETION_CHECK.md) 中 L2/L3/L4 与行业模型的「主要问题」，可按「优先级×工时」拆成可认领 Issue，与证据补全、权威对标季度任务并列。建议标签：`documentation`、`quality`；需符合 [QUALITY_STANDARDS](QUALITY_STANDARDS.md)、[CITATION_STANDARDS](CITATION_STANDARDS.md)。

| 类型 | 任务示例 | 产出/验收 | 建议标签 |
| ---- | -------- | --------- | -------- |
| L2 内容补全 | L2_D01/D02 补充行业案例；L2_D02 补充 DSL 示例；L2_D03 补充形式化验证；L2_D04/D07 补充容器编排与调度案例；L2_D06/D08 补充告警规则与自动化测试示例 | 对应文档「主要问题」消除或降级；引用与结构符合 QUALITY_STANDARDS | `documentation`、`quality` |
| L3 内容补全 | L3_D01 补充更多协议；L3_D02 补充 NoSQL 支持；L3_D04 补充边缘计算；L3_D05 补充多云部署；L3_D06 补充 AI 监控；L3_D07 补充智能调度；L3_D10 补充分布式模式 | 同上 | `documentation`、`quality` |
| 行业/理论补全 | 各 industry-model README 或 theory 补充案例、与标准/课程对照要点；theory.md 末增加「与标准/课程对照要点」小节（可引用 [AUTHORITY_STANDARD_COURSE_L2L3_MATRIX](reference/AUTHORITY_STANDARD_COURSE_L2L3_MATRIX.md)） | 案例可追溯；对照要点与 evidence 一致 | `documentation`、`quality`、`authority-alignment` |

使用方式：从 [DOCUMENT_COMPLETION_CHECK](DOCUMENT_COMPLETION_CHECK.md) 的「主要问题」列选取单项或组合（如「L2_D02 缺少 DSL 示例」），创建 Issue 并加入看板「待认领」；认领后按上表验收标准完成并提交 PR。

## 5.2 本周期已完成（示例，供下周期参考）

以下为近期一轮递归完善中已完成的任务，对应本看板季度/半年/年度任务类型；下一周期可从 §4.1 表格中认领新任务。**权威对齐与认知改进方案 100% 落地**：CNCF 认证/课程↔L3 映射（L4_D90 §4.2、AUTHORITY_ALIGNMENT_INDEX）、CKS 认证行；LEARNING_AND_REVIEW_TIPS 认知与学习依据（Sweller、Kang 2016、分块与间隔重复）；全 L3 文档（含 L3_D01/D02/D03/D04/D05/D06/D07/D08/D09）本节要点/预计阅读时间/单次阅读建议；CONCEPT_INDEX 不变式条目与术语表链接修正；RECURSIVE_IMPROVEMENT_KANBAN §5.1 内容补充任务表；formal-model/data-model/theory、interaction-model/theory 与 FORMAL_SPEC_LANGUAGES「与标准/课程对照要点」或预计阅读时间。

- **模板与链接**：新增 [templates/TEMPLATE_映射矩阵](templates/TEMPLATE_映射矩阵.md)；L4_D90、L4_D91 引用修正为 templates 路径。
- **证据补全**：STD-29119-5、STD-24641、K8S-001、ISTIO-001 等已填写实质内容并列入 evidence/README 已完整填写表。
- **断链修复**：CITATION_STANDARDS、QUALITY_STANDARDS 中 TEMPLATE_证据条目 路径修正；QUICK_NAVIGATION 中脚本链接改为 `../scripts/`、概念索引链接改为 `knowledge-standards/concept-index/CONCEPT_INDEX.md`。
- **学习与认知**：QUICK_NAVIGATION 增加「学完 X 再学 Y」建议顺序；REVIEW_CHECKLIST 阶段2/阶段3 检查点补全「先写再对」标注；LEARNING_AND_REVIEW_TIPS 补充适应性微学习说明。
- **长文档可读性**：L3_D06、L3_D07、L4_D90、L4_D92、L4_D93、formal-model/monitoring-model/theory 等补全「本节要点」「预计阅读时间」及部分「5 分钟版」。
- **概念页**：新增 concepts/monitoring-model.md、concepts/runtime-model.md；CONCEPT_INDEX 链接更新。
- **年度对照表**：新增 [reference/AUTHORITY_STANDARD_COURSE_L2L3_MATRIX](reference/AUTHORITY_STANDARD_COURSE_L2L3_MATRIX.md)；ROADMAP、PROJECT_STATUS 更新。
- **权威与边界**：AUTHORITY_ALIGNMENT_INDEX 增加维护约定（以各校官网为准）、框架边界说明及年度对照表链接。
- **权威对齐与递归改进方案（本轮 100% 落地）**：新增 [reference/PENDING_TRACKING_STANDARDS_COURSES](reference/PENDING_TRACKING_STANDARDS_COURSES.md) 待跟踪标准/课程；AUTHORITY_ALIGNMENT_INDEX 链向该页；RECURSIVE_IMPROVEMENT_KANBAN 增加断链修复优先高流量文档、待跟踪标准/课程维护任务；ROADMAP 短期/中期/长期补全（断链、证据、权威对标、术语链检查、学习路径与长文档可读性、概念与术语、适应性微学习）；五个 L4 文档顶部补全「本行业 ↔ L2/L3 映射」表并链回 alignment 矩阵；新增概念页 rule-engine、workflow、contract 及 CONCEPT_INDEX 条目；L3_D08/L3_D09、L4_D91/L4_D94 补全本节要点/预计阅读时间/5 分钟版；DOCUMENT_COMPLETION_CHECK 与 QUALITY_STANDARDS 增加术语链检查（可选）；LEARNING_AND_REVIEW_TIPS 补充适应性微学习引用；表格格式（MD060）修正。
- **本周期（计划落地）**：FORMAL_SPEC_LANGUAGES 增加 §2.1 按场景选型与学习路径（结构/数据→Alloy、并发/分布式→TLA+、规约与证明→Why3/Z/VDM）及课程链接；L3_D07/D08/D09 增加「单次阅读建议：建议分 2–4 次阅读，每次 1–2 节」；LEARNING_PATHS 各阶段总结增加「为何本顺序」、阶段2 增加「本阶段对应文档建议分 N 次完成」、进阶/专家路径补全复习检查点与间隔归来建议；CONCEPT_INDEX 自测问句汇总增加锚点与维护说明；RECURSIVE_IMPROVEMENT_KANBAN §4.1/§5 增加长文档分次阅读、为何先 X 后 Y、形式化语言选型任务类型。
- **本周期（本轮 100% 落地）**：AUTHORITY_ALIGNMENT_INDEX 增加 AI 标准行（NIST AI RMF / ISO/IEC 23053 / IEEE 2857 → L4_D93）；CITATION_STANDARDS 证据条目模板链接修正为 `templates/TEMPLATE_证据条目.md`；LEARNING_PATHS 前置依赖图下增加与 AUTHORITY_ALIGNMENT_INDEX 第 3 节、FORMAL_SPEC_LANGUAGES §2.1 的显式链接，进阶路径阶段1/2/3 总结增加「本阶段与权威对标」并链至 FORMAL_SPEC_LANGUAGES §2.1 与 AUTHORITY_ALIGNMENT_INDEX；REVIEW_CHECKLIST 使用说明统一「先写再对」、进阶路径三阶段补全「间隔归来建议」、新增专家路径整节（阶段1/2/3 复习检查点与间隔归来建议）；CONCEPT_INDEX 使用指南增加自测问句汇总锚点与认领说明；LEARNING_AND_REVIEW_TIPS §3 增加 Kang (2016) 间隔重复政策含义（含技术文档与培训设计）。L3_D07/D08/D09 已含单次阅读建议，无需补写。

## 6. 证据优先级与年度对照

- **待补充证据优先级列表**：见 [evidence/README](evidence/README.md#待补充证据优先级列表)。每季度证据条目补全任务可从该列表按优先级认领（STD-*、COURSE-* 及 L4/行业 README 高引用者优先）。
- **权威对齐年度对照表**：每年可生成一版「标准/课程 ↔ L2/L3 知识点」对照表，来源为 [AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md) 与 [alignment-L2-L3-matrix](formal-model/alignment-L2-L3-matrix.md)，供审稿与培训使用。

## 7. 相关文档

- [AUTHORITY_AND_COGNITION_ANALYSIS](AUTHORITY_AND_COGNITION_ANALYSIS.md) — 权威对齐与认知批判性分析（权威覆盖、认知/学习建议、链接与补充及可持续任务规划）
- [QUALITY_STANDARDS](QUALITY_STANDARDS.md)
- [CITATION_STANDARDS](CITATION_STANDARDS.md)
- [EXPERT_REVIEW_SYSTEM](EXPERT_REVIEW_SYSTEM.md)
- [evidence/README](evidence/README.md)
- [reference/AUTHORITY_ALIGNMENT_INDEX](reference/AUTHORITY_ALIGNMENT_INDEX.md)、[reference/PENDING_TRACKING_STANDARDS_COURSES](reference/PENDING_TRACKING_STANDARDS_COURSES.md) — 权威对标与待跟踪标准/课程
- [LEARNING_PATHS](LEARNING_PATHS.md)、[learning/REVIEW_CHECKLIST](learning/REVIEW_CHECKLIST.md)、[learning/LEARNING_AND_REVIEW_TIPS](learning/LEARNING_AND_REVIEW_TIPS.md) — 学习路径、复习清单与学习科学建议
