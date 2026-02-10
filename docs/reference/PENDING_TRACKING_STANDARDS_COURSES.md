# 待跟踪标准与课程 (Pending Tracking: Standards & Courses)

> 本页集中列出**待发布/在研**标准与**待补充/核查**课程，便于每季度或年度刷新时补全 [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md) 与 evidence。  
> **维护周期**：建议每半年或每年更新一次；发布或确认后移至 AUTHORITY_ALIGNMENT_INDEX 主表并建立 evidence（如适用）。

## 1. 待发布/在研标准

| 标准/项目 | 状态 | 说明 | 本框架拟映射 | 发布后动作 |
| --------- | ---- | ---- | ------------ | ---------- |
| ISO/IEC 12207 (FDIS 新版) | FDIS 在批 | 软件生命周期过程修订版 | L3_D09 CI/CD、practice-guides | 更新 AUTHORITY_ALIGNMENT_INDEX 版本；刷新 evidence:STD-12207 |
| IEEE/ISO/IEC P12207 | 在研 (PAR 已批) | 取代 12207:2017 的新版 | 同上 | 发布后入主表并建/更新 evidence |
| ISO/IEC/IEEE DIS 42024 | 草案中 | 企业、系统与软件 — 架构基础（Architecture fundamentals） | L2/L3 架构视角、与 42010 互补 | 发布后建 evidence 并补充 AUTHORITY_ALIGNMENT_INDEX 映射 |
| ISO/IEC/IEEE P24748-3 | 在研 | 12207 应用指南（与 24748-2 对应 15288 平行） | L3_D09、生命周期 | 发布后入主表并建 evidence |
| **SWEBOK V4.0**（IEEE-CS） | 约 2025-09 发布 | 软件工程知识体指南，18 个知识域（含软件架构、运维、安全等）；形式化方法传统上在构造/设计 KA | L2 逻辑与规格、L3 各模型、形式化基础 | 发布后建 evidence 并补 AUTHORITY_ALIGNMENT_INDEX 与 L2/L3 映射 |
| ISO/IEC/IEEE 41062 | 2024 已发布 | 软件工程 — 生命周期过程 — 软件获取 | L3_D09、采购与生命周期 | 可选：补入 AUTHORITY_ALIGNMENT_INDEX 主表或 evidence |
| ISO/IEC/IEEE 24748-1 | 2024 已发布 | 系统与软件工程 — 生命周期管理 第 1 部分（与 15288/12207 配套） | L3_D09、生命周期管理 | 可与现有 24748-2 并列，补入主表或 evidence |

## 2. 待补充/核查课程

| 机构 | 课程/方向 | 说明 | 本框架拟映射 | 核查/补充动作 |
| ---- | --------- | ---- | ------------ | ------------- |
| MIT | 形式化方法/逻辑/验证相关 6.xxx | 检索未直接对应到单门形式化方法课；6.042 为数学基础已列入 | L2 逻辑、L3_D08 验证 | **年度核查**：每年度核查 MIT 6.xxx 形式化/验证相关课程目录，若有新开或更名则补充至 AUTHORITY_ALIGNMENT_INDEX 并同步 LEARNING_PATHS |
| FME / FMTea | 全球形式化方法课程 | [FMTea 课程数据库](https://fme-teaching.github.io/courses/) 可按主题/国家/工具筛选 | L2/L3 形式化、验证、规格 | **年度/半年核查**：可从 FMTea 补充欧洲、澳洲、亚洲等与 L2/L3 强相关课程并加入 AUTHORITY_ALIGNMENT_INDEX；可选建 evidence:FMTea 或 COURSE-FMTea |
| 其他名校 | 形式化方法、软件工程新课程 | 新发现与 L2/L3 强相关的课程 | 按课程主题对应 L2/L3 | 发现后补充至 AUTHORITY_ALIGNMENT_INDEX 并同步 LEARNING_PATHS |

## 3. 使用说明

- **季度/年度任务**：运行权威对标刷新时，可据此表逐项检查「是否已发布/已上线」，并将已发布标准或已确认课程迁入 [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md)，必要时新建或更新 [evidence](../evidence/README.md) 条目。
- **与看板联动**：本表在 [RECURSIVE_IMPROVEMENT_KANBAN](../RECURSIVE_IMPROVEMENT_KANBAN.md) 的「待跟踪标准/课程维护」周期任务中被引用；更新本表后建议同步更新 AUTHORITY_ALIGNMENT_INDEX 的「本表最后核查日期」。

## 4. 参见

- [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md) — 权威对标总索引
- [AUTHORITY_STANDARD_COURSE_L2L3_MATRIX](AUTHORITY_STANDARD_COURSE_L2L3_MATRIX.md) — 标准/课程 ↔ L2/L3 年度对照表
- [evidence/README](../evidence/README.md) — 证据条目索引与待补充列表
- [RECURSIVE_IMPROVEMENT_KANBAN](../RECURSIVE_IMPROVEMENT_KANBAN.md) — 递归完善看板与周期任务
