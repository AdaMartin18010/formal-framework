# 标准/课程 ↔ L2/L3 知识点年度对照表

> 本表由 [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md) 与 [alignment-L2-L3-matrix](../formal-model/alignment-L2-L3-matrix.md) 导出，供审稿、培训与年度对标使用。  
> **生成周期**：建议每年更新一版；本版日期 2025-02。

## 1. 国际标准 ↔ L2/L3 知识点

| 标准/规范 | 主要 L2 映射 | 主要 L3 映射 | 不变式/要点 | 一致点/扩展点（摘要） |
|-----------|--------------|--------------|-------------|------------------------|
| ISO/IEC/IEEE 42010:2022 | L2 各元模型（架构视角） | L3_D01/D04/D05 视图与视角 | 架构描述、利益相关方 | — |
| ISO/IEC/IEEE 15288:2023 | L2 全域（生命周期过程） | L3 各模型、系统级过程 | 技术管理、技术过程 | 一致：L3 与 L3_D09 与 15288 技术过程对应；扩展：本框架给出形式化不变式与 DSL，15288 不规定规格语言 |
| IEEE 1012:2024 | L2_D08 测试元模型 | L3_D08 验证与确认、V&V | Determinism, CoverageGate, RegressionSafety | 一致：L3_D08 与 1012 V&V 对应；扩展：V&V 与 L2 不变式、L3 契约及 theory-enhancement 绑定 |
| ISO/IEC/IEEE 24748-2:2024 | 同上（15288 应用指南） | 同上 | 与 15288 配套 | — |
| ISO/IEC 12207 | L2 过程视角 | L3_D09 CI/CD、生命周期 | CI1–CI4, 流程阶段 | — |
| IEEE/ISO 29119-5:2024 | L2_D08 | L3_D08 关键词驱动测试 | 测试框架、互操作 | — |
| ISO/IEC/IEEE 24641:2023 | L2 模型驱动 | L3 各模型、theory-enhancement | 模型转换、验证、工具能力 | — |
| ISO/IEC 27001:2022 | L2_D05/D06 | L3_D05 配置安全、L3_D06 审计 | 安全与审计 | — |
| TLA+ / Alloy | L2 行为/关系规约 | L3_D08、theory-enhancement | 并发、不变式、轻量形式化 | — |
| OpenAPI 3.x | L2_D01 | L3_D01 API、契约 | ContractCompleteness, VersionCompatibility | — |
| NIST SP 800-190 | L2_D04 | L3_D04 容器、L4_D90 安全 | 容器安全 | — |

## 2. 名校课程 ↔ L2/L3 知识点（选列）

| 课程 | 主要 L2 映射 | 主要 L3 映射 | 学习路径 |
|------|--------------|--------------|----------|
| Stanford CS 256 | L2 形式化、行为规约 | L3_D08 验证、分布式 | 进阶·形式化验证 |
| Stanford CS 357S | L2 验证、测试 | L3_D08、FORMAL_SPEC_LANGUAGES | 进阶·验证与测试 |
| CMU 15-414 (Why3) | L2 规约、不变式 | L3_D08 演绎验证 | 进阶·形式化验证 |
| Berkeley EECS 219C | L2/L3 验证 | L3_D08、SAT/SMT、综合 | 进阶·验证 |
| MIT 6.042 / Berkeley CS 70 | L2 数学基础、逻辑 | — | 初学者·阶段1 前置 |
| Stanford CS 210 / CMU 15-413 | — | L3 各模型、practice-guides | 初学者·阶段2 后 |
| ETH Distributed Systems | L2 分布式视角 | L3_D10 分布式模式、L4 各行业 | 行业专项·分布式 |
| 清华形式化建模 | L2 建模与验证 | L3 各标准模型、TLA+/UPPAAL | 进阶·形式化与建模 |

## 3. 使用说明

- **审稿**：新增或修改 L2/L3 内容时，可据此表核对是否与所列标准/课程一致。
- **培训**：设计培训大纲时可按「标准/课程 → L2/L3」选取章节。
- **年度更新**：每年从 AUTHORITY_ALIGNMENT_INDEX 与 alignment-L2-L3-matrix 同步更新本表，并更新「本版日期」。

## 4. 参见

- [AUTHORITY_ALIGNMENT_INDEX](AUTHORITY_ALIGNMENT_INDEX.md) — 完整标准与课程列表及链接
- [alignment-L2-L3-matrix](../formal-model/alignment-L2-L3-matrix.md) — L2↔L3 对象/属性/不变式映射
- [LEARNING_PATHS](../LEARNING_PATHS.md) — 学习路径与阶段对应
