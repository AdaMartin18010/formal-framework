# 代码审查指南 (Code Review Guide)

> 本文档定义形式化框架中代码、脚本与配置变更的审查要求；与文档质量、引用规范、专家评审协同使用。

## 1. 适用范围

- 仓库内 **源代码**（如 `src/`、`scripts/`）的提交与合并。
- **配置文件**（CI/CD、工具链、文档生成相关）的变更。
- 影响 **文档结构、链接或引用** 的脚本与自动化逻辑。

## 2. 审查原则

- **功能正确**：变更实现预期行为，无引入明显缺陷。
- **可维护性**：命名清晰、结构合理、关键逻辑有注释或文档说明。
- **与文档一致**：若脚本或工具涉及文档规范（如链接校验、证据条目、DSL 解析），须与 [QUALITY_STANDARDS.md](QUALITY_STANDARDS.md)、[CITATION_STANDARDS.md](CITATION_STANDARDS.md) 一致。
- **可追溯**：重大逻辑或行为变更应在 CHANGELOG 或 PR 描述中说明。

## 3. 审查检查项

### 3.1 通用

- 代码风格与项目约定一致（若存在 linter/formatter 配置则通过检查）。
- 无敏感信息（密钥、内部 URL、个人数据）提交。
- 依赖变更合理且已记录（如 requirements.txt、package.json）。

### 3.2 脚本与工具

- 脚本用途、输入输出、使用场景在 README 或脚本内注释中说明。
- 对 docs/ 或 evidence/ 的读写行为符合文档结构与命名规范。
- 新增或修改的校验规则与 [QUALITY_STANDARDS.md](QUALITY_STANDARDS.md) 中门禁项对齐（如链接有效、引用合规）。

### 3.3 文档相关变更

- 若 PR 同时修改文档：需满足 [QUALITY_STANDARDS.md](QUALITY_STANDARDS.md) 与 [CITATION_STANDARDS.md](CITATION_STANDARDS.md) 中适用条款。
- 内部链接、证据条目引用、完成度等级等与 [EXPERT_REVIEW_SYSTEM.md](EXPERT_REVIEW_SYSTEM.md) 的评审要求一致（按文档类型决定是否需专家评审）。

## 4. 与文档质量体系的衔接

- **文档-only 变更**：以 [QUALITY_STANDARDS.md](QUALITY_STANDARDS.md) 与 [EXPERT_REVIEW_SYSTEM.md](EXPERT_REVIEW_SYSTEM.md) 为主；本指南适用于其中涉及的脚本或配置。
- **代码+文档**：代码部分按本指南审查；文档部分按质量规范与引用规范审查，必要时触发专家评审。

## 5. PR 与流程建议

- 在 PR 模板中提供「代码审查」与「文档/质量审查」勾选项，便于分类与记录。
- 建议 CI 中运行：linter、链接校验（如 [scripts/internal_link_checker.py](../scripts/internal_link_checker.py)）、文档质量检查（若已集成），作为合并前自动门禁。

---

**维护**：与 QUALITY_STANDARDS、CITATION_STANDARDS、EXPERT_REVIEW_SYSTEM 及 [CONTRIBUTING.md](../CONTRIBUTING.md) 同步。  
**最后更新**：按项目 CHANGELOG 维护。
