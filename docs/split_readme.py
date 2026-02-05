# -*- coding: utf-8 -*-
"""One-off script to split README: create README_EXTENDED and shorten README."""
import os
BASE = os.path.dirname(os.path.abspath(__file__))
README = os.path.join(BASE, "README.md")
EXTENDED = os.path.join(BASE, "README_EXTENDED.md")

with open(README, "r", encoding="utf-8") as f:
    lines = f.readlines()

# Find start of "## 6. 递归推理与自动化流程示例"
idx6 = None
for i, line in enumerate(lines):
    if line.strip().startswith("## 6. 递归推理与自动化流程示例"):
        idx6 = i
        break
if idx6 is None:
    raise SystemExit("Could not find ## 6. in README")

# Content for extended (from line 6 to end)
extended_header = """# 形式化框架 - 延伸阅读 (README Extended)

> 本文档为 [README](README.md) 的扩展部分，包含递归推理与自动化示例、各模型递归扩展案例、快速开始与路线图完整版、递归完善计划、AI 与社区治理、模板与 FAQ、全球化与可持续发展等。  
> **预计阅读时间**：约 30–40 分钟。

---

"""

extended_body = "".join(lines[idx6:])
with open(EXTENDED, "w", encoding="utf-8") as f:
    f.write(extended_header)
    f.write(extended_body)

# New short sections 6-11 for main README
new_sections = """
## 6. 延伸阅读与扩展内容

递归推理与自动化示例、各模型递归扩展案例、快速开始与路线图完整版、工具生态与项目状态、贡献指南的完整内容，以及递归完善计划、AI 与社区治理、模板与 FAQ、全球化与可持续发展等，见 **[README_EXTENDED](README_EXTENDED.md)**（约 30–40 分钟阅读）。

---

## 7. 快速开始指南

1. **了解项目定位**：阅读项目概述与 [LEARNING_PATHS](LEARNING_PATHS.md)。
2. **选择学习路径**：理论研究者 → formal-model/core-concepts/；架构师 → L2/L3 → industry-model/；行业专家 → L4 索引与对应行业 README。
3. **核心文档顺序**：README → formal-model/README → 选读 L2 → L3 → industry-model/*/README。详见 [QUICK_START_GUIDE](QUICK_START_GUIDE.md)。

---

## 8. 项目路线图

- **短期**：文档与证据完善、工具与质量提升。
- **中期**：形式化验证与工具生态、社区建设。
- **长期**：标准体系与认证、生态系统与创新。详见 [ROADMAP](ROADMAP.md)。

---

## 9. 工具生态

文档管理工具：索引生成、证据管理、质量度量、证据模板生成、综合工具。见 [scripts/README](../scripts/README.md) 与 README 第 11 节（完整版在 [README_EXTENDED](README_EXTENDED.md)）。

---

## 10. 项目状态

L2/L3/L4 与行业模型完成度、质量指标与最新更新见 [PROJECT_STATUS](PROJECT_STATUS.md)、[DOCUMENT_COMPLETION_CHECK](DOCUMENT_COMPLETION_CHECK.md)。

---

## 11. 贡献指南

贡献类型、流程与质量标准见 [CONTRIBUTING](CONTRIBUTING.md)。贡献与评审须对齐 [CITATION_STANDARDS](CITATION_STANDARDS.md)、[QUALITY_STANDARDS](QUALITY_STANDARDS.md)、[EXPERT_REVIEW_SYSTEM](EXPERT_REVIEW_SYSTEM.md)、[CODE_REVIEW_GUIDE](CODE_REVIEW_GUIDE.md)。

---
"""

# Main README: lines 1 to idx6-1 (0-indexed, so lines before ## 6.) + new_sections
main_content = "".join(lines[:idx6]) + new_sections
with open(README, "w", encoding="utf-8") as f:
    f.write(main_content)

print("Split done: README shortened, README_EXTENDED.md created.")
