# 引用规范 (Citation Standards)

> 本文档定义形式化框架中所有文档的引用与溯源要求，确保关键结论可追溯至高可信来源。

## 1. 适用范围

- 理论文档（`theory.md`）、行业案例、L2/L3/L4 标准模型中的**关键结论**与**术语定义**。
- 证据条目（`docs/evidence/*.md`）中的来源与映射说明。
- 对标表、映射矩阵中引用的标准、课程、官方文档。

## 2. 引用层级与可信度

| 层级 | 说明 | 示例 |
|------|------|------|
| **A - 权威** | 国际标准、官方项目文档、顶级会议/期刊论文、权威教材 | ISO/IEC 13568、Kubernetes 官方文档、CAV/ICSE 论文 |
| **B - 高可信** | 知名机构/大学课程大纲、广泛采用的行业规范、成熟开源项目文档 | CNCF 课程、IEEE 标准、Istio/Prometheus 官方文档 |
| **C - 参考** | 社区文章、博客、非官方教程、内部报告 | 需在文中注明「参考」并可与 A/B 对照使用 |

**要求**：关键结论（定义、公理、约束、与标准的对齐关系）须至少具备 **A 或 B** 级引用；C 仅作补充说明。

## 3. 引用格式

### 3.1 文内引用

- **标准**：`ISO/IEC 13568:2002`、`IEEE 1471`、`NIST SP 800-190`。
- **文档**：`[Kubernetes 官方文档](https://kubernetes.io/docs/)` 或 `evidence:CN-K8S-BASE`。
- **课程**：`Stanford CS 256 (Formal Methods for Reactive Systems)`，建议附课程主页或大纲链接。

### 3.2 证据条目引用

- 所有引用到外部标准/课程/项目的结论，应在 `docs/evidence/` 下建立对应证据条目（见 [TEMPLATE_证据条目](templates/TEMPLATE_证据条目.md)）。
- 证据条目须包含：来源、可信度、与本框架 L2/L3/L4 的映射、原文链接与版本/日期。

### 3.3 参考文献列表

- 文末「参考文献」或「引用」小节：按类型分组（标准、课程、文档、论文），每条含标题、来源、链接、版本/日期（如有）。

## 4. 必须引用的场景

- 术语的**形式化定义**或**行业标准定义**。
- **与 L2/L3/L4 的映射关系**（如「Pod ↔ L3_D04 容器编排单元」）若来自官方或标准，需注明来源。
- **验证与度量**中的阈值、公式或方法若源自标准/论文，需引用。
- **DSL 或接口设计**与现有标准（如 OpenAPI、Kubernetes API）的对齐说明。

## 5. 与质量门禁的关系

- 文档完成度等级 **RC** 与 **FINAL** 要求：关键结论具备高可信引用，且无未注明来源的权威性声称。
- 评审检查清单见 [community-framework.md](community-framework.md) 第 3.0 节；引用合规由 [EXPERT_REVIEW_SYSTEM.md](EXPERT_REVIEW_SYSTEM.md) 与 [QUALITY_STANDARDS.md](QUALITY_STANDARDS.md) 共同约束。

---

**维护**：与 [QUALITY_STANDARDS.md](QUALITY_STANDARDS.md)、[EXPERT_REVIEW_SYSTEM.md](EXPERT_REVIEW_SYSTEM.md)、[CODE_REVIEW_GUIDE.md](CODE_REVIEW_GUIDE.md) 同步更新。  
**最后更新**：按项目 CHANGELOG 维护。
