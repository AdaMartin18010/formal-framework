---
id: evidence:STD-ALLOY
title: Alloy 关系逻辑与轻量形式化分析
version: V1.0
status: rc
category: 标准/方法
source: Alloy (Daniel Jackson et al.)
credibility: A
---

## 1. 基本信息

- **名称**：Alloy（关系逻辑建模语言与分析器）
- **来源**：Daniel Jackson（MIT）；[alloytools.org](https://alloytools.org/)
- **版本/日期**：Alloy 4.x / Alloy 6 现行；工具与文档以官网为准。
- **范围**：用关系逻辑与一阶逻辑描述结构、约束与行为；通过有界模型检验（SAT 求解）查找反例、验证性质；适用于软件与系统结构建模、DSL 与配置分析。
- **与本框架映射**：theory-enhancement、DSL 分析；L2 关系与结构、轻量形式化；[L3_D08 测试标准模型](../L3_D08_测试标准模型.md) 中的轻量验证。

## 2. 摘要

- Alloy 的「签名 (Signature)」「关系」「约束」「断言/谓词」与本框架 L2 元模型中的实体、属性、关系、不变式对应；适合对 L2 数据模型、交互模型等做结构一致性与约束的可执行检查。
- 关键对齐：Alloy 签名与域 ↔ L2 Entity/Field/Relation；Alloy 事实 (fact) ↔ L2 不变式；run/check ↔ L3_D08 验证与反例生成；与 [reference/FORMAL_SPEC_LANGUAGES](../reference/FORMAL_SPEC_LANGUAGES.md) 中「轻量形式化」分支一致。

## 3. 对齐维度

- **术语对齐**：Signature ↔ L2 实体/类型；Fact ↔ L2 不变式；Assertion ↔ 可验证性质；Instance ↔ 模型实例/反例。
- **结构/接口**：Alloy 模块可对应 formal-model 下 data-model、interaction-model 等 theory 的结构化规格；与 DSL 设计 (dsl-draft.md) 可互相参照。
- **约束/不变式**：Alloy 的 fact、pred、assert 与 L2/L3 文档中的形式化约束可对照。
- **度量/指标**：有界检验的范围与反例数量与 L3_D08 的验证覆盖、缺陷发现对应。

## 4. 映射

- **L2**：L2_D02 数据元模型、L2_D01 交互元模型（结构、关系、约束）；L2 各元模型中的轻量形式化片段。
- **L3**：[L3_D02 数据标准模型](../L3_D02_数据标准模型.md)、[L3_D01 交互标准模型](../L3_D01_交互标准模型.md)、[L3_D08 测试标准模型](../L3_D08_测试标准模型.md)；[FORMAL_SPEC_LANGUAGES](../reference/FORMAL_SPEC_LANGUAGES.md)。
- **L4**：各行业中对数据结构与契约有一致性分析需求的场景（如 API 契约、配置模型）。

## 5. 引用

- **原文/官方**：[Alloy Tools](https://alloytools.org/)；*Software Abstractions* (Daniel Jackson, MIT Press)。
- **版本/日期**：Alloy 4/6 现行；本条目核查日期 2025-02。
- **其他参考**：[reference/AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 2 节；[reference/FORMAL_SPEC_LANGUAGES](../reference/FORMAL_SPEC_LANGUAGES.md)。

## 6. 评审

- 评审人：待定
- 结论：待评审
- 备注：与 TLA+（偏行为与时序）互补；Alloy 侧重结构与关系，适合 L2 结构不变式的快速分析。
