---
id: evidence:STD-TLA
title: TLA+ 行为与时序逻辑规约
version: V1.0
status: rc
category: 标准/方法
source: TLA+ (Leslie Lamport)
credibility: A
---

## 1. 基本信息

- **名称**：TLA+ (Temporal Logic of Actions)
- **作者/来源**：Leslie Lamport；[tlaplus.net](https://lamport.azurewebsites.net/tla/tla.html)
- **版本/日期**：TLA+2 现行；工具 TLA+ Toolbox 与 VS Code 插件维护中。
- **范围**：用时序逻辑与行为规约描述并发与分布式系统；支持模型检验（model checking）与求精（refinement）；适用于协议、算法、系统行为的正确性分析。
- **与本框架映射**：theory-enhancement/formal-verification；L2/L3 行为规约、并发与分布式；[L3_D08 测试标准模型](../L3_D08_测试标准模型.md) 中的形式化验证与模型检验。

## 2. 摘要

- TLA+ 的规约风格（状态、动作、时序公式、不变式、精化）与本框架 L2 元模型中的「不变式」「前置/后置条件」「状态迁移」对应；L3_D10 分布式模式中的一致性、容错、共识可用 TLA+ 建模与检验。
- 关键对齐：TLA+ 不变式 (Invariant) ↔ L2 各元模型不变式；TLA+ 精化 (Refinement) ↔ L2→L3 细化；模型检验 ↔ L3_D08 验证与确认及 [evidence:STD-1012](STD-1012.md)。

## 3. 对齐维度

- **术语对齐**：Specification ↔ 本框架「规格」；Invariant ↔ L2 不变式；Refinement ↔ L2→L3 细化；Model checking ↔ L3_D08 验证。
- **结构/接口**：TLA+ 模块与子模块可对应 formal-model 下各 theory 的规格片段；PlusCal 可对应流程/状态机描述。
- **约束/不变式**：TLA+ 的 INVARIANTS、PROPERTIES 与 L2/L3 文档中的形式化不变式可互相参照。
- **度量/指标**：模型检验的覆盖与状态空间与 L3_D08 的验证覆盖率、回归安全对应。

## 4. 映射

- **L2**：L2 各元模型中的形式化不变式、状态与操作；L2_D04 运行时、L2_D07 控制调度、L2_D08 测试。
- **L3**：[L3_D08 测试标准模型](../L3_D08_测试标准模型.md)、[L3_D10 分布式模式标准模型](../L3_D10_分布式模式标准模型.md)；[FORMAL_SPEC_LANGUAGES](../reference/FORMAL_SPEC_LANGUAGES.md)。
- **L4**：各行业中对并发与分布式行为有形式化需求的场景（云原生、Web3 共识等）。

## 5. 业界采用与 2024 社区调查

- **业界采用**：AWS 自 2011 年起将 TLA+ 用于复杂系统与公有云服务设计，公开分享其收益（形式化方法可发现其他手段难以发现的缺陷、投资回报良好）；Intel 在硬件设计中使用 TLA+，有项目在 RTL 实现前通过形式化验证发现数百个缺陷并达到最低缺陷率；Microsoft 亦有内部采用。TLA+ Foundation 作为非营利组织成立，成员包括 AWS、Oracle 等，旨在推动工业与学术界采用。
- **2024 社区调查要点**（来源：TLA+ 社区调查）：用户动机中约 53.7% 为对形式化方法的普遍兴趣，36.1% 通过学术/研究接触，25% 因 TLA+ 的缺陷发现能力；约 90% 用户反馈提升了对系统的理解；其他常见收益包括简洁性、表达力与工具支持。主要挑战包括学习曲线陡峭、调试能力有限、建模抽象难度及与其他工具的集成问题。
- 本条目被 [AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 2 节引用。

## 6. 引用

- **原文/官方**：[The TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)；[TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)；[TLA+ Tools](https://github.com/tlaplus/tlaplus)；[TLA+ Foundation](https://foundation.tlapl.us/)；工业采用案例见 [Industrial Use of TLA+](https://foundation.tlapl.us/industry/index.html)。
- **版本/日期**：TLA+2 现行；本条目核查日期 2025-02。
- **其他参考**：[reference/AUTHORITY_ALIGNMENT_INDEX](../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 2 节；[reference/FORMAL_SPEC_LANGUAGES](../reference/FORMAL_SPEC_LANGUAGES.md)。

## 7. 评审

- 评审人：待定
- 结论：待评审
- 备注：引用 TLA+ 时建议注明 Lamport 及 tlaplus.net；与 IEEE 1012 高完整性 V&V 方法对应。
