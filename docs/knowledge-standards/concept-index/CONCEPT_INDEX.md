# 形式化框架概念索引 (Formal Framework Concept Index)

> **最后更新**: 2025-02-02  
> **维护者**: Formal Framework Team

本文档是按**字母顺序**的形式化框架概念索引（定义位置、前置知识、自测问句、概念页入口）。侧重**概念索引与关系的理论**（关系图谱、分类体系、国际标准/名校对标、工程实践）的文档见 [概念索引与关系](../../formal-model/core-concepts/concept-index.md)；两文档互为补充，避免混淆。

## 概述

本文档是形式化框架项目的核心概念索引，按字母顺序组织所有核心概念，提供快速查找和学习路径导航。

## 使用指南

- **查找概念**：按字母顺序查找，或使用浏览器搜索功能
- **学习路径**：查看每个概念的前置知识和学习顺序
- **概念页与定义位置**：**有独立概念页**的概念（如形式化建模、数据模型、形式化验证等）在 `concepts/` 目录下有详细索引页，可点击进入；**无独立概念页**的概念（如业务逻辑、CI/CD 模型等）仅在本表中列出，其「定义位置」指向首次定义与完整讲解所在的文档，请以定义位置为准。审稿与补充时可按优先级为高引用概念新增概念页。
- **自测问句与主动回忆**：所有带自测问句的概念见 [自测问句汇总](#自测问句汇总便于检索与主动回忆)；建议**先写再对**（先凭记忆写一句答案再核对）。为高引用概念补自测问句的认领与验收见该节维护说明及 [RECURSIVE_IMPROVEMENT_KANBAN](../../RECURSIVE_IMPROVEMENT_KANBAN.md) §4.1。

## 概念索引

### A

#### [抽象语法树 (Abstract Syntax Tree)](./concepts/abstract-syntax-tree.md)

- **定义位置**: `docs/formal-model/core-concepts/abstract-syntax-tree.md`
- **首次引入**: 第2章 理论基础
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [解析器理论](../../formal-model/core-concepts/domain-specific-language.md#解析器生成)（定义位置：DSL 文档）
- **相关概念**: [领域特定语言](#领域特定语言-domain-specific-language), [代码生成](#代码生成-code-generation), [语义分析](#语义分析-semantic-analysis)
- **应用场景**: 代码生成、模型解析、程序分析
- **学习时间**: 约2-3小时
- **自测问句**: DSL 与 AST 的关系是什么？AST 在代码生成或模型解析中扮演什么角色？

#### [自动推理 (Automated Reasoning)](./concepts/automated-reasoning.md)

- **定义位置**: `docs/formal-model/core-concepts/automated-reasoning.md`
- **首次引入**: 第3章 验证方法
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [逻辑学基础](#逻辑学-logic), [形式化验证](#形式化验证-formal-verification)
- **相关概念**: [形式化验证](#形式化验证-formal-verification), [知识图谱](#知识图谱-knowledge-graph), [语义分析](#语义分析-semantic-analysis)
- **应用场景**: 定理证明、模型检验、智能推理
- **学习时间**: 约4-5小时
- **自测问句**: SAT/SMT 求解器在本框架中对应哪些验证活动？自动推理与 L3_D08 测试标准模型的关系是什么？

### B

#### [不变式 (Invariant)](../../formal-model/alignment-L2-L3-matrix.md)

- **定义位置**: [L2↔L3 映射总表](../../formal-model/alignment-L2-L3-matrix.md) 各节「不变式映射」；与「断言」的区分见 [术语表·断言](../glossary/GLOSSARY.md)
- **首次引入**: L2/L3 元模型与标准模型中的形式化约束
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling)
- **相关概念**: [契约](#契约-contract)、[形式化验证](#形式化验证-formal-verification)、[测试模型](#测试模型-testing-model)；循环不变式见 [术语表·循环不变式](../glossary/GLOSSARY.md#循环不变式-loop-invariant)
- **应用场景**: 模型级约束、规格与验证；与单次执行/用例级「断言」区分
- **自测问句**: 本框架中「不变式」与「断言」分别对应哪些文档与活动？

#### [业务逻辑 (Business Logic)](../../formal-model/functional-model/business-logic/theory.md)

- **定义位置**: `docs/formal-model/functional-model/business-logic/theory.md`
- **首次引入**: L2元模型 - 功能模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [功能建模](#功能建模-functional-modeling)
- **相关概念**: [规则引擎](#规则引擎-rule-engine), [状态机](#状态机-state-machine), [工作流](#工作流-workflow)
- **应用场景**: 业务系统建模、规则定义、流程设计
- **学习时间**: 约1-2小时
- **自测问句**: 业务逻辑与规则引擎、工作流在本框架中的边界是什么？分别对应 L2/L3 的哪些文档？

### C

#### [代码生成 (Code Generation)](./concepts/code-generation.md)

- **定义位置**: `docs/formal-model/core-concepts/code-generation.md`
- **首次引入**: 第4章 代码生成
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [抽象语法树](#抽象语法树-abstract-syntax-tree), [领域特定语言](#领域特定语言-domain-specific-language)
- **相关概念**: [模型驱动工程](#模型驱动工程-model-driven-engineering), [模型转换](#模型转换-model-transformation)
- **应用场景**: 代码自动生成、模板引擎、代码重构
- **学习时间**: 约3-4小时
- **自测问句**: 从模型到代码的生成在本框架中依赖哪些概念（如 AST、DSL、模型转换）？与 L3 标准模型的关系是什么？
- **详细索引**: [查看详细索引页](./concepts/code-generation.md)

#### [CI/CD模型 (CI/CD Model)](../../formal-model/cicd-model/theory.md)

- **定义位置**: `docs/formal-model/cicd-model/theory.md`
- **首次引入**: L3标准模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [部署模型](#部署模型-deployment-model), [测试模型](#测试模型-testing-model)
- **相关概念**: [部署模型](#部署模型-deployment-model), [测试模型](#测试模型-testing-model), [监控模型](#监控模型-monitoring-model)
- **应用场景**: 持续集成、持续部署、DevOps
- **学习时间**: 约2-3小时
- **自测问句**: L3_D09 CI/CD 标准模型中的流水线阶段、门禁与 ISO/IEC/IEEE 15288 生命周期过程的对应关系是什么？

### D

#### [数据模型 (Data Model)](./concepts/data-model.md)

- **定义位置**: `docs/formal-model/data-model/theory.md`
- **首次引入**: L2元模型 - 数据模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [数据库理论](../../formal-model/data-model/theory.md#72-数据库标准)（定义位置：数据模型理论）, [关系模型](../../formal-model/data-model/theory.md#91-数据建模设计模式)（定义位置：数据模型理论）
- **相关概念**: [实体模型](#实体-entity), [查询模型](#查询-query), [索引模型](#索引-index)
- **应用场景**: 数据库设计、数据建模、数据迁移
- **学习时间**: 约2小时
- **自测问句**: 能否举一个「行业模型映射到通用数据模型」的例子（如金融账户、AI 特征表）？

#### [部署模型 (Deployment Model)](./concepts/deployment-model.md)

- **定义位置**: `docs/formal-model/deployment-model/theory.md`
- **首次引入**: L2元模型 - 部署模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [运行时模型](#运行时模型-runtime-model), [基础设施](#基础设施-infrastructure)
- **相关概念**: [运行时模型](#运行时模型-runtime-model), [配置管理](#配置-configuration), [版本控制](#版本-version)
- **应用场景**: 系统部署、基础设施管理、版本管理
- **学习时间**: 约2-3小时
- **自测问句**: 部署模型与运行时模型、L3_D05 部署标准模型的关系是什么？配置与版本在本框架中如何体现？

#### [分布式模式模型 (Distributed Pattern Model)](../../formal-model/distributed-pattern-model/theory.md)

- **定义位置**: `docs/formal-model/distributed-pattern-model/theory.md`
- **首次引入**: L3标准模型
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [运行时模型](#运行时模型-runtime-model), [交互模型](#交互模型-interaction-model)
- **相关概念**: [容错模式](#容错-fault-tolerance), [一致性](#一致性-consistency), [负载均衡](#负载均衡-load-balancing)
- **应用场景**: 分布式系统设计、微服务架构、高可用系统
- **学习时间**: 约4-5小时
- **自测问句**: L3_D10 分布式模式标准模型与各 L4 行业（云原生、金融、IoT、Web3）的映射关系是什么？能举一例吗？

#### [领域特定语言 (Domain Specific Language)](./concepts/domain-specific-language.md)

- **定义位置**: `docs/formal-model/core-concepts/domain-specific-language.md`
- **首次引入**: 第2章 理论基础
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [语言设计](#语言设计-language-design)
- **相关概念**: [抽象语法树](#抽象语法树-abstract-syntax-tree), [代码生成](#代码生成-code-generation), [模型驱动工程](#模型驱动工程-model-driven-engineering)
- **应用场景**: DSL设计、领域建模、代码生成
- **学习时间**: 约3-4小时
- **自测问句**: DSL 与 AST 的关系是什么？本框架各 theory/dsl-draft 中的 DSL 片段分别对应哪个 L2/L3 模型？
- **详细索引**: [查看详细索引页](./concepts/domain-specific-language.md)

### F

#### [形式化建模 (Formal Modeling)](./concepts/formal-modeling.md)

- **定义位置**: `docs/formal-model/core-concepts/formal-modeling.md`
- **首次引入**: 第1章 基础理论
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [数学基础](#数学-mathematics), [逻辑学](#逻辑学-logic)
- **相关概念**: [形式化验证](#形式化验证-formal-verification), [模型驱动工程](#模型驱动工程-model-driven-engineering)
- **应用场景**: 系统建模、规范定义、系统验证
- **学习时间**: 约3-4小时
- **自测问句**: 能否用一句话说明「形式化建模」在本框架中指的是什么？数据、功能、交互三个元模型分别解决什么问题？
- **详细索引**: [查看详细索引页](./concepts/formal-modeling.md)

#### [形式化验证 (Formal Verification)](./concepts/formal-verification.md)

- **定义位置**: `docs/formal-model/core-concepts/formal-verification.md`
- **首次引入**: 第3章 验证方法
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [逻辑学](#逻辑学-logic)
- **相关概念**: [自动推理](#自动推理-automated-reasoning), [模型检验](#模型检验-model-checking), [定理证明](#定理证明-theorem-proving)
- **应用场景**: 系统验证、安全证明、正确性保证
- **学习时间**: 约4-5小时
- **自测问句**: 形式化验证在本框架中与 L3_D08 测试标准模型、IEEE 1012 V&V 的对应关系是什么？定理证明、模型检验、SMT 分别对应哪些文档？
- **详细索引**: [查看详细索引页](./concepts/formal-verification.md)

#### [功能模型 (Functional Model)](./concepts/functional-model.md)

- **定义位置**: `docs/formal-model/functional-model/theory.md`
- **首次引入**: L2元模型 - 功能模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [业务逻辑](#业务逻辑-business-logic)
- **相关概念**: [业务逻辑](#业务逻辑-business-logic), [状态机](#状态机-state-machine), [工作流](#工作流-workflow), [规则引擎](#规则引擎-rule-engine)
- **应用场景**: 业务建模、流程设计、规则定义
- **学习时间**: 约2小时
- **自测问句**: 业务逻辑、规则引擎、状态机、工作流在本框架中分别对应哪些子模型或 L3 标准？

### I

#### [交互模型 (Interaction Model)](./concepts/interaction-model.md)

- **定义位置**: `docs/formal-model/interaction-model/theory.md`
- **首次引入**: L2元模型 - 交互模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [API设计](#api-design), [协议设计](#协议-protocol)
- **相关概念**: [API模型](#api-model), [契约模型](#契约-contract), [消息模型](#消息-message)
- **应用场景**: API设计、服务接口、消息传递
- **学习时间**: 约2小时
- **自测问句**: 能用自己的话解释「交互模型」与「运行时模型」的区别吗？API 契约应归入哪一层？
- **易混概念**: 与 [运行时模型](#运行时模型-runtime-model) 的边界：交互模型聚焦**契约、API、协议与消息格式**（L3_D01）；运行时模型聚焦**容器、编排、工作负载与运行时资源**（L3_D04）。流量治理若涉及协议/契约属 L3_D01，若涉及 Pod/Service 编排属 L3_D04。详见 [L3_D01 交互标准模型](../../L3_D01_交互标准模型.md)、[L3_D04 运行时标准模型](../../L3_D04_运行时标准模型.md) 概述中的「与 L3 边界」。

#### [行业映射 (Industry Mapping)](../../formal-model/core-concepts/industry-mapping.md)

- **定义位置**: `docs/formal-model/core-concepts/industry-mapping.md`
- **首次引入**: L4行业模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [行业知识](#行业知识-industry-knowledge)
- **相关概念**: [云原生架构](#云原生-cloud-native), [金融架构](#金融-finance), [IoT架构](#iot-architecture)
- **应用场景**: 行业标准对齐、跨行业映射、最佳实践
- **学习时间**: 约3-4小时
- **自测问句**: 能否举一个「行业模型映射到通用 L2/L3 模型」的例子（如云原生 K8s 对应 L3_D04，金融支付对应 L3_D01/L3_D08）？

### K

#### [知识图谱 (Knowledge Graph)](../../formal-model/core-concepts/knowledge-graph.md)

- **定义位置**: `docs/formal-model/core-concepts/knowledge-graph.md`
- **首次引入**: 第5章 知识组织
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [图论](#图论-graph-theory), [知识表示](#知识表示-knowledge-representation)
- **相关概念**: [自动推理](#自动推理-automated-reasoning), [语义分析](#语义分析-semantic-analysis)
- **应用场景**: 知识组织、智能检索、关系推理
- **学习时间**: 约3-4小时
- **自测问句**: 本框架中概念索引、术语表与「知识图谱」的关系是什么？知识图谱如何支持 L2/L3 概念的关系推理？

### M

#### [模型驱动工程 (Model Driven Engineering)](../../formal-model/core-concepts/model-driven-engineering.md)

- **定义位置**: `docs/formal-model/core-concepts/model-driven-engineering.md`
- **首次引入**: 第4章 代码生成
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [代码生成](#代码生成-code-generation)
- **相关概念**: [模型转换](#模型转换-model-transformation), [领域特定语言](#领域特定语言-domain-specific-language)
- **应用场景**: 模型到代码转换、自动化开发、代码生成
- **学习时间**: 约4-5小时
- **自测问句**: MDE 在本框架中与 L2 元模型、L3 标准模型、DSL 的对应关系是什么？模型转换的输入输出分别是什么？

#### [模型转换 (Model Transformation)](../../formal-model/core-concepts/model-transformation.md)

- **定义位置**: `docs/formal-model/core-concepts/model-transformation.md`
- **首次引入**: 第4章 代码生成
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [模型驱动工程](#模型驱动工程-model-driven-engineering)
- **相关概念**: [模型驱动工程](#模型驱动工程-model-driven-engineering), [代码生成](#代码生成-code-generation)
- **应用场景**: 模型转换、代码生成、模型重构
- **学习时间**: 约3-4小时
- **自测问句**: 模型转换与代码生成在本框架中的边界是什么？L2→L3、L3→行业模型的映射属于模型转换吗？

#### [监控模型 (Monitoring Model)](./concepts/monitoring-model.md)

- **定义位置**: `docs/formal-model/monitoring-model/theory.md`
- **首次引入**: L2元模型 - 监控模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [运行时模型](#运行时模型-runtime-model), [可观测性](#可观测性-observability)
- **相关概念**: [指标模型](#指标-metrics), [告警模型](#告警-alerting), [日志模型](#日志-logs), [追踪模型](#追踪-tracing)
- **应用场景**: 系统监控、性能分析、故障诊断
- **学习时间**: 约2-3小时
- **自测问句**: 监控模型与 L3_D06 监控标准模型、可观测性（指标/日志/追踪）的对应关系是什么？SLO 在本框架中属于哪一层？

### Q

#### [契约 (Contract)](./concepts/contract.md)

- **定义位置**: `docs/formal-model/interaction-model/contract/theory.md`
- **首次引入**: L2 元模型 - 交互模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [交互模型](#交互模型-interaction-model)、[API 设计](../../formal-model/interaction-model/api/theory.md)
- **相关概念**: [交互模型](#交互模型-interaction-model)、[API 模型](#api-model)、[消息模型](#消息-message)
- **应用场景**: API 契约设计、接口规范、Design by Contract
- **学习时间**: 约 1–2 小时
- **自测问句**: API 契约应归入 L2 还是 L3？OpenAPI、gRPC 契约在本框架中对应哪个标准模型？
- **详细索引**: [查看详细索引页](./concepts/contract.md)

### R

#### [规则引擎 (Rule Engine)](./concepts/rule-engine.md)

- **定义位置**: `docs/formal-model/functional-model/rule-engine/theory.md`
- **首次引入**: L2 元模型 - 功能模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [功能模型](#功能模型-functional-model)、[业务逻辑](#业务逻辑-business-logic)
- **相关概念**: [业务逻辑](#业务逻辑-business-logic)、[状态机](#状态机-state-machine)、[工作流](#工作流-workflow)
- **应用场景**: 规则与决策建模、风控/合规引擎
- **学习时间**: 约 2–3 小时
- **自测问句**: 规则引擎与工作流、状态机在 L2_D03 功能元模型中的边界是什么？对应 L3_D03 的哪些对象？
- **详细索引**: [查看详细索引页](./concepts/rule-engine.md)

#### [递归建模 (Recursive Modeling)](../../formal-model/core-concepts/recursive-modeling.md)

- **定义位置**: `docs/formal-model/core-concepts/recursive-modeling.md`
- **首次引入**: 第2章 理论基础
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [递归理论](#递归理论-recursion-theory)
- **相关概念**: [形式化建模](#形式化建模-formal-modeling), [模型转换](#模型转换-model-transformation)
- **应用场景**: 复杂系统建模、递归结构定义、模型扩展
- **学习时间**: 约4-5小时
- **自测问句**: 本框架中「递归扩展路径」指什么？L2→L3→L4 与行业子模型的递归细分如何对应？

#### [运行时模型 (Runtime Model)](./concepts/runtime-model.md)

- **定义位置**: `docs/formal-model/runtime-model/theory.md`
- **首次引入**: L2元模型 - 运行时模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [容器技术](#容器-container), [编排](#编排-orchestration)
- **相关概念**: [容器模型](#容器-container), [编排模型](#编排-orchestration), [网络模型](#网络-network), [存储模型](#存储-storage)
- **应用场景**: 容器编排、资源管理、运行时环境
- **学习时间**: 约2-3小时
- **自测问句**: 能区分「API 网关的契约设计」与「API 网关的部署与副本数」分别对应哪个模型吗？
- **易混概念**: 与 [交互模型](#交互模型-interaction-model) 的边界：运行时模型描述**载体与执行环境**（容器、Pod、Service、编排）；交互模型描述**接口与协议**（OpenAPI、gRPC、消息格式）。详见 [L3_D04 运行时标准模型](../../L3_D04_运行时标准模型.md)、[L3_D01 交互标准模型](../../L3_D01_交互标准模型.md) 概述中的「与 L3 边界」。

### W

#### [工作流 (Workflow)](./concepts/workflow.md)

- **定义位置**: `docs/formal-model/functional-model/workflow/theory.md`
- **首次引入**: L2 元模型 - 功能模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [功能模型](#功能模型-functional-model)、[业务逻辑](#业务逻辑-business-logic)
- **相关概念**: [业务逻辑](#业务逻辑-business-logic)、[规则引擎](#规则引擎-rule-engine)、[状态机](#状态机-state-machine)
- **应用场景**: 业务流程建模、流水线设计、任务编排
- **学习时间**: 约 2–3 小时
- **自测问句**: 工作流与 BPMN、L3_D03 功能标准模型的关系是什么？CI/CD 流水线属于工作流还是部署模型？
- **详细索引**: [查看详细索引页](./concepts/workflow.md)

### S

#### [语义分析 (Semantic Analysis)](../../formal-model/core-concepts/semantic-analysis.md)

- **定义位置**: `docs/formal-model/core-concepts/semantic-analysis.md`
- **首次引入**: 第3章 验证方法
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [抽象语法树](#抽象语法树-abstract-syntax-tree), [形式化验证](#形式化验证-formal-verification)
- **相关概念**: [抽象语法树](#抽象语法树-abstract-syntax-tree), [形式化验证](#形式化验证-formal-verification), [自动推理](#自动推理-automated-reasoning)
- **应用场景**: 代码分析、语义检查、类型推断
- **学习时间**: 约3-4小时
- **自测问句**: 语义分析与 AST、形式化验证在本框架中的关系是什么？与 L3_D08 测试中的断言、契约检查有何联系？

### T

#### [测试模型 (Testing Model)](./concepts/testing-model.md)

- **定义位置**: `docs/formal-model/testing-model/theory.md`
- **首次引入**: L2元模型 - 测试模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [软件测试](#软件测试-software-testing), [测试理论](#测试理论-testing-theory)
- **相关概念**: [测试用例](#测试用例-test-case), [断言](#断言-assertion), [覆盖率](#覆盖率-coverage)
- **应用场景**: 测试设计、测试自动化、质量保证
- **学习时间**: 约2小时
- **自测问句**: 测试模型与 L3_D08 测试标准模型、IEEE 1012 V&V 的对应关系是什么？断言与不变式在本框架中如何区分？

## 自测问句汇总（便于检索与主动回忆） {#自测问句汇总便于检索与主动回忆}

以下为所有带「自测问句」的概念，建议**先写再对**（先凭记忆写一句答案，再点开定义位置核对）。用法见 [learning/LEARNING_AND_REVIEW_TIPS](../../learning/LEARNING_AND_REVIEW_TIPS.md) 与 [REVIEW_CHECKLIST](../../learning/REVIEW_CHECKLIST.md)。维护：每半年可为 2–3 个高引用概念补自测问句并同步更新本表；认领任务见 [RECURSIVE_IMPROVEMENT_KANBAN](../../RECURSIVE_IMPROVEMENT_KANBAN.md) §4.1 概念与术语。

| 概念 | 自测问句（要点） |
|------|------------------|
| [形式化建模](#形式化建模-formal-modeling) | 一句话说明形式化建模；数据/功能/交互三块分别解决什么 |
| [数据模型](#数据模型-data-model) | 行业模型映射到通用数据模型的例子 |
| [功能模型](#功能模型-functional-model) | 业务逻辑、规则引擎、状态机、工作流对应哪些子模型或 L3 |
| [交互模型](#交互模型-interaction-model) | 交互模型与运行时模型区别；API 契约归哪一层 |
| [运行时模型](#运行时模型-runtime-model) | API 网关契约设计 vs 部署与副本数分别对应哪个模型 |
| [测试模型](#测试模型-testing-model) | 测试模型与 L3_D08、IEEE 1012 对应；断言与不变式区分 |
| [抽象语法树](#抽象语法树-abstract-syntax-tree) | DSL 与 AST 关系；AST 在代码生成中的角色 |
| [自动推理](#自动推理-automated-reasoning) | SAT/SMT 对应哪些验证活动；与 L3_D08 关系 |
| [不变式](#不变式-invariant) | 本框架中不变式与断言分别对应哪些文档与活动 |
| [业务逻辑](#业务逻辑-business-logic) | 业务逻辑与规则引擎、工作流边界；对应 L2/L3 文档 |
| [代码生成](#代码生成-code-generation) | 模型到代码依赖哪些概念；与 L3 关系 |
| [CI/CD模型](#cicd模型-cicd-model) | L3_D09 与 15288 生命周期对应关系 |
| [部署模型](#部署模型-deployment-model) | 部署与运行时、L3_D05 关系；配置与版本如何体现 |
| [分布式模式模型](#分布式模式模型-distributed-pattern-model) | L3_D10 与各 L4 行业映射；举一例 |
| [领域特定语言](#领域特定语言-domain-specific-language) | DSL 与 AST 关系；各 dsl-draft 对应哪个 L2/L3 |
| [形式化验证](#形式化验证-formal-verification) | 与 L3_D08、IEEE 1012 对应；定理证明/模型检验/SMT 对应文档 |
| [行业映射](#行业映射-industry-mapping) | 行业模型映射到 L2/L3 的例子 |
| [知识图谱](#知识图谱-knowledge-graph) | 概念索引、术语表与知识图谱关系；如何支持关系推理 |
| [模型驱动工程](#模型驱动工程-model-driven-engineering) | MDE 与 L2/L3、DSL 对应；模型转换输入输出 |
| [模型转换](#模型转换-model-transformation) | 模型转换与代码生成边界；L2→L3 是否属于模型转换 |
| [监控模型](#监控模型-monitoring-model) | 与 L3_D06、可观测性对应；SLO 属于哪一层 |
| [契约](#契约-contract) | API 契约归 L2 还是 L3；OpenAPI/gRPC 对应哪个标准模型 |
| [规则引擎](#规则引擎-rule-engine) | 与工作流、状态机在 L2_D03 的边界；对应 L3_D03 哪些对象 |
| [递归建模](#递归建模-recursive-modeling) | 递归扩展路径指什么；L2→L3→L4 递归细分如何对应 |
| [工作流](#工作流-workflow) | 工作流与 BPMN、L3_D03 关系；CI/CD 流水线属工作流还是部署模型 |
| [语义分析](#语义分析-semantic-analysis) | 与 AST、形式化验证关系；与 L3_D08 断言、契约检查联系 |
| [测试模型](#测试模型-testing-model) | 与 L3_D08、IEEE 1012 对应；断言与不变式区分 |
| 术语表补充：状态机、断言、可观测性 | 状态机对应哪些 L2/L3；断言 vs 不变式；可观测性对应哪个 L2/L3 模型（见下方术语表补充） |

## 概念分类索引

### 基础理论概念

- [形式化建模](#形式化建模-formal-modeling)
- [形式化验证](#形式化验证-formal-verification)
- [不变式](#不变式-invariant)
- [自动推理](#自动推理-automated-reasoning)
- [抽象语法树](#抽象语法树-abstract-syntax-tree)
- [领域特定语言](#领域特定语言-domain-specific-language)

### 建模概念

- [数据模型](#数据模型-data-model)
- [功能模型](#功能模型-functional-model)
- [交互模型](#交互模型-interaction-model)
- [契约](#契约-contract)
- [规则引擎](#规则引擎-rule-engine)
- [工作流](#工作流-workflow)
- [运行时模型](#运行时模型-runtime-model)
- [部署模型](#部署模型-deployment-model)
- [监控模型](#监控模型-monitoring-model)
- [测试模型](#测试模型-testing-model)

### 工程实践概念

- [代码生成](#代码生成-code-generation)
- [模型驱动工程](#模型驱动工程-model-driven-engineering)
- [模型转换](#模型转换-model-transformation)
- [CI/CD模型](#cicd模型-cicd-model)
- [分布式模式模型](#分布式模式模型-distributed-pattern-model)

### 知识组织概念

- [知识图谱](#知识图谱-knowledge-graph)
- [行业映射](#行业映射-industry-mapping)
- [递归建模](#递归建模-recursive-modeling)
- [语义分析](#语义分析-semantic-analysis)

### 云原生/行业概念（详见术语表）

以下概念在 [术语表 (Glossary)](../glossary/GLOSSARY.md) 中有定义并与 L3/L4 映射：**VirtualService**、**DestinationRule**、**GitOps**、**SLO**、**FaaS**、**冷启动**、**金丝雀发布**、**熔断器**。应用场景见 [云原生行业模型](../../industry-model/cloud-native-architecture/README.md)。

### 术语表补充（无独立概念页，以术语表为准）

以下概念被多处引用，定义与 L2/L3 映射见 [术语表 (Glossary)](../glossary/GLOSSARY.md)：**状态机**（State Machine）、**断言**（Assertion）、**可观测性**（Observability）。状态机对应 L2_D03/L2_D07、L3_D03；断言对应 L3_D08 测试与形式化规格；可观测性对应 L2_D06、L3_D06 及行业可观测性实践。

**自测问句（高引用术语，先写再对）**：① 状态机在本框架中对应哪些 L2/L3 文档？与工作流、规则引擎的边界是什么？② 断言与不变式分别对应哪些文档与活动（单次执行/用例级 vs 模型级）？③ 可观测性的指标/日志/追踪在本框架中对应哪个 L2/L3 模型？

## 学习路径建议

### 初学者路径

1. [形式化建模](#形式化建模-formal-modeling) →
2. [数据模型](#数据模型-data-model) →
3. [功能模型](#功能模型-functional-model) →
4. [交互模型](#交互模型-interaction-model) →
5. [测试模型](#测试模型-testing-model)

### 进阶路径

1. [抽象语法树](#抽象语法树-abstract-syntax-tree) →
2. [领域特定语言](#领域特定语言-domain-specific-language) →
3. [代码生成](#代码生成-code-generation) →
4. [模型驱动工程](#模型驱动工程-model-driven-engineering)

### 专家路径

1. [形式化验证](#形式化验证-formal-verification) →
2. [自动推理](#自动推理-automated-reasoning) →
3. [递归建模](#递归建模-recursive-modeling) →
4. [行业映射](#行业映射-industry-mapping)

## 相关文档

- [学习路径文档](../../LEARNING_PATHS.md)
- [术语表](../glossary/GLOSSARY.md)
- [概念关系图谱](../concept-maps/CONCEPT_MAPS.md)
- [详细概念索引页](./concepts/)

---

**维护说明**: 本索引应定期更新，确保所有新概念及时添加，链接有效性保持95%以上。
