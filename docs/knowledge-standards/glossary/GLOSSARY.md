# 形式化框架术语表 (Glossary)

> **最后更新**: 2025-02-02  
> **维护者**: Formal Framework Team

## 概述

本文档是形式化框架项目的术语表，提供所有核心术语的中英文对照、形式化定义、使用场景和相关标准。

## 使用指南

- **查找术语**：按字母顺序查找，或使用浏览器搜索功能
- **理解定义**：查看形式化定义和通俗解释
- **应用场景**：了解术语的实际应用
- **相关标准**：查看相关的国际标准

## 术语索引

### A

#### 抽象语法树 (Abstract Syntax Tree, AST)

**英文**: Abstract Syntax Tree  
**缩写**: AST  
**分类**: 数据结构

**定义**: 源代码的树状表示，忽略语法细节，只保留程序的结构信息。

**形式化定义**:
```text
AST = (N, E, root, label)

其中：
- N: 节点集合
- E: 边集合（父子关系）
- root: 根节点
- label: 节点标签函数
```

**使用场景**:
- 代码生成
- 程序分析
- 代码转换
- IDE功能实现

**相关标准**:
- ECMAScript AST (ECMA-262)
- Python AST (PEP 339)

**相关概念**: [领域特定语言](#领域特定语言-domain-specific-language-dsl), [代码生成](#代码生成-code-generation)

---

#### 自动推理 (Automated Reasoning)

**英文**: Automated Reasoning  
**分类**: 验证方法

**定义**: 使用计算机自动进行逻辑推理的过程，包括定理证明、模型检验等。

**形式化定义**:
```text
AutomatedReasoning = (Knowledge, Rules, Inference, Conclusion)

其中：
- Knowledge: 知识库
- Rules: 推理规则
- Inference: 推理引擎
- Conclusion: 推理结论
```

**使用场景**:
- 定理证明
- 模型检验
- 程序验证
- 知识推理

**相关标准**:
- SMT-LIB标准
- TPTP标准

**相关概念**: [形式化验证](#形式化验证-formal-verification), [SAT求解器](#sat求解器-sat-solver)

---

#### 断言 (Assertion)

**英文**: Assertion  
**分类**: 测试 / 验证

**定义**: 对程序或系统在某一时刻应满足的条件的布尔表达式；用于测试用例中的预期结果判定，或形式化规格中的不变式/后置条件。

**使用场景**: 单元测试、契约测试、形式化验证、L3_D08 测试标准模型中的 TestCase.assertions。

**本框架映射**: [L3_D08 测试标准模型](../../L3_D08_测试标准模型.md)、[测试模型理论](../../formal-model/testing-model/theory.md)；与「不变式」的区别：断言多用于单次执行/用例级，不变式用于模型级约束。参见 [概念索引·测试模型](../concept-index/CONCEPT_INDEX.md#测试模型-testing-model)。

**相关概念**: [形式化验证](#形式化验证-formal-verification), [循环不变式](#循环不变式-loop-invariant)；测试模型见 [概念索引·测试模型](../concept-index/CONCEPT_INDEX.md#测试模型-testing-model)

---

### B

#### 业务逻辑 (Business Logic)

**英文**: Business Logic  
**分类**: 功能模型

**定义**: 描述业务规则和业务流程的逻辑。

**形式化定义**:
```text
BusinessLogic = (Rules, Workflow, StateMachine)

其中：
- Rules: 业务规则集合
- Workflow: 工作流定义
- StateMachine: 状态机定义
```

**使用场景**:
- 业务系统建模
- 规则引擎设计
- 工作流定义

**相关标准**:
- BPMN 2.0
- DMN (Decision Model and Notation)

**相关概念**: [功能模型](#功能模型-functional-model), [规则引擎](#规则引擎-rule-engine)

---

### C

#### 代码生成 (Code Generation)

**英文**: Code Generation  
**分类**: 工程实践

**定义**: 从形式化模型自动生成代码的过程。

**形式化定义**:
```text
CodeGeneration = (Model, Template, Generator, Code)

其中：
- Model: 形式化模型
- Template: 代码模板
- Generator: 生成器
- Code: 生成的代码
```

**使用场景**:
- 模型驱动工程
- 代码自动生成
- 模板引擎

**相关标准**:
- OMG MOF (Meta-Object Facility)
- Eclipse EMF

**相关概念**: [模型驱动工程](#模型驱动工程-model-driven-engineering-mde), [抽象语法树](#抽象语法树-abstract-syntax-tree-ast)

---

#### CTL (计算树逻辑)

**英文**: Computation Tree Logic  
**缩写**: CTL  
**分类**: 时序逻辑

**定义**: 用于描述计算树上性质的时序逻辑，区分路径量词和时序操作符。

**形式化定义**:
```text
CTL公式语法：
φ ::= p | ¬φ | φ₁ ∧ φ₂ | E φ | A φ | X φ | F φ | G φ | φ₁ U φ₂

其中：
- E: 存在路径
- A: 所有路径
- X, F, G, U: 时序操作符
```

**使用场景**:
- 模型检验
- 系统性质验证
- 并发系统验证

**相关标准**:
- IEEE 1012-2024

**相关概念**: [LTL](#ltl-线性时序逻辑), [时序逻辑](#时序逻辑-temporal-logic)

---

### D

#### 数据模型 (Data Model)

**英文**: Data Model  
**分类**: 建模概念

**定义**: 描述数据结构和数据关系的模型。

**形式化定义**:
```text
DataModel = (Entities, Relations, Constraints)

其中：
- Entities: 实体集合
- Relations: 关系集合
- Constraints: 约束集合
```

**使用场景**:
- 数据库设计
- 数据建模
- 数据迁移

**相关标准**:
- ER模型
- UML类图
- SQL标准

**相关概念**: [实体](#实体-entity), [关系](#关系-relation)

---

#### 领域特定语言 (Domain Specific Language, DSL)

**英文**: Domain Specific Language  
**缩写**: DSL  
**分类**: 语言设计

**定义**: 针对特定问题域设计的计算机语言。

**形式化定义**:
```text
DSL = (Syntax, Semantics, Domain)

其中：
- Syntax: 语法定义
- Semantics: 语义定义
- Domain: 问题域
```

**使用场景**:
- 领域建模
- 配置语言
- 查询语言

**相关标准**:
- ISO/IEC 14977 (EBNF)

**相关概念**: [抽象语法树](#抽象语法树-abstract-syntax-tree-ast), [代码生成](#代码生成-code-generation)

---

### F

#### 形式化建模 (Formal Modeling)

**英文**: Formal Modeling  
**分类**: 基础理论

**定义**: 使用数学符号和逻辑规则描述系统行为的方法。

**形式化定义**:
```text
FormalModel = (Syntax, Semantics, Axioms, Rules)

其中：
- Syntax: 语法定义
- Semantics: 语义定义
- Axioms: 公理集合
- Rules: 推理规则
```

**使用场景**:
- 系统建模
- 规范定义
- 系统验证

**相关标准**:
- Z Notation (ISO/IEC 13568)
- VDM (ISO/IEC 13817)

**相关概念**: [形式化验证](#形式化验证-formal-verification), [模型驱动工程](#模型驱动工程-model-driven-engineering-mde)

---

#### 形式化验证 (Formal Verification)

**英文**: Formal Verification  
**分类**: 验证方法

**定义**: 使用数学方法证明系统满足其规格说明的过程。

**形式化定义**:
```text
FormalVerification = (Specification, Model, Proof, Verification)

其中：
- Specification: 形式化规格说明
- Model: 系统模型
- Proof: 证明过程
- Verification: 验证结果
```

**使用场景**:
- 系统验证
- 安全证明
- 正确性保证

**相关标准**:
- IEEE 1012-2024
- ISO/IEC 15408

**相关概念**: [程序验证](#程序验证-program-verification), [模型检验](#模型检验-model-checking)

---

### H

#### Hoare逻辑 (Hoare Logic)

**英文**: Hoare Logic  
**分类**: 程序验证

**定义**: 用于程序验证的逻辑系统，使用Hoare三元组描述程序性质。

**形式化定义**:
```text
Hoare三元组：{P} S {Q}

其中：
- P: 前置条件
- S: 程序语句
- Q: 后置条件

含义：如果在执行S之前P成立，且S终止，则执行S后Q成立
```

**使用场景**:
- 程序正确性证明
- 程序验证
- 代码审查

**相关标准**:
- IEEE 1012-2024

**相关概念**: [程序验证](#程序验证-program-verification), [循环不变式](#循环不变式-loop-invariant)

---

### L

#### LTL (线性时序逻辑)

**英文**: Linear Temporal Logic  
**缩写**: LTL  
**分类**: 时序逻辑

**定义**: 用于描述线性执行路径上性质的时序逻辑。

**形式化定义**:
```text
LTL公式语法：
φ ::= p | ¬φ | φ₁ ∧ φ₂ | X φ | F φ | G φ | φ₁ U φ₂

其中：
- X: Next（下一个状态）
- F: Finally（最终）
- G: Globally（总是）
- U: Until（直到）
```

**使用场景**:
- 模型检验
- 反应式系统验证
- 并发系统验证

**相关标准**:
- IEEE 1012-2024

**相关概念**: [CTL](#ctl-计算树逻辑), [时序逻辑](#时序逻辑-temporal-logic)

---

#### 循环不变式 (Loop Invariant)

**英文**: Loop Invariant  
**分类**: 程序验证

**定义**: 在循环执行过程中始终保持为真的性质。

**形式化定义**:
```text
循环不变式P满足：
1. 初始化：循环开始前P成立
2. 保持：每次迭代后P仍成立
3. 终止：循环终止时能推出后置条件
```

**使用场景**:
- 循环正确性证明
- 程序验证
- 算法分析

**相关标准**:
- IEEE 1012-2024

**相关概念**: [Hoare逻辑](#hoare逻辑-hoare-logic), [程序验证](#程序验证-program-verification)

---

### M

#### 模型检验 (Model Checking)

**英文**: Model Checking  
**分类**: 验证方法

**定义**: 自动检查系统模型是否满足给定性质的方法。

**形式化定义**:
```text
ModelChecking = (Model, Property, Checker, Result)

其中：
- Model: 系统模型
- Property: 待验证性质
- Checker: 检验器
- Result: 检验结果
```

**使用场景**:
- 系统性质验证
- 并发系统验证
- 硬件验证

**相关标准**:
- IEEE 1012-2024

**相关概念**: [时序逻辑](#时序逻辑-temporal-logic), [形式化验证](#形式化验证-formal-verification)

---

#### 模型驱动工程 (Model Driven Engineering, MDE)

**英文**: Model Driven Engineering  
**缩写**: MDE  
**分类**: 工程实践

**定义**: 以模型为中心，通过模型转换自动生成代码的软件开发方法。

**形式化定义**:
```text
MDE = (Models, Transformations, Code)

其中：
- Models: 模型集合
- Transformations: 转换规则集合
- Code: 生成的代码
```

**使用场景**:
- 代码自动生成
- 模型转换
- 平台无关建模

**相关标准**:
- OMG MDA (Model Driven Architecture)
- OMG MOF

**相关概念**: [代码生成](#代码生成-code-generation), [模型转换](#模型转换-model-transformation)

---

### P

#### 程序验证 (Program Verification)

**英文**: Program Verification  
**分类**: 验证方法

**定义**: 使用数学方法证明程序正确性的过程。

**形式化定义**:
```text
ProgramVerification = (Program, Specification, Proof, Verification)

其中：
- Program: 程序代码
- Specification: 形式化规格说明
- Proof: 证明过程
- Verification: 验证结果
```

**使用场景**:
- 程序正确性证明
- 安全关键系统验证
- 代码审查

**相关标准**:
- IEEE 1012-2024
- SPARK语言标准

**相关概念**: [Hoare逻辑](#hoare逻辑-hoare-logic), [形式化验证](#形式化验证-formal-verification)

---

### S

#### SAT求解器 (SAT Solver)

**英文**: SAT Solver  
**分类**: 自动推理工具

**定义**: 用于求解布尔可满足性问题的工具。

**形式化定义**:
```text
SAT问题：给定布尔公式φ，判断是否存在赋值使得φ为真

SAT求解器：自动求解SAT问题的算法和工具
```

**使用场景**:
- 约束求解
- 模型检验
- 程序分析

**相关标准**:
- SMT-LIB标准
- DIMACS格式

**相关概念**: [SMT求解器](#smt求解器-smt-solver), [自动推理](#自动推理-automated-reasoning)

---

#### SMT求解器 (SMT Solver)

**英文**: SMT Solver  
**分类**: 自动推理工具

**定义**: 用于求解可满足性模理论问题的工具。

**形式化定义**:
```text
SMT问题：给定一阶逻辑公式φ和理论T，判断是否存在模型使得φ在T中可满足

SMT求解器：自动求解SMT问题的算法和工具
```

**使用场景**:
- 程序验证
- 约束求解
- 模型检验

**相关标准**:
- SMT-LIB标准

**相关概念**: [SAT求解器](#sat求解器-sat-solver), [自动推理](#自动推理-automated-reasoning)

---

### T

#### 状态机 (State Machine)

**英文**: State Machine / Finite State Machine (FSM)  
**分类**: 功能模型

**定义**: 由状态集合、转移条件与初始/终态组成的离散行为模型；在任意时刻处于唯一状态，事件触发后按转移规则迁移。

**使用场景**: 业务流程、协议行为、L2_D07 控制调度元模型与 L3_D03 功能标准模型中的状态机子域；与工作流、规则引擎并列于功能模型下。

**本框架映射**: [L2_D03 功能元模型](../../L2_D03_功能元模型.md)、[L2_D07 控制调度元模型](../../L2_D07_控制调度元模型.md)、[L3_D03 功能标准模型](../../L3_D03_功能标准模型.md)；[功能模型·状态机](../../formal-model/functional-model/state-machine/theory.md)。参见 [概念索引·功能模型](../concept-index/CONCEPT_INDEX.md#功能模型-functional-model)。

**相关概念**: [业务逻辑](#业务逻辑-business-logic), [规则引擎](#规则引擎-rule-engine), [工作流](../../formal-model/functional-model/workflow/theory.md)

---

#### 时序逻辑 (Temporal Logic)

**英文**: Temporal Logic  
**分类**: 逻辑理论

**定义**: 用于描述和推理系统随时间变化行为的模态逻辑。

**形式化定义**:
```text
时序逻辑扩展经典逻辑，增加时间相关的操作符：
- X: Next（下一个状态）
- F: Finally（最终）
- G: Globally（总是）
- U: Until（直到）
```

**使用场景**:
- 模型检验
- 反应式系统验证
- 并发系统验证

**相关标准**:
- IEEE 1012-2024

**相关概念**: [LTL](#ltl-线性时序逻辑), [CTL](#ctl-计算树逻辑)

---

### W

#### 最弱前置条件 (Weakest Precondition, WP)

**英文**: Weakest Precondition  
**缩写**: WP  
**分类**: 程序验证

**定义**: 使得程序执行后满足后置条件的最弱前置条件。

**形式化定义**:
```text
wp(S, Q) = 最弱的前置条件P，使得{P} S {Q}成立

性质：
- wp(S, Q) → P，对于所有满足{P} S {Q}的P
```

**使用场景**:
- 程序验证
- 程序推导
- 代码生成

**相关标准**:
- IEEE 1012-2024

**相关概念**: [Hoare逻辑](#hoare逻辑-hoare-logic), [程序验证](#程序验证-program-verification)

---

### 行业与云原生相关术语

#### VirtualService（虚拟服务）

**英文**: VirtualService  
**分类**: 云原生 / 服务网格

**定义**: Istio 中定义流量路由规则的对象，指定请求如何被路由到某一服务的不同版本或子集（如金丝雀、蓝绿）。

**使用场景**: 服务网格流量治理、金丝雀发布、A/B 测试。

**本框架映射**: [L3_D04 运行时标准模型](../../L3_D04_运行时标准模型.md) 服务网格路由；[云原生案例二：Service Mesh](../../industry-model/cloud-native-architecture/README.md#案例二service-mesh-流量治理istio)。

**相关概念**: [DestinationRule](#destinationrule目标规则), [金丝雀发布](#金丝雀发布-canary-release)

---

#### DestinationRule（目标规则）

**英文**: DestinationRule  
**分类**: 云原生 / 服务网格

**定义**: Istio 中定义到达目标服务后的流量策略（负载均衡、连接池、熔断、子集）的配置对象。

**使用场景**: 服务网格、弹性与容错策略。

**本框架映射**: [L3_D04 运行时标准模型](../../L3_D04_运行时标准模型.md)；[云原生案例二：Service Mesh](../../industry-model/cloud-native-architecture/README.md#案例二service-mesh-流量治理istio)。

**相关概念**: [VirtualService](#virtualservice虚拟服务), [熔断器](#熔断器-circuit-breaker)

---

#### GitOps

**英文**: GitOps  
**分类**: 云原生 / 部署

**定义**: 以 Git 为唯一事实来源的声明式持续交付方式：期望状态存于 Git，集群通过控制器与 Git 同步并自愈。

**使用场景**: 多环境部署、审计、回滚、质量门禁（如 PR 审批）。

**本框架映射**: [L3_D05 部署标准模型](../../L3_D05_部署标准模型.md)、[L3_D09 CI/CD 标准模型](../../L3_D09_CICD标准模型.md)；[云原生案例三：GitOps（ArgoCD）](../../industry-model/cloud-native-architecture/README.md#案例三gitops-持续交付argocd)。

**相关概念**: [部署模型](../../formal-model/deployment-model/theory.md), [CI/CD 模型](../../formal-model/cicd-model/theory.md)

---

#### 可观测性 (Observability)

**英文**: Observability  
**分类**: 可观测性 / 监控

**定义**: 通过外部输出（指标、日志、追踪等）推断系统内部状态的能力；通常归纳为 Metrics、Logs、Traces 三大支柱，辅以 Dashboard 与告警。

**使用场景**: 运维监控、故障诊断、SLO 管理、L3_D06 监控标准模型与 L4 各行业可观测性实践。

**本框架映射**: [L2_D06 监控元模型](../../L2_D06_监控元模型.md)、[L3_D06 监控标准模型](../../L3_D06_监控标准模型.md)、[监控模型理论](../../formal-model/monitoring-model/theory.md)；[概念索引·监控模型](../concept-index/CONCEPT_INDEX.md#监控模型-monitoring-model)。云原生见 [案例四：可观测性](../../industry-model/cloud-native-architecture/README.md#案例四可观测性一体化prometheusotel)。

**相关概念**: [SLO（服务等级目标）](#slo服务等级目标), [监控模型](../../formal-model/monitoring-model/theory.md)

---

#### SLO（服务等级目标）

**英文**: Service Level Objective  
**缩写**: SLO  
**分类**: 可观测性 / 监控

**定义**: 服务等级目标的量化指标（如可用性 99.9%、P99 延迟 &lt; 500ms），用于驱动告警与容量规划。

**使用场景**: 监控、告警、容量与稳定性管理。

**本框架映射**: [L3_D06 监控标准模型](../../L3_D06_监控标准模型.md)；[云原生案例四：可观测性](../../industry-model/cloud-native-architecture/README.md#案例四可观测性一体化prometheusotel)。

**相关概念**: [可观测性](#可观测性-observability)、监控模型、SLI（服务等级指标）；[监控模型](../../formal-model/monitoring-model/theory.md)

---

#### FaaS（函数即服务）

**英文**: Function as a Service  
**缩写**: FaaS  
**分类**: 云原生 / Serverless

**定义**: 以函数为部署与计费单位的云服务形态；由事件触发，自动扩缩容，按调用与执行时长计费。

**使用场景**: 事件驱动、API 后端、定时任务、轻量计算。

**本框架映射**: [L3_D04 运行时标准模型](../../L3_D04_运行时标准模型.md)、[L3_D03 功能标准模型](../../L3_D03_功能标准模型.md)；[云原生案例五：Serverless](../../industry-model/cloud-native-architecture/README.md#案例五serverless-函数计算aws-lambdaknative)。

**相关概念**: [Serverless](../../industry-model/cloud-native-architecture/serverless/theory.md), [冷启动](#冷启动-cold-start)

---

#### 冷启动 (Cold Start)

**英文**: Cold Start  
**分类**: 云原生 / Serverless

**定义**: 函数实例从零启动或从休眠恢复时的延迟，影响首请求或低频调用的响应时间。

**使用场景**: Serverless 性能优化、预留并发与预热策略。

**本框架映射**: [L3_D04 运行时标准模型](../../L3_D04_运行时标准模型.md)；[云原生案例五：Serverless](../../industry-model/cloud-native-architecture/README.md#案例五serverless-函数计算aws-lambdaknative)。

**相关概念**: [FaaS](#faas函数即服务), [弹性伸缩](../../formal-model/runtime-model/theory.md)

---

#### 金丝雀发布 (Canary Release)

**英文**: Canary Release  
**分类**: 云原生 / 部署与流量

**定义**: 将小比例流量导向新版本，观察指标与错误率后再逐步放量的发布策略。

**使用场景**: 服务网格、API 网关、蓝绿/金丝雀发布。

**本框架映射**: [L3_D01 交互标准模型](../../L3_D01_交互标准模型.md)、[L3_D04 运行时标准模型](../../L3_D04_运行时标准模型.md)；[云原生案例二：Service Mesh](../../industry-model/cloud-native-architecture/README.md#案例二service-mesh-流量治理istio)、[案例六：API 网关](../../industry-model/cloud-native-architecture/README.md#案例六api-网关流量治理kongenvoy)。

**相关概念**: [VirtualService](#virtualservice虚拟服务), [蓝绿发布](https://martinfowler.com/bliki/BlueGreenDeployment.html)

---

#### 熔断器 (Circuit Breaker)

**英文**: Circuit Breaker  
**分类**: 分布式 / 弹性

**定义**: 当下游失败率或延迟超过阈值时，暂时拒绝请求并快速失败，避免级联故障的模式。

**使用场景**: 服务间调用、API 网关、服务网格。

**本框架映射**: [L3_D04 运行时标准模型](../../L3_D04_运行时标准模型.md)、[L3_D10 分布式模式标准模型](../../L3_D10_分布式模式标准模型.md)；[云原生案例二、案例六](../../industry-model/cloud-native-architecture/README.md)。

**相关概念**: [DestinationRule](#destinationrule目标规则), [重试与超时](../../formal-model/distributed-pattern-model/theory.md)

---

## 术语分类

### 按类别分类

#### 基础理论
- [形式化建模](#形式化建模-formal-modeling)
- [形式化验证](#形式化验证-formal-verification)
- [时序逻辑](#时序逻辑-temporal-logic)

#### 数据结构
- [抽象语法树](#抽象语法树-abstract-syntax-tree-ast)

#### 语言设计
- [领域特定语言](#领域特定语言-domain-specific-language-dsl)

#### 验证方法
- [自动推理](#自动推理-automated-reasoning)
- [程序验证](#程序验证-program-verification)
- [模型检验](#模型检验-model-checking)
- [Hoare逻辑](#hoare逻辑-hoare-logic)

#### 时序逻辑
- [LTL](#ltl-线性时序逻辑)
- [CTL](#ctl-计算树逻辑)

#### 建模概念
- [数据模型](#数据模型-data-model)
- [业务逻辑](#业务逻辑-business-logic)

#### 工程实践
- [代码生成](#代码生成-code-generation)
- [模型驱动工程](#模型驱动工程-model-driven-engineering-mde)

#### 工具
- [SAT求解器](#sat求解器-sat-solver)
- [SMT求解器](#smt求解器-smt-solver)

#### 云原生 / 行业
- [VirtualService](#virtualservice虚拟服务)
- [DestinationRule](#destinationrule目标规则)
- [GitOps](#gitops)
- [SLO（服务等级目标）](#slo服务等级目标)
- [FaaS（函数即服务）](#faas函数即服务)
- [冷启动](#冷启动-cold-start)
- [金丝雀发布](#金丝雀发布-canary-release)
- [熔断器](#熔断器-circuit-breaker)

## 相关文档

- [概念索引](../concept-index/CONCEPT_INDEX.md)
- [学习路径](../../LEARNING_PATHS.md)
- [概念关系图谱](../concept-maps/CONCEPT_MAPS.md)

---

**维护说明**：本术语表应定期更新，确保所有新术语及时添加，定义准确性和完整性保持95%以上。
