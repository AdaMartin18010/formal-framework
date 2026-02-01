# 形式化框架概念索引 (Formal Framework Concept Index)

> **最后更新**: 2025-02-02  
> **维护者**: Formal Framework Team

## 概述

本文档是形式化框架项目的核心概念索引，按字母顺序组织所有核心概念，提供快速查找和学习路径导航。

## 使用指南

- **查找概念**：按字母顺序查找，或使用浏览器搜索功能
- **学习路径**：查看每个概念的前置知识和学习顺序
- **详细索引**：点击概念名称查看详细索引页（位于 `concepts/` 目录）

## 概念索引

### A

#### [抽象语法树 (Abstract Syntax Tree)](./concepts/abstract-syntax-tree.md)

- **定义位置**: `docs/formal-model/core-concepts/abstract-syntax-tree.md`
- **首次引入**: 第2章 理论基础
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [解析器理论](#解析器-parser)
- **相关概念**: [领域特定语言](#领域特定语言-domain-specific-language), [代码生成](#代码生成-code-generation), [语义分析](#语义分析-semantic-analysis)
- **应用场景**: 代码生成、模型解析、程序分析
- **学习时间**: 约2-3小时

#### [自动推理 (Automated Reasoning)](./concepts/automated-reasoning.md)

- **定义位置**: `docs/formal-model/core-concepts/automated-reasoning.md`
- **首次引入**: 第3章 验证方法
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [逻辑学基础](#逻辑学-logic), [形式化验证](#形式化验证-formal-verification)
- **相关概念**: [形式化验证](#形式化验证-formal-verification), [知识图谱](#知识图谱-knowledge-graph), [语义分析](#语义分析-semantic-analysis)
- **应用场景**: 定理证明、模型检验、智能推理
- **学习时间**: 约4-5小时

### B

#### [业务逻辑 (Business Logic)](./concepts/business-logic.md)

- **定义位置**: `docs/formal-model/functional-model/business-logic/theory.md`
- **首次引入**: L2元模型 - 功能模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [功能建模](#功能建模-functional-modeling)
- **相关概念**: [规则引擎](#规则引擎-rule-engine), [状态机](#状态机-state-machine), [工作流](#工作流-workflow)
- **应用场景**: 业务系统建模、规则定义、流程设计
- **学习时间**: 约1-2小时

### C

#### [代码生成 (Code Generation)](./concepts/code-generation.md)

- **定义位置**: `docs/formal-model/core-concepts/code-generation.md`
- **首次引入**: 第4章 代码生成
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [抽象语法树](#抽象语法树-abstract-syntax-tree), [领域特定语言](#领域特定语言-domain-specific-language)
- **相关概念**: [模型驱动工程](#模型驱动工程-model-driven-engineering), [模型转换](#模型转换-model-transformation)
- **应用场景**: 代码自动生成、模板引擎、代码重构
- **学习时间**: 约3-4小时
- **详细索引**: [查看详细索引页](./concepts/code-generation.md)

#### [CI/CD模型 (CI/CD Model)](./concepts/cicd-model.md)

- **定义位置**: `docs/formal-model/cicd-model/theory.md`
- **首次引入**: L3标准模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [部署模型](#部署模型-deployment-model), [测试模型](#测试模型-testing-model)
- **相关概念**: [部署模型](#部署模型-deployment-model), [测试模型](#测试模型-testing-model), [监控模型](#监控模型-monitoring-model)
- **应用场景**: 持续集成、持续部署、DevOps
- **学习时间**: 约2-3小时

### D

#### [数据模型 (Data Model)](./concepts/data-model.md)

- **定义位置**: `docs/formal-model/data-model/theory.md`
- **首次引入**: L2元模型 - 数据模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [数据库理论](#数据库-database), [关系模型](#关系模型-relational-model)
- **相关概念**: [实体模型](#实体-entity), [查询模型](#查询-query), [索引模型](#索引-index)
- **应用场景**: 数据库设计、数据建模、数据迁移
- **学习时间**: 约2小时

#### [部署模型 (Deployment Model)](./concepts/deployment-model.md)

- **定义位置**: `docs/formal-model/deployment-model/theory.md`
- **首次引入**: L2元模型 - 部署模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [运行时模型](#运行时模型-runtime-model), [基础设施](#基础设施-infrastructure)
- **相关概念**: [运行时模型](#运行时模型-runtime-model), [配置管理](#配置-configuration), [版本控制](#版本-version)
- **应用场景**: 系统部署、基础设施管理、版本管理
- **学习时间**: 约2-3小时

#### [分布式模式模型 (Distributed Pattern Model)](./concepts/distributed-pattern-model.md)

- **定义位置**: `docs/formal-model/distributed-pattern-model/theory.md`
- **首次引入**: L3标准模型
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [运行时模型](#运行时模型-runtime-model), [交互模型](#交互模型-interaction-model)
- **相关概念**: [容错模式](#容错-fault-tolerance), [一致性](#一致性-consistency), [负载均衡](#负载均衡-load-balancing)
- **应用场景**: 分布式系统设计、微服务架构、高可用系统
- **学习时间**: 约4-5小时

#### [领域特定语言 (Domain Specific Language)](./concepts/domain-specific-language.md)

- **定义位置**: `docs/formal-model/core-concepts/domain-specific-language.md`
- **首次引入**: 第2章 理论基础
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [语言设计](#语言设计-language-design)
- **相关概念**: [抽象语法树](#抽象语法树-abstract-syntax-tree), [代码生成](#代码生成-code-generation), [模型驱动工程](#模型驱动工程-model-driven-engineering)
- **应用场景**: DSL设计、领域建模、代码生成
- **学习时间**: 约3-4小时
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
- **详细索引**: [查看详细索引页](./concepts/formal-modeling.md)

#### [形式化验证 (Formal Verification)](./concepts/formal-verification.md)

- **定义位置**: `docs/formal-model/core-concepts/formal-verification.md`
- **首次引入**: 第3章 验证方法
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [逻辑学](#逻辑学-logic)
- **相关概念**: [自动推理](#自动推理-automated-reasoning), [模型检验](#模型检验-model-checking), [定理证明](#定理证明-theorem-proving)
- **应用场景**: 系统验证、安全证明、正确性保证
- **学习时间**: 约4-5小时
- **详细索引**: [查看详细索引页](./concepts/formal-verification.md)

#### [功能模型 (Functional Model)](./concepts/functional-model.md)

- **定义位置**: `docs/formal-model/functional-model/theory.md`
- **首次引入**: L2元模型 - 功能模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [业务逻辑](#业务逻辑-business-logic)
- **相关概念**: [业务逻辑](#业务逻辑-business-logic), [状态机](#状态机-state-machine), [工作流](#工作流-workflow), [规则引擎](#规则引擎-rule-engine)
- **应用场景**: 业务建模、流程设计、规则定义
- **学习时间**: 约2小时

### I

#### [交互模型 (Interaction Model)](./concepts/interaction-model.md)

- **定义位置**: `docs/formal-model/interaction-model/theory.md`
- **首次引入**: L2元模型 - 交互模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [API设计](#api-design), [协议设计](#协议-protocol)
- **相关概念**: [API模型](#api-model), [契约模型](#契约-contract), [消息模型](#消息-message)
- **应用场景**: API设计、服务接口、消息传递
- **学习时间**: 约2小时

#### [行业映射 (Industry Mapping)](./concepts/industry-mapping.md)

- **定义位置**: `docs/formal-model/core-concepts/industry-mapping.md`
- **首次引入**: L4行业模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [行业知识](#行业知识-industry-knowledge)
- **相关概念**: [云原生架构](#云原生-cloud-native), [金融架构](#金融-finance), [IoT架构](#iot-architecture)
- **应用场景**: 行业标准对齐、跨行业映射、最佳实践
- **学习时间**: 约3-4小时

### K

#### [知识图谱 (Knowledge Graph)](./concepts/knowledge-graph.md)

- **定义位置**: `docs/formal-model/core-concepts/knowledge-graph.md`
- **首次引入**: 第5章 知识组织
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [图论](#图论-graph-theory), [知识表示](#知识表示-knowledge-representation)
- **相关概念**: [自动推理](#自动推理-automated-reasoning), [语义分析](#语义分析-semantic-analysis)
- **应用场景**: 知识组织、智能检索、关系推理
- **学习时间**: 约3-4小时

### M

#### [模型驱动工程 (Model Driven Engineering)](./concepts/model-driven-engineering.md)

- **定义位置**: `docs/formal-model/core-concepts/model-driven-engineering.md`
- **首次引入**: 第4章 代码生成
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [代码生成](#代码生成-code-generation)
- **相关概念**: [模型转换](#模型转换-model-transformation), [领域特定语言](#领域特定语言-domain-specific-language)
- **应用场景**: 模型到代码转换、自动化开发、代码生成
- **学习时间**: 约4-5小时

#### [模型转换 (Model Transformation)](./concepts/model-transformation.md)

- **定义位置**: `docs/formal-model/core-concepts/model-transformation.md`
- **首次引入**: 第4章 代码生成
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [模型驱动工程](#模型驱动工程-model-driven-engineering)
- **相关概念**: [模型驱动工程](#模型驱动工程-model-driven-engineering), [代码生成](#代码生成-code-generation)
- **应用场景**: 模型转换、代码生成、模型重构
- **学习时间**: 约3-4小时

#### [监控模型 (Monitoring Model)](./concepts/monitoring-model.md)

- **定义位置**: `docs/formal-model/monitoring-model/theory.md`
- **首次引入**: L2元模型 - 监控模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [运行时模型](#运行时模型-runtime-model), [可观测性](#可观测性-observability)
- **相关概念**: [指标模型](#指标-metrics), [告警模型](#告警-alerting), [日志模型](#日志-logs), [追踪模型](#追踪-tracing)
- **应用场景**: 系统监控、性能分析、故障诊断
- **学习时间**: 约2-3小时

### R

#### [递归建模 (Recursive Modeling)](./concepts/recursive-modeling.md)

- **定义位置**: `docs/formal-model/core-concepts/recursive-modeling.md`
- **首次引入**: 第2章 理论基础
- **难度等级**: ⭐⭐⭐⭐ (高级)
- **前置知识**: [形式化建模](#形式化建模-formal-modeling), [递归理论](#递归理论-recursion-theory)
- **相关概念**: [形式化建模](#形式化建模-formal-modeling), [模型转换](#模型转换-model-transformation)
- **应用场景**: 复杂系统建模、递归结构定义、模型扩展
- **学习时间**: 约4-5小时

#### [运行时模型 (Runtime Model)](./concepts/runtime-model.md)

- **定义位置**: `docs/formal-model/runtime-model/theory.md`
- **首次引入**: L2元模型 - 运行时模型
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [容器技术](#容器-container), [编排](#编排-orchestration)
- **相关概念**: [容器模型](#容器-container), [编排模型](#编排-orchestration), [网络模型](#网络-network), [存储模型](#存储-storage)
- **应用场景**: 容器编排、资源管理、运行时环境
- **学习时间**: 约2-3小时

### S

#### [语义分析 (Semantic Analysis)](./concepts/semantic-analysis.md)

- **定义位置**: `docs/formal-model/core-concepts/semantic-analysis.md`
- **首次引入**: 第3章 验证方法
- **难度等级**: ⭐⭐⭐ (中级)
- **前置知识**: [抽象语法树](#抽象语法树-abstract-syntax-tree), [形式化验证](#形式化验证-formal-verification)
- **相关概念**: [抽象语法树](#抽象语法树-abstract-syntax-tree), [形式化验证](#形式化验证-formal-verification), [自动推理](#自动推理-automated-reasoning)
- **应用场景**: 代码分析、语义检查、类型推断
- **学习时间**: 约3-4小时

### T

#### [测试模型 (Testing Model)](./concepts/testing-model.md)

- **定义位置**: `docs/formal-model/testing-model/theory.md`
- **首次引入**: L2元模型 - 测试模型
- **难度等级**: ⭐⭐ (初级)
- **前置知识**: [软件测试](#软件测试-software-testing), [测试理论](#测试理论-testing-theory)
- **相关概念**: [测试用例](#测试用例-test-case), [断言](#断言-assertion), [覆盖率](#覆盖率-coverage)
- **应用场景**: 测试设计、测试自动化、质量保证
- **学习时间**: 约2小时

## 概念分类索引

### 基础理论概念

- [形式化建模](#形式化建模-formal-modeling)
- [形式化验证](#形式化验证-formal-verification)
- [自动推理](#自动推理-automated-reasoning)
- [抽象语法树](#抽象语法树-abstract-syntax-tree)
- [领域特定语言](#领域特定语言-domain-specific-language)

### 建模概念

- [数据模型](#数据模型-data-model)
- [功能模型](#功能模型-functional-model)
- [交互模型](#交互模型-interaction-model)
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
