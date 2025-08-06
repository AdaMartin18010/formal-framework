# Formal Model 通用形式化建模体系

## 目录导航

### 核心模型

- **data-model/** - 数据建模
  - entity/ - 实体建模
  - index/ - 索引建模  
  - migration/ - 迁移建模
  - query/ - 查询建模
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

- **functional-model/** - 功能建模
  - business-logic/ - 业务逻辑
  - rule-engine/ - 规则引擎
  - state-machine/ - 状态机
  - workflow/ - 工作流
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

- **interaction-model/** - 交互建模
  - api/ - API建模
  - contract/ - 契约建模
  - message/ - 消息建模
  - protocol/ - 协议建模
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

- **runtime-model/** - 运行时建模
  - container/ - 容器建模
  - network/ - 网络建模
  - orchestration/ - 编排建模
  - storage/ - 存储建模
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

- **deployment-model/** - 部署建模
  - configuration/ - 配置建模
  - infrastructure/ - 基础设施建模
  - rollback/ - 回滚建模
  - version/ - 版本建模
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

- **monitoring-model/** - 监控建模
  - alerting/ - 告警建模
  - logs/ - 日志建模
  - metrics/ - 指标建模
  - tracing/ - 追踪建模
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

- **testing-model/** - 测试建模
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

- **cicd-model/** - CI/CD建模
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

- **distributed-pattern-model/** - 分布式模式建模
  - dsl-draft.md - DSL草案
  - theory.md - 理论说明

## 递归扩展原则

每个模型都支持递归扩展，可以不断细分为更具体的子模型。例如：

- data-model → entity → field → constraint → validation
- functional-model → business-logic → rule → condition → action
- interaction-model → api → endpoint → parameter → response

## 行业映射

通用模型可以与行业模型进行映射：

- data-model ↔ finance-architecture/core-banking
- functional-model ↔ ai-infrastructure-architecture/feature-store
- interaction-model ↔ cloud-native-architecture/api-gateway

## 自动化推理

每个模型都支持自动化推理和代码生成：

- DSL → SQL DDL
- DSL → API代码
- DSL → 测试用例
- DSL → 部署配置

## 贡献指南

1. 选择要完善的模型或子模型
2. 补充 dsl-draft.md 和 theory.md 内容
3. 添加自动化推理伪代码
4. 提供行业映射案例
5. 提交PR并等待评审

## 快速开始

1. 阅读 docs/README.md 了解整体架构
2. 选择感兴趣的模型开始探索
3. 参考行业模型了解实际应用
4. 参与社区讨论和贡献
