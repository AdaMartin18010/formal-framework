# 业务逻辑建模DSL草案

## 1. 设计目标

- 用统一DSL描述顺序、分支、并发、循环、补偿等业务流程要素。
- 支持自动生成BPMN、UML活动图、工作流引擎配置等。

## 2. 基本语法结构

```dsl
process OrderProcess {
  start: CreateOrder
  state CreateOrder {
    on event OrderCreated => PayOrder
  }
  state PayOrder {
    on event PaymentSuccess => ShipOrder
    on event PaymentFail => CancelOrder
  }
  state ShipOrder {
    on event Shipped => Complete
  }
  state CancelOrder {
    on event Cancelled => End
    compensation: Refund
  }
  state Complete {
    on event Done => End
  }
}
```

## 3. 关键元素

- process/state：流程与状态定义
- on event：事件触发
- compensation：补偿动作
- 并发/分支/循环：可扩展结构

## 4. 常用流程结构声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| process OrderProcess { ... }                  | 流程定义       |
| state PayOrder { ... }                        | 状态/节点定义  |
| on event PaymentSuccess => ShipOrder          | 事件转移       |
| compensation: Refund                          | 补偿动作       |
| parallel { TaskA, TaskB }                     | 并发结构       |
| branch { if cond => A; else => B }            | 条件分支       |
| loop { Task while cond }                      | 循环结构       |

## 5. 与主流标准的映射

- 可自动转换为BPMN、UML活动图、Camunda/Activiti等配置
- 支持与主流工作流引擎集成

## 6. 递归扩展建议

- 支持复杂嵌套、子流程、动态分支
- 支持异常处理与补偿机制
