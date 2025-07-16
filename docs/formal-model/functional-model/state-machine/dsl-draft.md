# 状态机建模DSL草案

## 1. 设计目标

- 用统一DSL描述有限状态机、层次状态机、并发状态机等要素。
- 支持自动生成UML状态图、SCXML、XState等配置。

## 2. 基本语法结构

```dsl
statemachine OrderFSM {
  initial: Created
  state Created {
    on event Pay => Paid
  }
  state Paid {
    on event Ship => Shipped
    on event Cancel => Cancelled
  }
  state Shipped {
    on event Complete => Completed
  }
  state Cancelled {
    on event Refund => Refunded
  }
  state Completed {}
  state Refunded {}
}
```

## 3. 关键元素

- statemachine/state：状态机与状态定义
- on event：事件触发转移
- initial：初始状态
- 并发/嵌套/动作：可扩展结构

## 4. 常用状态机声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| statemachine OrderFSM { ... }                 | 状态机定义     |
| state Paid { ... }                            | 状态定义       |
| on event Pay => Paid                          | 事件转移       |
| initial: Created                              | 初始状态       |
| parallel { StateA, StateB }                   | 并发状态       |
| submachine { ... }                            | 子状态机/嵌套  |

## 5. 与主流标准的映射

- 可自动转换为UML状态图、SCXML、XState等配置
- 支持与主流状态机工具集成

## 6. 递归扩展建议

- 支持复杂嵌套、并发、动作与条件转移
- 支持状态机可视化与自动化测试
