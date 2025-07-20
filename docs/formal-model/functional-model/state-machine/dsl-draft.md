# 状态机建模DSL草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述状态、事件、转移、动作、嵌套子状态、并发、异常处理等要素，支持递归组合。
- 支持自动生成代码、流程引擎配置、可视化状态图等。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 基本语法结构

```dsl
state_machine OrderStatus {
  states: [ created, paid, shipped, delivered, cancelled ]
  transitions: [
    { from: created, to: paid, trigger: payment_success },
    { from: paid, to: shipped, trigger: shipping_started },
    { from: shipped, to: delivered, trigger: delivery_confirmed },
    { from: any, to: cancelled, trigger: order_cancelled }
  ]
}
```

## 3. 关键元素

- state_machine：状态机声明
- states：状态集合（支持嵌套、并发）
- transitions：转移规则（支持条件、动作、异常处理）
- trigger：触发事件
- entry/exit：进入/离开动作
- permission/audit：权限与审计

## 4. 高级用法与递归扩展

### 4.1 嵌套子状态与分层状态机

```dsl
state_machine DeliveryProcess {
  states: [
    pending,
    in_progress {
      substates: [ picking, packing, shipping ]
      initial: picking
      transitions: [
        { from: picking, to: packing, trigger: picked },
        { from: packing, to: shipping, trigger: packed }
      ]
    },
    completed
  ]
  transitions: [
    { from: pending, to: in_progress, trigger: start },
    { from: in_progress, to: completed, trigger: delivered }
  ]
}
```

### 4.2 并发与分支状态

```dsl
state_machine PaymentAndShipping {
  states: [
    payment {
      substates: [ waiting, paid ]
    },
    shipping {
      substates: [ pending, shipped ]
    }
  ]
  parallel: [ payment, shipping ]
  transitions: [
    { from: payment.waiting, to: payment.paid, trigger: payment_success },
    { from: shipping.pending, to: shipping.shipped, trigger: shipping_started }
  ]
}
```

### 4.3 异常处理与补偿

```dsl
state_machine RefundProcess {
  states: [ requested, processing, refunded, failed ]
  transitions: [
    { from: requested, to: processing, trigger: start },
    { from: processing, to: refunded, trigger: success },
    { from: processing, to: failed, trigger: error, on_error: send_notification(admin, "退款失败") }
  ]
}
```

### 4.4 权限与安全声明

```dsl
state_machine SensitiveFlow {
  states: [ start, sensitive_action, end ]
  transitions: [
    { from: start, to: sensitive_action, trigger: request, permission: "admin_only", audit: true },
    { from: sensitive_action, to: end, trigger: complete }
  ]
}
```

### 4.5 AI自动化与智能状态机生成

```dsl
# 支持AI自动生成状态机
ai_state_machine "为订单系统自动生成完整的订单状态流转" {
  domain: "order"
  optimize: true
}
```

## 5. 与主流标准的映射

- 可自动转换为UML状态图、SCXML、Spring StateMachine等配置
- 可生成代码、API、可视化状态图
- 支持权限、安全、审计策略自动生成

## 6. 递归扩展建议

- 支持多层嵌套状态、并发、分支、异常处理、补偿机制
- 支持AI自动生成与优化状态机
- 支持多系统集成、分布式状态机、变更影响分析
- 支持状态安全、权限、审计、数据脱敏
- 支持状态机性能分析、监控与自动优化

## 7. 工程实践示例

```dsl
state_machine UserLifecycle {
  states: [ registered, activated, suspended, deleted ]
  transitions: [
    { from: registered, to: activated, trigger: activate },
    { from: activated, to: suspended, trigger: suspend },
    { from: suspended, to: activated, trigger: reactivate },
    { from: any, to: deleted, trigger: delete, permission: "admin_only", audit: true }
  ]
}
```

---
