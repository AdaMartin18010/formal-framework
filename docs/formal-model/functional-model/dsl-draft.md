# 功能模型DSL草案

## 1. 设计目标

- 用统一DSL描述业务逻辑、状态机、工作流、规则等功能要素。
- 支持自动生成业务代码、流程图、规则引擎配置等。

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
  }
  state Complete {
    on event Done => End
  }
}

rule DiscountRule {
  when order.amount > 1000
  then order.discount = 0.1
}
```

## 3. 关键元素

- process/state：流程与状态定义
- event：事件触发
- rule：规则定义
- when/then：规则条件与动作
- action：可选动作块

## 4. 示例

```dsl
process UserRegister {
  start: InputInfo
  state InputInfo {
    on event InfoSubmitted => Validate
  }
  state Validate {
    on event Valid => Register
    on event Invalid => InputInfo
  }
  state Register {
    on event Registered => End
  }
}

rule AgeCheck {
  when user.age < 18
  then reject("未成年人禁止注册")
}
```

## 5. 与主流标准的映射

- 可自动转换为BPMN、UML状态机、Drools规则等格式
- 支持与工作流引擎、规则引擎集成

## 6. 递归扩展建议

- 支持并发、分支、子流程等复杂流程结构
- 支持规则优先级、分组、动态加载
- 支持异常处理与补偿机制
