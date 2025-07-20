# 工作流建模DSL草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述流程、任务、分支、并发、子流程、补偿、异常处理等要素，支持递归组合。
- 支持自动生成BPMN、Camunda、Argo Workflows等配置与代码。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 基本语法结构

```dsl
workflow OrderFulfillment {
  start: CreateOrder
  tasks: [
    CreateOrder {
      next: [ Payment ]
    },
    Payment {
      next: [ ShipOrder, CancelOrder ]
      on_error: [ CancelOrder ]
    },
    ShipOrder {
      next: [ Complete ]
    },
    CancelOrder {
      end: true
      compensation: Refund
    },
    Complete {
      end: true
    },
    Refund {
      end: true
    }
  ]
}
```

## 3. 关键元素

- workflow：工作流声明
- tasks：任务节点（支持嵌套、并发、子流程）
- next：下一个任务/分支
- on_error/compensation：异常处理与补偿
- parallel/branch：并发与分支结构
- permission/audit：权限与审计

## 4. 高级用法与递归扩展

### 4.1 嵌套子流程与分层工作流

```dsl
workflow ProjectDelivery {
  start: Planning
  tasks: [
    Planning {
      next: [ Development ]
    },
    Development {
      subflow: DevWorkflow
      next: [ Testing ]
    },
    Testing {
      next: [ Release ]
    },
    Release {
      end: true
    }
  ]
}

workflow DevWorkflow {
  start: Coding
  tasks: [
    Coding {
      next: [ CodeReview ]
    },
    CodeReview {
      next: [ Merge ]
    },
    Merge {
      end: true
    }
  ]
}
```

### 4.2 并发与分支流程

```dsl
workflow ParallelApproval {
  start: Submit
  tasks: [
    Submit {
      next: [ [ ManagerApproval, FinanceApproval ] ] # 并发
    },
    ManagerApproval {
      next: [ Finalize ]
    },
    FinanceApproval {
      next: [ Finalize ]
    },
    Finalize {
      end: true
    }
  ]
}
```

### 4.3 补偿与异常处理

```dsl
workflow PaymentProcess {
  start: Pay
  tasks: [
    Pay {
      next: [ Confirm ]
      on_error: [ Rollback ]
    },
    Confirm {
      end: true
    },
    Rollback {
      compensation: Refund
      end: true
    },
    Refund {
      end: true
    }
  ]
}
```

### 4.4 权限与安全声明

```dsl
workflow SensitiveOperation {
  start: Request
  tasks: [
    Request {
      next: [ Approve ]
      permission: "admin_only"
      audit: true
    },
    Approve {
      end: true
    }
  ]
}
```

### 4.5 AI自动化与智能工作流生成

```dsl
# 支持AI自动生成工作流
ai_workflow "为电商系统自动生成订单履约全流程" {
  domain: "ecommerce"
  optimize: true
}
```

## 5. 与主流标准的映射

- 可自动转换为BPMN、Camunda、Argo Workflows等配置
- 可生成代码、API、可视化流程图
- 支持权限、安全、审计策略自动生成

## 6. 递归扩展建议

- 支持多层嵌套子流程、并发、分支、补偿、异常处理
- 支持AI自动生成与优化工作流
- 支持多系统集成、分布式工作流、变更影响分析
- 支持流程安全、权限、审计、数据脱敏
- 支持流程性能分析、监控与自动优化

## 7. 工程实践示例

```dsl
workflow LeaveApproval {
  start: Apply
  tasks: [
    Apply {
      next: [ [ ManagerApprove, HRApprove ] ]
    },
    ManagerApprove {
      next: [ FinalApprove ]
    },
    HRApprove {
      next: [ FinalApprove ]
    },
    FinalApprove {
      end: true
      permission: "hr_manager"
      audit: true
    }
  ]
}
```

---
