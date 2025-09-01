# 功能模型DSL设计 (Functional Model DSL Design)

## 概述

功能模型DSL是一种专门用于描述和管理业务逻辑、规则引擎、状态机、工作流等功能的领域特定语言。它提供声明式语法来定义业务功能、处理流程、决策逻辑和状态转换，支持从简单业务规则到复杂工作流的各种场景。

## 设计原则

### 核心原则

1. **声明式设计**：使用声明式语法描述业务逻辑，而非命令式代码
2. **业务导向**：以业务需求为中心，而非技术实现
3. **可组合性**：支持功能模块的组合和重用
4. **可测试性**：便于单元测试和集成测试
5. **可维护性**：易于理解和维护的业务逻辑

### 设计模式

```yaml
# 设计模式
design_patterns:
  business_rule_pattern:
    description: "业务规则模式"
    benefits:
      - "清晰的业务逻辑"
      - "易于维护"
      - "可重用性"
    example: |
      rule "discount_rule" {
        description: "折扣规则"
        conditions: [
          "customer.type == 'VIP'"
          "order.total_amount >= 1000"
        ]
        actions: [
          "apply_discount(0.15)"
          "add_loyalty_points(100)"
        ]
        priority: 1
      }
      
  state_machine_pattern:
    description: "状态机模式"
    benefits:
      - "清晰的状态转换"
      - "事件驱动"
      - "状态管理"
    example: |
      state_machine "order_processing" {
        initial_state: "pending"
        states: [
          {
            name: "pending"
            description: "待处理"
            actions: ["validate_order", "check_inventory"]
            transitions: [
              { event: "order_validated", target: "confirmed" }
              { event: "validation_failed", target: "cancelled" }
            ]
          },
          {
            name: "confirmed"
            description: "已确认"
            actions: ["process_payment", "prepare_shipment"]
            transitions: [
              { event: "payment_successful", target: "shipped" }
              { event: "payment_failed", target: "cancelled" }
            ]
          }
        ]
      }
      
  workflow_pattern:
    description: "工作流模式"
    benefits:
      - "流程自动化"
      - "任务分配"
      - "流程监控"
    example: |
      workflow "approval_process" {
        description: "审批流程"
        steps: [
          {
            name: "submit"
            description: "提交申请"
            actor: "applicant"
            next: "review"
          },
          {
            name: "review"
            description: "部门审核"
            actor: "department_manager"
            next: "approve"
            conditions: ["amount <= 10000"]
          },
          {
            name: "approve"
            description: "最终审批"
            actor: "finance_manager"
            next: "complete"
          }
        ]
      }
```

## DSL语法设计

### 基本语法结构

```yaml
# 基本语法
basic_syntax:
  function_definition: |
    function <function_name> {
      version: "<version>"
      description: "<description>"
      
      inputs: [
        <input_definitions>
      ]
      
      outputs: [
        <output_definitions>
      ]
      
      business_logic: [
        <logic_definitions>
      ]
      
      rules: [
        <rule_definitions>
      ]
      
      workflows: [
        <workflow_definitions>
      ]
    }
    
  input_definition: |
    {
      name: "<input_name>"
      type: "<data_type>"
      description: "<description>"
      required: <boolean>
      validation: "<validation_rule>"
    }
    
  output_definition: |
    {
      name: "<output_name>"
      type: "<data_type>"
      description: "<description>"
      transformation: "<transformation_rule>"
    }
    
  logic_definition: |
    {
      name: "<logic_name>"
      type: "<logic_type>"
      expression: "<expression>"
      conditions: [
        <condition_definitions>
      ]
      actions: [
        <action_definitions>
      ]
    }
```

### 数据类型定义

```yaml
# 数据类型
data_types:
  primitive_types:
    - name: "string"
      description: "字符串类型"
      examples: ["text", "varchar", "char"]
      
    - name: "number"
      description: "数值类型"
      examples: ["integer", "decimal", "float"]
      
    - name: "boolean"
      description: "布尔类型"
      examples: ["true", "false"]
      
    - name: "date"
      description: "日期类型"
      examples: ["date", "datetime", "timestamp"]
      
    - name: "object"
      description: "对象类型"
      examples: ["json", "struct", "map"]
      
    - name: "array"
      description: "数组类型"
      examples: ["list", "collection", "set"]
      
  business_types:
    - name: "money"
      description: "货币类型"
      format: "decimal(10,2)"
      
    - name: "percentage"
      description: "百分比类型"
      format: "decimal(5,2)"
      
    - name: "email"
      description: "邮箱类型"
      format: "email_pattern"
      
    - name: "phone"
      description: "电话类型"
      format: "phone_pattern"
      
    - name: "address"
      description: "地址类型"
      format: "address_structure"
```

### 表达式语法

```yaml
# 表达式语法
expression_syntax:
  arithmetic_expressions:
    - name: "addition"
      syntax: "<operand1> + <operand2>"
      example: "price + tax"
      
    - name: "subtraction"
      syntax: "<operand1> - <operand2>"
      example: "total - discount"
      
    - name: "multiplication"
      syntax: "<operand1> * <operand2>"
      example: "quantity * unit_price"
      
    - name: "division"
      syntax: "<operand1> / <operand2>"
      example: "total / quantity"
      
  comparison_expressions:
    - name: "equality"
      syntax: "<operand1> == <operand2>"
      example: "status == 'active'"
      
    - name: "inequality"
      syntax: "<operand1> != <operand2>"
      example: "type != 'admin'"
      
    - name: "greater_than"
      syntax: "<operand1> > <operand2>"
      example: "amount > 1000"
      
    - name: "less_than"
      syntax: "<operand1> < <operand2>"
      example: "age < 18"
      
  logical_expressions:
    - name: "and"
      syntax: "<condition1> && <condition2>"
      example: "is_vip && amount > 1000"
      
    - name: "or"
      syntax: "<condition1> || <condition2>"
      example: "is_new_customer || amount > 5000"
      
    - name: "not"
      syntax: "!<condition>"
      example: "!is_blocked"
      
  function_calls:
    - name: "built_in_functions"
      functions:
        - "sum(collection)"
        - "avg(collection)"
        - "count(collection)"
        - "max(collection)"
        - "min(collection)"
        - "length(string)"
        - "substring(string, start, end)"
        - "format_date(date, format)"
        
    - name: "business_functions"
      functions:
        - "calculate_discount(amount, rate)"
        - "apply_tax(amount, rate)"
        - "validate_email(email)"
        - "format_currency(amount, currency)"
        - "calculate_age(birth_date)"
```

## 业务逻辑建模设计

### 基本业务逻辑

```yaml
# 基本业务逻辑
basic_business_logic:
  calculation_logic: |
    business_logic "price_calculation" {
      description: "价格计算逻辑"
      inputs: [
        {
          name: "base_price"
          type: "decimal"
          description: "基础价格"
        },
        {
          name: "quantity"
          type: "integer"
          description: "数量"
        },
        {
          name: "discount_rate"
          type: "percentage"
          description: "折扣率"
        }
      ]
      
      outputs: [
        {
          name: "total_price"
          type: "money"
          description: "总价格"
        },
        {
          name: "discount_amount"
          type: "money"
          description: "折扣金额"
        }
      ]
      
      logic: [
        {
          name: "calculate_subtotal"
          expression: "base_price * quantity"
          output: "subtotal"
        },
        {
          name: "calculate_discount"
          expression: "subtotal * discount_rate / 100"
          output: "discount_amount"
        },
        {
          name: "calculate_total"
          expression: "subtotal - discount_amount"
          output: "total_price"
        }
      ]
    }
    
  validation_logic: |
    business_logic "order_validation" {
      description: "订单验证逻辑"
      inputs: [
        {
          name: "order"
          type: "object"
          description: "订单对象"
        }
      ]
      
      outputs: [
        {
          name: "is_valid"
          type: "boolean"
          description: "是否有效"
        },
        {
          name: "errors"
          type: "array"
          description: "错误信息"
        }
      ]
      
      logic: [
        {
          name: "validate_customer"
          condition: "order.customer_id != null"
          action: "add_error('Customer ID is required')"
        },
        {
          name: "validate_items"
          condition: "order.items.length > 0"
          action: "add_error('Order must have at least one item')"
        },
        {
          name: "validate_amount"
          condition: "order.total_amount > 0"
          action: "add_error('Order amount must be greater than 0')"
        }
      ]
    }
```

### 复杂业务逻辑

```yaml
# 复杂业务逻辑
complex_business_logic:
  pricing_logic: |
    business_logic "dynamic_pricing" {
      description: "动态定价逻辑"
      inputs: [
        {
          name: "product"
          type: "object"
          description: "产品信息"
        },
        {
          name: "customer"
          type: "object"
          description: "客户信息"
        },
        {
          name: "market_data"
          type: "object"
          description: "市场数据"
        }
      ]
      
      outputs: [
        {
          name: "final_price"
          type: "money"
          description: "最终价格"
        },
        {
          name: "pricing_factors"
          type: "object"
          description: "定价因素"
        }
      ]
      
      logic: [
        {
          name: "base_price_calculation"
          expression: "product.base_price"
          output: "base_price"
        },
        {
          name: "demand_adjustment"
          condition: "market_data.demand_level == 'high'"
          expression: "base_price * 1.1"
          output: "demand_adjusted_price"
        },
        {
          name: "competition_adjustment"
          condition: "market_data.competitor_price < demand_adjusted_price"
          expression: "market_data.competitor_price * 0.95"
          output: "competition_adjusted_price"
        },
        {
          name: "customer_discount"
          condition: "customer.type == 'VIP'"
          expression: "competition_adjusted_price * 0.9"
          output: "customer_discounted_price"
        },
        {
          name: "seasonal_adjustment"
          expression: "customer_discounted_price * market_data.seasonal_factor"
          output: "final_price"
        }
      ]
    }
    
  approval_logic: |
    business_logic "approval_workflow" {
      description: "审批工作流逻辑"
      inputs: [
        {
          name: "request"
          type: "object"
          description: "申请请求"
        },
        {
          name: "approvers"
          type: "array"
          description: "审批人列表"
        }
      ]
      
      outputs: [
        {
          name: "approval_result"
          type: "object"
          description: "审批结果"
        }
      ]
      
      logic: [
        {
          name: "initial_review"
          condition: "request.amount <= 10000"
          action: "auto_approve"
          next: "complete"
        },
        {
          name: "manager_review"
          condition: "request.amount > 10000 && request.amount <= 50000"
          action: "assign_to_manager"
          next: "manager_decision"
        },
        {
          name: "executive_review"
          condition: "request.amount > 50000"
          action: "assign_to_executive"
          next: "executive_decision"
        }
      ]
    }
```

## 规则引擎建模设计

### 基本规则

```yaml
# 基本规则
basic_rules:
  discount_rule: |
    rule "vip_discount" {
      description: "VIP客户折扣规则"
      priority: 1
      
      conditions: [
        "customer.type == 'VIP'"
        "order.total_amount >= 1000"
      ]
      
      actions: [
        {
          name: "apply_discount"
          expression: "order.total_amount * 0.15"
          description: "应用15%折扣"
        },
        {
          name: "add_loyalty_points"
          expression: "order.total_amount * 0.1"
          description: "添加忠诚度积分"
        }
      ]
      
      metadata: {
        category: "pricing"
        version: "1.0"
        author: "business_analyst"
      }
    }
    
  validation_rule: |
    rule "order_validation" {
      description: "订单验证规则"
      priority: 10
      
      conditions: [
        "order.customer_id != null"
        "order.items.length > 0"
        "order.total_amount > 0"
      ]
      
      actions: [
        {
          name: "mark_valid"
          expression: "true"
          description: "标记订单为有效"
        }
      ]
      
      else_actions: [
        {
          name: "mark_invalid"
          expression: "false"
          description: "标记订单为无效"
        },
        {
          name: "add_validation_error"
          expression: "'Order validation failed'"
          description: "添加验证错误"
        }
      ]
    }
```

### 复杂规则

```yaml
# 复杂规则
complex_rules:
  tiered_discount_rule: |
    rule "tiered_discount" {
      description: "分层折扣规则"
      priority: 2
      
      decision_table: {
        conditions: [
          "customer.tier"
          "order.total_amount"
          "order.category"
        ]
        
        rules: [
          {
            conditions: ["gold", ">= 5000", "electronics"]
            actions: ["apply_discount(0.20)", "add_points(200)"]
          },
          {
            conditions: ["gold", ">= 5000", "*"]
            actions: ["apply_discount(0.15)", "add_points(150)"]
          },
          {
            conditions: ["silver", ">= 3000", "*"]
            actions: ["apply_discount(0.10)", "add_points(100)"]
          },
          {
            conditions: ["bronze", ">= 1000", "*"]
            actions: ["apply_discount(0.05)", "add_points(50)"]
          }
        ]
      }
    }
    
  risk_assessment_rule: |
    rule "risk_assessment" {
      description: "风险评估规则"
      priority: 5
      
      conditions: [
        "transaction.amount > 10000"
        "customer.risk_score > 0.7"
        "transaction.frequency > 5"
      ]
      
      actions: [
        {
          name: "flag_high_risk"
          expression: "true"
          description: "标记为高风险"
        },
        {
          name: "require_approval"
          expression: "true"
          description: "要求审批"
        },
        {
          name: "send_alert"
          expression: "'High risk transaction detected'"
          description: "发送告警"
        }
      ]
      
      else_actions: [
        {
          name: "flag_normal_risk"
          expression: "false"
          description: "标记为正常风险"
        }
      ]
    }
```

## 状态机建模设计

### 基本状态机

```yaml
# 基本状态机
basic_state_machines:
  order_state_machine: |
    state_machine "order_processing" {
      description: "订单处理状态机"
      initial_state: "pending"
      
      states: [
        {
          name: "pending"
          description: "待处理"
          entry_actions: ["validate_order", "check_inventory"]
          exit_actions: ["log_state_change"]
          
          transitions: [
            {
              event: "order_validated"
              target: "confirmed"
              condition: "inventory_available"
              actions: ["reserve_inventory"]
            },
            {
              event: "validation_failed"
              target: "cancelled"
              actions: ["send_rejection_email"]
            }
          ]
        },
        {
          name: "confirmed"
          description: "已确认"
          entry_actions: ["process_payment", "prepare_shipment"]
          
          transitions: [
            {
              event: "payment_successful"
              target: "shipped"
              actions: ["generate_shipping_label"]
            },
            {
              event: "payment_failed"
              target: "cancelled"
              actions: ["release_inventory", "send_payment_failure_email"]
            }
          ]
        },
        {
          name: "shipped"
          description: "已发货"
          entry_actions: ["send_shipping_notification"]
          
          transitions: [
            {
              event: "delivery_confirmed"
              target: "delivered"
              actions: ["send_delivery_confirmation"]
            },
            {
              event: "delivery_failed"
              target: "returned"
              actions: ["initiate_return_process"]
            }
          ]
        },
        {
          name: "delivered"
          description: "已送达"
          entry_actions: ["complete_order", "send_feedback_request"]
          final: true
        },
        {
          name: "cancelled"
          description: "已取消"
          entry_actions: ["refund_payment", "send_cancellation_email"]
          final: true
        }
      ]
    }
```

### 复杂状态机

```yaml
# 复杂状态机
complex_state_machines:
  loan_application_state_machine: |
    state_machine "loan_application" {
      description: "贷款申请状态机"
      initial_state: "draft"
      
      states: [
        {
          name: "draft"
          description: "草稿"
          entry_actions: ["initialize_application"]
          
          transitions: [
            {
              event: "submit"
              target: "submitted"
              condition: "application_complete"
              actions: ["validate_application"]
            }
          ]
        },
        {
          name: "submitted"
          description: "已提交"
          entry_actions: ["assign_case_officer", "start_credit_check"]
          
          transitions: [
            {
              event: "credit_check_complete"
              target: "under_review"
              condition: "credit_score_acceptable"
              actions: ["update_credit_score"]
            },
            {
              event: "credit_check_failed"
              target: "rejected"
              actions: ["send_rejection_letter"]
            }
          ]
        },
        {
          name: "under_review"
          description: "审核中"
          entry_actions: ["request_additional_documents"]
          
          transitions: [
            {
              event: "documents_received"
              target: "approved"
              condition: "all_requirements_met"
              actions: ["generate_loan_agreement"]
            },
            {
              event: "documents_incomplete"
              target: "pending_documents"
              actions: ["request_missing_documents"]
            },
            {
              event: "review_failed"
              target: "rejected"
              actions: ["send_rejection_letter"]
            }
          ]
        },
        {
          name: "pending_documents"
          description: "等待文档"
          entry_actions: ["send_document_reminder"]
          
          transitions: [
            {
              event: "documents_received"
              target: "under_review"
              actions: ["validate_documents"]
            },
            {
              event: "timeout"
              target: "expired"
              actions: ["send_expiration_notice"]
            }
          ]
        },
        {
          name: "approved"
          description: "已批准"
          entry_actions: ["disburse_loan", "send_approval_letter"]
          final: true
        },
        {
          name: "rejected"
          description: "已拒绝"
          entry_actions: ["send_rejection_letter", "archive_application"]
          final: true
        },
        {
          name: "expired"
          description: "已过期"
          entry_actions: ["archive_application"]
          final: true
        }
      ]
    }
```

## 工作流建模设计

### 基本工作流

```yaml
# 基本工作流
basic_workflows:
  approval_workflow: |
    workflow "expense_approval" {
      description: "费用审批工作流"
      
      steps: [
        {
          name: "submit"
          description: "提交申请"
          actor: "employee"
          form: "expense_form"
          next: "manager_review"
        },
        {
          name: "manager_review"
          description: "经理审核"
          actor: "department_manager"
          form: "approval_form"
          next: "finance_review"
          conditions: ["amount <= 5000"]
        },
        {
          name: "finance_review"
          description: "财务审核"
          actor: "finance_manager"
          form: "finance_approval_form"
          next: "complete"
        },
        {
          name: "complete"
          description: "完成"
          actor: "system"
          actions: ["process_payment", "send_notification"]
        }
      ]
      
      parallel_steps: [
        {
          name: "parallel_approval"
          steps: ["manager_review", "finance_review"]
          join_condition: "all_approved"
        }
      ]
    }
```

### 复杂工作流

```yaml
# 复杂工作流
complex_workflows:
  procurement_workflow: |
    workflow "procurement_process" {
      description: "采购流程工作流"
      
      steps: [
        {
          name: "requisition"
          description: "采购申请"
          actor: "requester"
          form: "requisition_form"
          next: "budget_check"
        },
        {
          name: "budget_check"
          description: "预算检查"
          actor: "budget_officer"
          form: "budget_approval_form"
          next: "vendor_selection"
          conditions: ["budget_available"]
        },
        {
          name: "vendor_selection"
          description: "供应商选择"
          actor: "procurement_officer"
          form: "vendor_selection_form"
          next: "quote_request"
        },
        {
          name: "quote_request"
          description: "报价请求"
          actor: "procurement_officer"
          form: "quote_request_form"
          next: "quote_evaluation"
        },
        {
          name: "quote_evaluation"
          description: "报价评估"
          actor: "procurement_committee"
          form: "quote_evaluation_form"
          next: "contract_negotiation"
        },
        {
          name: "contract_negotiation"
          description: "合同谈判"
          actor: "legal_officer"
          form: "contract_form"
          next: "final_approval"
        },
        {
          name: "final_approval"
          description: "最终审批"
          actor: "executive"
          form: "final_approval_form"
          next: "purchase_order"
        },
        {
          name: "purchase_order"
          description: "采购订单"
          actor: "procurement_officer"
          form: "purchase_order_form"
          next: "delivery"
        },
        {
          name: "delivery"
          description: "交付验收"
          actor: "requester"
          form: "delivery_acceptance_form"
          next: "payment"
        },
        {
          name: "payment"
          description: "付款"
          actor: "finance_officer"
          form: "payment_form"
          next: "complete"
        },
        {
          name: "complete"
          description: "完成"
          actor: "system"
          actions: ["archive_documents", "update_inventory"]
        }
      ]
      
      parallel_steps: [
        {
          name: "parallel_approval"
          steps: ["budget_check", "legal_review"]
          join_condition: "all_approved"
        }
      ]
      
      sub_workflows: [
        {
          name: "vendor_evaluation"
          workflow: "vendor_evaluation_process"
          trigger: "vendor_selection"
        }
      ]
    }
```

## 完整示例

### 电商业务功能

```yaml
# 电商业务功能示例
function "ecommerce_business" {
  version: "1.0.0"
  description: "电商业务功能模型"
  
  business_logic: [
    {
      name: "order_processing"
      description: "订单处理逻辑"
      inputs: [
        { name: "order", type: "object" },
        { name: "customer", type: "object" },
        { name: "inventory", type: "object" }
      ]
      outputs: [
        { name: "processing_result", type: "object" }
      ]
      logic: [
        {
          name: "validate_order"
          condition: "order.items.length > 0"
          action: "validate_order_items"
        },
        {
          name: "check_inventory"
          condition: "inventory.available"
          action: "reserve_inventory"
        },
        {
          name: "calculate_total"
          expression: "sum(order.items.price * order.items.quantity)"
          output: "total_amount"
        }
      ]
    }
  ]
  
  rules: [
    {
      name: "vip_discount"
      description: "VIP客户折扣"
      conditions: [
        "customer.type == 'VIP'"
        "order.total_amount >= 1000"
      ]
      actions: [
        "apply_discount(0.15)"
        "add_loyalty_points(100)"
      ]
    },
    {
      name: "free_shipping"
      description: "免运费规则"
      conditions: [
        "order.total_amount >= 200"
        "order.shipping_address.country == 'US'"
      ]
      actions: [
        "apply_free_shipping"
      ]
    }
  ]
  
  state_machines: [
    {
      name: "order_state"
      description: "订单状态机"
      initial_state: "pending"
      states: [
        {
          name: "pending"
          transitions: [
            { event: "confirmed", target: "confirmed" }
          ]
        },
        {
          name: "confirmed"
          transitions: [
            { event: "shipped", target: "shipped" }
          ]
        },
        {
          name: "shipped"
          transitions: [
            { event: "delivered", target: "delivered" }
          ]
        }
      ]
    }
  ]
  
  workflows: [
    {
      name: "order_fulfillment"
      description: "订单履行工作流"
      steps: [
        {
          name: "order_received"
          actor: "system"
          next: "inventory_check"
        },
        {
          name: "inventory_check"
          actor: "warehouse"
          next: "picking"
        },
        {
          name: "picking"
          actor: "warehouse"
          next: "packing"
        },
        {
          name: "packing"
          actor: "warehouse"
          next: "shipping"
        },
        {
          name: "shipping"
          actor: "logistics"
          next: "delivery"
        },
        {
          name: "delivery"
          actor: "courier"
          next: "complete"
        }
      ]
    }
  ]
}
```

## 工具链支持

### 开发工具

```yaml
# 开发工具
development_tools:
  dsl_editor:
    features:
      - "语法高亮"
      - "自动补全"
      - "语法检查"
      - "实时预览"
    tools:
      - "VS Code Extension"
      - "IntelliJ Plugin"
      - "Web-based Editor"
      
  validation_tool:
    features:
      - "语法验证"
      - "逻辑验证"
      - "规则验证"
      - "工作流验证"
    tools:
      - "DSL Validator"
      - "Logic Validator"
      - "Rule Engine Validator"
      
  testing_tool:
    features:
      - "单元测试"
      - "集成测试"
      - "规则测试"
      - "工作流测试"
    tools:
      - "DSL Test Runner"
      - "Rule Engine Tester"
      - "Workflow Simulator"
```

### 执行引擎

```yaml
# 执行引擎
execution_engine:
  core_components:
    - name: "Parser"
      description: "DSL解析器"
      features:
        - "语法解析"
        - "语义分析"
        - "错误报告"
        
    - name: "Rule Engine"
      description: "规则引擎"
      features:
        - "规则执行"
        - "条件评估"
        - "动作执行"
        
    - name: "State Machine Engine"
      description: "状态机引擎"
      features:
        - "状态管理"
        - "事件处理"
        - "状态转换"
        
    - name: "Workflow Engine"
      description: "工作流引擎"
      features:
        - "流程执行"
        - "任务分配"
        - "流程监控"
```

## 最佳实践

### 设计最佳实践

1. **业务导向**：以业务需求为中心设计功能
2. **模块化设计**：将复杂功能拆分为小模块
3. **可重用性**：设计可重用的业务逻辑组件
4. **可测试性**：确保功能易于测试

### 实施最佳实践

1. **渐进式开发**：逐步实现复杂功能
2. **充分测试**：对每个功能进行充分测试
3. **文档维护**：保持文档的及时更新
4. **版本管理**：对功能模型进行版本管理

### 维护最佳实践

1. **监控告警**：监控功能执行状态
2. **性能优化**：持续优化功能性能
3. **错误处理**：建立完善的错误处理机制
4. **变更管理**：建立功能变更的管理流程

## 相关概念

- [功能建模理论](theory.md)
- [业务逻辑建模](business-logic/theory.md)
- [规则引擎建模](rule-engine/theory.md)
- [状态机建模](state-machine/theory.md)
- [工作流建模](workflow/theory.md)

## 参考文献

1. Fowler, M. (2018). "Refactoring: Improving the Design of Existing Code"
2. Hohpe, G., & Woolf, B. (2003). "Enterprise Integration Patterns"
3. Evans, E. (2003). "Domain-Driven Design"
4. Gamma, E., et al. (1994). "Design Patterns"
5. Martin, R. C. (2008). "Clean Code"
