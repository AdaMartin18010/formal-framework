# 采购管理系统 DSL 草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述供应商管理、采购流程、合同管理、库存管理等采购核心业务要素，支持递归组合。
- 支持自动生成采购系统代码、业务规则、工作流、报表等。
- 支持与通用数据模型、功能模型、交互模型的深度映射。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 与通用模型映射关系

### 2.1 数据模型映射

```dsl
# 供应商实体映射到通用数据模型
entity Supplier {
  id: int primary key auto_increment
  supplier_code: string unique
  supplier_name: string not null
  contact_person: string
  email: string
  phone: string
  address: text
  tax_id: string
  registration_number: string
  supplier_type: enum["manufacturer", "distributor", "service_provider"]
  status: enum["active", "inactive", "suspended"]
  rating: decimal(3,2)
  created_at: datetime default now
  updated_at: datetime default now
}

# 采购申请实体映射到通用数据模型
entity PurchaseRequest {
  id: int primary key auto_increment
  request_id: string unique
  requester_id: int references Employee(id)
  department_id: int references Department(id)
  request_date: date not null
  priority: enum["low", "medium", "high", "urgent"]
  status: enum["draft", "submitted", "approved", "rejected", "completed"]
  total_amount: decimal(15,2)
  currency: string default "USD"
  description: text
  created_at: datetime default now
}

# 采购订单实体映射到通用数据模型
entity PurchaseOrder {
  id: int primary key auto_increment
  po_number: string unique
  supplier_id: int references Supplier(id)
  request_id: int references PurchaseRequest(id)
  order_date: date not null
  expected_delivery: date
  status: enum["draft", "sent", "confirmed", "shipped", "delivered", "cancelled"]
  total_amount: decimal(15,2)
  currency: string default "USD"
  payment_terms: string
  shipping_address: text
  created_at: datetime default now
}
```

### 2.2 功能模型映射

```dsl
# 采购申请审批业务逻辑映射到通用功能模型
business_logic PurchaseApproval {
  input: [purchase_request, budget_info, approval_rules]
  validation: [
    { field: "request_amount", rule: "within_budget_limit" },
    { field: "supplier", rule: "approved_supplier" },
    { field: "justification", rule: "valid_business_case" },
    { field: "priority", rule: "appropriate_priority_level" }
  ]
  process: [
    { step: "validate_request", condition: "all_valid" },
    { step: "check_budget", condition: "budget_available" },
    { step: "manager_approval", condition: "amount < 10000" },
    { step: "director_approval", condition: "amount >= 10000" },
    { step: "create_purchase_order", output: "po_number" },
    { step: "notify_supplier", input: "po_number" }
  ]
  output: "approval_result"
  error_handling: {
    budget_exceeded: "return_error_message",
    supplier_not_approved: "return_error_message",
    approval_rejected: "return_rejection_reason"
  }
}

# 供应商评估规则引擎映射到通用功能模型
rule_engine SupplierEvaluation {
  rules: [
    {
      name: "quality_rule",
      condition: "quality_score >= 4.0",
      action: "approve_supplier",
      priority: 1
    },
    {
      name: "delivery_rule",
      condition: "on_time_delivery >= 0.95",
      action: "approve_supplier",
      priority: 2
    },
    {
      name: "price_rule",
      condition: "price_competitiveness >= 0.8",
      action: "approve_supplier",
      priority: 3
    }
  ]
  aggregation: "overall_supplier_score"
  threshold: 0.7
  output: "supplier_approval_status"
}
```

### 2.3 交互模型映射

```dsl
# 采购API接口映射到通用交互模型
api ProcurementAPI {
  endpoints: [
    {
      path: "/purchase-requests",
      method: "GET",
      response: "PurchaseRequestList",
      security: "oauth2"
    },
    {
      path: "/purchase-requests",
      method: "POST",
      request: "PurchaseRequestCreate",
      response: "PurchaseRequestCreated",
      security: "oauth2"
    },
    {
      path: "/purchase-orders",
      method: "GET",
      response: "PurchaseOrderList",
      security: "oauth2"
    },
    {
      path: "/suppliers",
      method: "GET",
      response: "SupplierList",
      security: "oauth2"
    },
    {
      path: "/suppliers/{supplier_id}/evaluate",
      method: "POST",
      request: "SupplierEvaluationRequest",
      response: "SupplierEvaluationResult",
      security: "oauth2"
    }
  ]
  security: {
    authentication: "oauth2",
    authorization: "role_based",
    rate_limiting: "per_user_per_minute"
  }
}
```

## 3. 核心业务建模

### 3.1 供应商管理

```dsl
# 供应商分类
entity SupplierCategory {
  id: int primary key auto_increment
  category_code: string unique
  category_name: string not null
  description: text
  parent_category_id: int references SupplierCategory(id)
  status: enum["active", "inactive"]
}

# 供应商评估
entity SupplierEvaluation {
  id: int primary key auto_increment
  supplier_id: int references Supplier(id)
  evaluator_id: int references Employee(id)
  evaluation_date: date not null
  evaluation_period: {
    start_date: date,
    end_date: date
  }
  evaluation_criteria: {
    quality_score: decimal(3,2),
    delivery_score: decimal(3,2),
    price_score: decimal(3,2),
    service_score: decimal(3,2)
  }
  overall_score: decimal(3,2)
  comments: text
  recommendations: [text]
  status: enum["draft", "submitted", "approved"]
}

# 供应商状态机
state_machine SupplierStatus {
  states: [
    { name: "prospect", initial: true },
    { name: "evaluating" },
    { name: "approved" },
    { name: "active" },
    { name: "suspended" },
    { name: "blacklisted", final: true }
  ]
  transitions: [
    { from: "prospect", to: "evaluating", event: "start_evaluation" },
    { from: "evaluating", to: "approved", event: "approve_supplier" },
    { from: "approved", to: "active", event: "activate_supplier" },
    { from: "active", to: "suspended", event: "suspend_supplier" },
    { from: "suspended", to: "active", event: "reactivate_supplier" },
    { from: "active", to: "blacklisted", event: "blacklist_supplier" }
  ]
}
```

### 3.2 采购流程管理

```dsl
# 采购申请工作流
workflow PurchaseRequestWorkflow {
  steps: [
    {
      name: "create_request",
      type: "user_input",
      required: ["item_details", "quantity", "justification", "budget"]
    },
    {
      name: "department_approval",
      type: "manager_approval",
      required: ["approval", "comments"],
      depends_on: ["create_request"]
    },
    {
      name: "budget_check",
      type: "automated",
      service: "budget_system",
      depends_on: ["department_approval"]
    },
    {
      name: "procurement_review",
      type: "procurement_input",
      required: ["supplier_selection", "price_analysis"],
      depends_on: ["budget_check"]
    },
    {
      name: "final_approval",
      type: "approval",
      required: ["approval", "comments"],
      depends_on: ["procurement_review"]
    }
  ]
  timeouts: {
    department_approval: "3d",
    procurement_review: "2d",
    final_approval: "1d"
  }
}

# 采购订单状态机
state_machine PurchaseOrderStatus {
  states: [
    { name: "draft", initial: true },
    { name: "sent" },
    { name: "confirmed" },
    { name: "in_production" },
    { name: "shipped" },
    { name: "delivered" },
    { name: "completed", final: true },
    { name: "cancelled", final: true }
  ]
  transitions: [
    { from: "draft", to: "sent", event: "send_to_supplier" },
    { from: "sent", to: "confirmed", event: "supplier_confirm" },
    { from: "confirmed", to: "in_production", event: "start_production" },
    { from: "in_production", to: "shipped", event: "ship_order" },
    { from: "shipped", to: "delivered", event: "confirm_delivery" },
    { from: "delivered", to: "completed", event: "complete_order" },
    { from: "sent", to: "cancelled", event: "cancel_order" }
  ]
}
```

### 3.3 合同管理

```dsl
# 合同实体
entity Contract {
  id: int primary key auto_increment
  contract_number: string unique
  supplier_id: int references Supplier(id)
  contract_type: enum["purchase", "service", "framework", "master"]
  start_date: date not null
  end_date: date not null
  total_value: decimal(15,2)
  currency: string default "USD"
  payment_terms: string
  delivery_terms: string
  status: enum["draft", "active", "expired", "terminated"]
  created_at: datetime default now
}

# 合同条款
entity ContractTerm {
  id: int primary key auto_increment
  contract_id: int references Contract(id)
  term_type: enum["payment", "delivery", "quality", "penalty", "warranty"]
  description: text
  conditions: text
  penalties: text
  created_at: datetime default now
}

# 合同审批规则
rule_engine ContractApproval {
  rules: [
    {
      name: "value_threshold_rule",
      condition: "contract_value > 100000",
      action: "require_legal_review",
      priority: 1
    },
    {
      name: "supplier_rating_rule",
      condition: "supplier_rating < 3.0",
      action: "require_additional_review",
      priority: 2
    },
    {
      name: "contract_duration_rule",
      condition: "duration > 3_years",
      action: "require_board_approval",
      priority: 3
    }
  ]
  aggregation: "approval_requirements"
  output: "approval_workflow"
}
```

### 3.4 库存管理

```dsl
# 库存实体
entity Inventory {
  id: int primary key auto_increment
  item_id: int references Item(id)
  warehouse_id: int references Warehouse(id)
  quantity: int not null
  reserved_quantity: int default 0
  available_quantity: int
  unit_cost: decimal(10,2)
  last_updated: datetime default now
}

# 库存预警规则
rule_engine InventoryAlert {
  rules: [
    {
      name: "low_stock_alert",
      condition: "available_quantity <= reorder_point",
      action: "trigger_reorder",
      priority: 1
    },
    {
      name: "overstock_alert",
      condition: "quantity > max_stock_level",
      action: "trigger_slowdown",
      priority: 2
    },
    {
      name: "expiry_alert",
      condition: "expiry_date <= 30_days",
      action: "trigger_consumption",
      priority: 3
    }
  ]
  aggregation: "inventory_actions"
  output: "inventory_alerts"
}
```

## 4. AI自动化推理能力

### 4.1 智能供应商选择

```dsl
# AI供应商推荐
ai_supplier_recommendation SupplierRecommendation {
  features: [
    "historical_performance",
    "price_competitiveness",
    "quality_rating",
    "delivery_reliability",
    "financial_stability"
  ]
  model_type: "recommendation_system"
  training_data: "historical_purchase_data"
  output: "recommended_suppliers"
}

# 智能价格预测
ai_price_prediction PricePrediction {
  features: [
    "market_trends",
    "supplier_costs",
    "demand_forecast",
    "seasonal_factors"
  ]
  prediction_horizon: "6_months"
  confidence_interval: 0.9
  output: "price_forecast"
}
```

### 4.2 智能采购优化

```dsl
# 采购策略优化
ai_procurement_optimization ProcurementOptimization {
  optimization_algorithm: "genetic_algorithm"
  objectives: [
    "minimize_cost",
    "maximize_quality",
    "minimize_delivery_time",
    "maximize_supplier_reliability"
  ]
  constraints: [
    "budget_limit",
    "quality_requirements",
    "delivery_deadlines"
  ]
  output: "optimal_procurement_strategy"
}

# 需求预测
ai_demand_forecasting DemandForecasting {
  features: [
    "historical_consumption",
    "seasonal_patterns",
    "business_growth",
    "market_trends"
  ]
  forecasting_method: "time_series_analysis"
  forecast_period: "12_months"
  output: "demand_forecast"
}
```

### 4.3 智能风险分析

```dsl
# 供应商风险评估
ai_supplier_risk SupplierRiskAssessment {
  risk_factors: [
    "financial_health",
    "operational_capacity",
    "geopolitical_risk",
    "regulatory_compliance"
  ]
  risk_model: "ensemble_classifier"
  risk_threshold: 0.7
  output: "risk_score"
}

# 供应链中断预测
ai_supply_disruption SupplyDisruptionPrediction {
  features: [
    "supplier_performance",
    "geopolitical_events",
    "natural_disasters",
    "regulatory_changes"
  ]
  prediction_horizon: "3_months"
  output: "disruption_probability"
}
```

## 5. 安全与合规

```dsl
# 采购合规检查
procurement_compliance ProcurementCompliance {
  anti_corruption: {
    due_diligence: true,
    conflict_of_interest: true,
    gift_policy: true
  }
  regulatory_compliance: {
    import_export: true,
    environmental: true,
    labor_standards: true
  }
  data_protection: {
    supplier_data: true,
    contract_terms: true,
    audit_trail: true
  }
}

# 审计跟踪
audit_trail ProcurementAudit {
  tracked_actions: [
    "purchase_request_creation",
    "approval_decisions",
    "supplier_selection",
    "contract_modifications"
  ]
  retention_period: "7_years"
  access_control: "role_based"
}
```

## 6. 监控与报告

```dsl
# 采购指标监控
procurement_metrics ProcurementMetrics {
  cost_metrics: [
    "total_spend",
    "cost_savings",
    "price_variance",
    "budget_utilization"
  ]
  performance_metrics: [
    "supplier_performance",
    "delivery_on_time",
    "quality_acceptance",
    "cycle_time"
  ]
  risk_metrics: [
    "supplier_concentration",
    "single_source_risk",
    "geographic_risk"
  ]
}

# 自动化报告
automated_reports ProcurementReports {
  reports: [
    {
      name: "monthly_spend_analysis",
      schedule: "monthly",
      recipients: ["procurement_manager", "finance_director"]
    },
    {
      name: "supplier_performance_review",
      schedule: "quarterly",
      recipients: ["supplier_manager", "quality_manager"]
    },
    {
      name: "annual_procurement_strategy",
      schedule: "annually",
      recipients: ["procurement_director", "ceo"]
    }
  ]
}
```

---

本节递归扩展了采购管理系统DSL，涵盖与通用模型的深度映射、AI自动化推理、核心业务建模、安全合规等内容，为采购管理系统的工程实现提供了全链路建模支撑。
