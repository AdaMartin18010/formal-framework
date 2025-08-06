# 资产管理系统 DSL 草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述资产登记、维护管理、折旧计算、资产处置等资产管理核心业务要素，支持递归组合。
- 支持自动生成资产系统代码、业务规则、报表、工作流等。
- 支持与通用数据模型、功能模型、交互模型的深度映射。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 与通用模型映射关系

### 2.1 数据模型映射

```dsl
# 资产实体映射到通用数据模型
entity Asset {
  id: int primary key auto_increment
  asset_id: string unique
  asset_name: string not null
  asset_type: enum["equipment", "building", "vehicle", "software", "intangible"]
  category_id: int references AssetCategory(id)
  location_id: int references Location(id)
  department_id: int references Department(id)
  custodian_id: int references Employee(id)
  purchase_date: date not null
  purchase_cost: decimal(15,2) not null
  current_value: decimal(15,2)
  depreciation_method: enum["straight_line", "declining_balance", "units_of_production"]
  useful_life: int  # years
  salvage_value: decimal(10,2)
  status: enum["active", "maintenance", "disposed", "lost"]
  created_at: datetime default now
  updated_at: datetime default now
}

# 资产类别实体映射到通用数据模型
entity AssetCategory {
  id: int primary key auto_increment
  category_code: string unique
  category_name: string not null
  parent_category_id: int references AssetCategory(id)
  depreciation_rate: decimal(5,4)
  useful_life: int
  description: text
  status: enum["active", "inactive"]
  created_at: datetime default now
}

# 位置实体映射到通用数据模型
entity Location {
  id: int primary key auto_increment
  location_code: string unique
  location_name: string not null
  location_type: enum["building", "floor", "room", "warehouse"]
  address: text
  parent_location_id: int references Location(id)
  status: enum["active", "inactive"]
  created_at: datetime default now
}
```

### 2.2 功能模型映射

```dsl
# 资产登记业务逻辑映射到通用功能模型
business_logic AssetRegistration {
  input: [asset_data, purchase_info, location_info]
  validation: [
    { field: "asset_id", rule: "unique_asset_id" },
    { field: "purchase_cost", rule: "positive_amount" },
    { field: "useful_life", rule: "positive_years" },
    { field: "location", rule: "valid_location" }
  ]
  process: [
    { step: "validate_asset_data", condition: "all_valid" },
    { step: "create_asset_record", output: "asset_id" },
    { step: "assign_location", input: "asset_id" },
    { step: "assign_custodian", input: "asset_id" },
    { step: "calculate_depreciation", input: "asset_id" },
    { step: "generate_asset_tag", input: "asset_id" }
  ]
  output: "registration_result"
  error_handling: {
    duplicate_asset: "return_error_message",
    invalid_location: "return_error_message",
    system_error: "rollback_and_retry"
  }
}

# 折旧计算规则引擎映射到通用功能模型
rule_engine DepreciationCalculation {
  rules: [
    {
      name: "straight_line_rule",
      condition: "depreciation_method = 'straight_line'",
      action: "calculate_straight_line_depreciation",
      priority: 1
    },
    {
      name: "declining_balance_rule",
      condition: "depreciation_method = 'declining_balance'",
      action: "calculate_declining_balance_depreciation",
      priority: 2
    },
    {
      name: "units_of_production_rule",
      condition: "depreciation_method = 'units_of_production'",
      action: "calculate_units_of_production_depreciation",
      priority: 3
    }
  ]
  aggregation: "total_depreciation"
  output: "depreciation_schedule"
}
```

### 2.3 交互模型映射

```dsl
# 资产管理API接口映射到通用交互模型
api AssetManagementAPI {
  endpoints: [
    {
      path: "/assets",
      method: "GET",
      response: "AssetList",
      security: "oauth2"
    },
    {
      path: "/assets/{asset_id}",
      method: "GET",
      response: "AssetDetails",
      security: "oauth2"
    },
    {
      path: "/assets",
      method: "POST",
      request: "AssetCreateRequest",
      response: "AssetCreated",
      security: "oauth2"
    },
    {
      path: "/assets/{asset_id}/maintenance",
      method: "POST",
      request: "MaintenanceRequest",
      response: "MaintenanceScheduled",
      security: "oauth2"
    },
    {
      path: "/assets/{asset_id}/dispose",
      method: "POST",
      request: "DisposalRequest",
      response: "DisposalProcessed",
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

### 3.1 资产生命周期管理

```dsl
# 资产状态机
state_machine AssetLifecycle {
  states: [
    { name: "procurement", initial: true },
    { name: "received" },
    { name: "commissioned" },
    { name: "operational" },
    { name: "maintenance" },
    { name: "decommissioned" },
    { name: "disposed", final: true }
  ]
  transitions: [
    { from: "procurement", to: "received", event: "asset_received" },
    { from: "received", to: "commissioned", event: "asset_commissioned" },
    { from: "commissioned", to: "operational", event: "asset_operational" },
    { from: "operational", to: "maintenance", event: "maintenance_required" },
    { from: "maintenance", to: "operational", event: "maintenance_completed" },
    { from: "operational", to: "decommissioned", event: "asset_decommissioned" },
    { from: "decommissioned", to: "disposed", event: "asset_disposed" }
  ]
}

# 资产转移
entity AssetTransfer {
  id: int primary key auto_increment
  asset_id: int references Asset(id)
  from_location_id: int references Location(id)
  to_location_id: int references Location(id)
  from_custodian_id: int references Employee(id)
  to_custodian_id: int references Employee(id)
  transfer_date: date not null
  transfer_reason: text
  approval_status: enum["pending", "approved", "rejected"]
  approved_by: int references Employee(id)
  created_at: datetime default now
}
```

### 3.2 维护管理

```dsl
# 维护计划
entity MaintenancePlan {
  id: int primary key auto_increment
  asset_id: int references Asset(id)
  maintenance_type: enum["preventive", "corrective", "predictive"]
  frequency: enum["daily", "weekly", "monthly", "quarterly", "yearly"]
  description: text
  estimated_cost: decimal(10,2)
  estimated_duration: int  # hours
  vendor_id: int references Vendor(id)
  status: enum["active", "inactive"]
  created_at: datetime default now
}

# 维护工单
entity MaintenanceWorkOrder {
  id: int primary key auto_increment
  asset_id: int references Asset(id)
  maintenance_plan_id: int references MaintenancePlan(id)
  work_order_number: string unique
  maintenance_type: enum["scheduled", "emergency", "breakdown"]
  priority: enum["low", "medium", "high", "critical"]
  description: text
  scheduled_date: date
  actual_start_date: datetime
  actual_end_date: datetime
  cost: decimal(10,2)
  technician_id: int references Employee(id)
  status: enum["scheduled", "in_progress", "completed", "cancelled"]
  created_at: datetime default now
}

# 维护规则引擎
rule_engine MaintenanceRules {
  rules: [
    {
      name: "preventive_maintenance_rule",
      condition: "operating_hours >= maintenance_interval",
      action: "schedule_preventive_maintenance",
      priority: 1
    },
    {
      name: "emergency_maintenance_rule",
      condition: "asset_condition = 'critical'",
      action: "schedule_emergency_maintenance",
      priority: 2
    },
    {
      name: "predictive_maintenance_rule",
      condition: "sensor_data_anomaly_detected",
      action: "schedule_predictive_maintenance",
      priority: 3
    }
  ]
  aggregation: "maintenance_schedule"
  output: "maintenance_work_orders"
}
```

### 3.3 折旧管理

```dsl
# 折旧记录
entity DepreciationRecord {
  id: int primary key auto_increment
  asset_id: int references Asset(id)
  depreciation_date: date not null
  depreciation_amount: decimal(10,2) not null
  accumulated_depreciation: decimal(10,2)
  book_value: decimal(10,2)
  depreciation_method: enum["straight_line", "declining_balance", "units_of_production"]
  created_at: datetime default now
}

# 折旧计算规则
rule_engine DepreciationRules {
  rules: [
    {
      name: "straight_line_calculation",
      condition: "method = 'straight_line'",
      action: "depreciation = (cost - salvage) / useful_life",
      priority: 1
    },
    {
      name: "declining_balance_calculation",
      condition: "method = 'declining_balance'",
      action: "depreciation = book_value * rate",
      priority: 2
    },
    {
      name: "units_of_production_calculation",
      condition: "method = 'units_of_production'",
      action: "depreciation = (cost - salvage) * (units_used / total_units)",
      priority: 3
    }
  ]
  aggregation: "total_depreciation"
  output: "depreciation_schedule"
}
```

### 3.4 资产处置

```dsl
# 资产处置
entity AssetDisposal {
  id: int primary key auto_increment
  asset_id: int references Asset(id)
  disposal_type: enum["sale", "scrap", "donation", "trade_in"]
  disposal_date: date not null
  disposal_value: decimal(10,2)
  disposal_reason: text
  buyer_recipient: string
  approval_status: enum["pending", "approved", "rejected"]
  approved_by: int references Employee(id)
  created_at: datetime default now
}

# 处置审批规则
rule_engine DisposalApproval {
  rules: [
    {
      name: "value_threshold_rule",
      condition: "asset_value > 10000",
      action: "require_management_approval",
      priority: 1
    },
    {
      name: "age_threshold_rule",
      condition: "asset_age < 2_years",
      action: "require_additional_justification",
      priority: 2
    },
    {
      name: "condition_rule",
      condition: "asset_condition = 'good'",
      action: "consider_repair_instead",
      priority: 3
    }
  ]
  aggregation: "approval_requirements"
  output: "disposal_approval_workflow"
}
```

## 4. AI自动化推理能力

### 4.1 智能维护预测

```dsl
# 预测性维护
ai_predictive_maintenance PredictiveMaintenance {
  features: [
    "operating_hours",
    "temperature_readings",
    "vibration_data",
    "performance_metrics",
    "historical_failures"
  ]
  model_type: "time_series_forecasting"
  prediction_horizon: "30_days"
  confidence_interval: 0.9
  output: "maintenance_prediction"
}

# 故障预测
ai_failure_prediction FailurePrediction {
  features: [
    "equipment_age",
    "maintenance_history",
    "operating_conditions",
    "environmental_factors"
  ]
  model_type: "survival_analysis"
  risk_threshold: 0.7
  output: "failure_probability"
}
```

### 4.2 智能资产优化

```dsl
# 资产利用率优化
ai_asset_optimization AssetOptimization {
  optimization_algorithm: "genetic_algorithm"
  objectives: [
    "maximize_utilization",
    "minimize_maintenance_cost",
    "maximize_lifespan",
    "minimize_downtime"
  ]
  constraints: [
    "budget_limit",
    "capacity_constraints",
    "safety_requirements"
  ]
  output: "optimal_asset_allocation"
}

# 资产价值预测
ai_asset_value_prediction AssetValuePrediction {
  features: [
    "market_conditions",
    "technological_obsolescence",
    "maintenance_condition",
    "demand_forecast"
  ]
  prediction_horizon: "5_years"
  output: "future_asset_value"
}
```

### 4.3 智能库存优化

```dsl
# 备件需求预测
ai_spare_parts_forecasting SparePartsForecasting {
  features: [
    "equipment_failure_history",
    "maintenance_schedule",
    "parts_consumption",
    "lead_time_data"
  ]
  forecasting_method: "demand_forecasting"
  forecast_period: "12_months"
  output: "spare_parts_demand"
}

# 库存优化
ai_inventory_optimization InventoryOptimization {
  optimization_algorithm: "multi_objective_optimization"
  objectives: [
    "minimize_stockout_risk",
    "minimize_holding_cost",
    "maximize_service_level"
  ]
  constraints: [
    "budget_constraints",
    "storage_capacity",
    "supplier_lead_times"
  ]
  output: "optimal_inventory_levels"
}
```

## 5. 安全与合规

```dsl
# 资产安全
asset_security AssetSecurity {
  physical_security: {
    access_control: true,
    surveillance: true,
    asset_tagging: true
  }
  data_security: {
    encryption: "AES-256",
    access_logging: true,
    backup_protection: true
  }
  insurance: {
    coverage: "comprehensive",
    valuation: "replacement_cost",
    claims_tracking: true
  }
}

# 合规检查
asset_compliance AssetCompliance {
  regulatory_compliance: {
    safety_standards: true,
    environmental_regulations: true,
    industry_standards: true
  }
  financial_compliance: {
    accounting_standards: true,
    tax_regulations: true,
    audit_requirements: true
  }
  data_protection: {
    gdpr_compliance: true,
    data_retention: "7_years",
    privacy_protection: true
  }
}
```

## 6. 监控与报告

```dsl
# 资产指标监控
asset_metrics AssetMetrics {
  financial_metrics: [
    "total_asset_value",
    "depreciation_expense",
    "maintenance_cost",
    "return_on_assets"
  ]
  operational_metrics: [
    "asset_utilization",
    "uptime_percentage",
    "maintenance_efficiency",
    "mean_time_between_failures"
  ]
  compliance_metrics: [
    "safety_incidents",
    "regulatory_violations",
    "insurance_claims",
    "audit_findings"
  ]
}

# 自动化报告
automated_reports AssetReports {
  reports: [
    {
      name: "monthly_asset_summary",
      schedule: "monthly",
      recipients: ["asset_manager", "finance_director"]
    },
    {
      name: "quarterly_maintenance_review",
      schedule: "quarterly",
      recipients: ["maintenance_manager", "operations_director"]
    },
    {
      name: "annual_asset_valuation",
      schedule: "annually",
      recipients: ["asset_director", "ceo", "audit_committee"]
    }
  ]
}
```

---

本节递归扩展了资产管理系统DSL，涵盖与通用模型的深度映射、AI自动化推理、核心业务建模、安全合规等内容，为资产管理系统的工程实现提供了全链路建模支撑。
