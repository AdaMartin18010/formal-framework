# 企业管理模型 DSL 草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述企业管理中的HR、CRM、采购、资产、项目等核心业务要素，支持递归组合。
- 支持自动生成企业管理代码、业务流程、报表分析、决策支持等。
- 支持与通用数据模型、功能模型、交互模型的深度映射。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 与通用模型映射关系

### 2.1 数据模型映射

```dsl
# 员工实体映射到通用数据模型
entity Employee {
  id: int primary key auto_increment
  employee_id: string unique
  first_name: string not null
  last_name: string not null
  email: string unique
  phone: string
  department_id: int references Department(id)
  position_id: int references Position(id)
  hire_date: date not null
  salary: decimal(10,2)
  status: enum["active", "inactive", "terminated", "on_leave"]
  manager_id: int references Employee(id)
  created_at: datetime default now
  updated_at: datetime default now
}

# 客户实体映射到通用数据模型
entity Customer {
  id: int primary key auto_increment
  customer_id: string unique
  company_name: string
  contact_person: string
  email: string
  phone: string
  address: text
  industry: string
  customer_type: enum["prospect", "lead", "customer", "partner"]
  status: enum["active", "inactive", "lost"]
  assigned_to: int references Employee(id)
  created_at: datetime default now
}

# 供应商实体映射到通用数据模型
entity Supplier {
  id: int primary key auto_increment
  supplier_id: string unique
  company_name: string not null
  contact_person: string
  email: string
  phone: string
  address: text
  category: enum["goods", "services", "both"]
  status: enum["active", "inactive", "blacklisted"]
  rating: float
  created_at: datetime default now
}

# 资产实体映射到通用数据模型
entity Asset {
  id: int primary key auto_increment
  asset_id: string unique
  asset_name: string not null
  asset_type: enum["hardware", "software", "furniture", "vehicle", "building"]
  category: string
  purchase_date: date
  purchase_cost: decimal(10,2)
  current_value: decimal(10,2)
  location: string
  assigned_to: int references Employee(id)
  status: enum["in_use", "available", "maintenance", "retired"]
  created_at: datetime default now
}

# 项目实体映射到通用数据模型
entity Project {
  id: int primary key auto_increment
  project_id: string unique
  project_name: string not null
  description: text
  start_date: date
  end_date: date
  budget: decimal(12,2)
  status: enum["planning", "active", "on_hold", "completed", "cancelled"]
  priority: enum["low", "medium", "high", "critical"]
  manager_id: int references Employee(id)
  client_id: int references Customer(id)
  created_at: datetime default now
}
```

### 2.2 功能模型映射

```dsl
# HR招聘业务逻辑映射到通用功能模型
business_logic RecruitmentProcess {
  input: [job_requirement, candidate_info]
  validation: [
    { field: "job_requirement", rule: "valid_position" },
    { field: "candidate_info", rule: "complete_profile" },
    { field: "candidate_info", rule: "qualification_match" }
  ]
  process: [
    { step: "screening", condition: "profile_valid" },
    { step: "interview_scheduling", service: "calendar_service" },
    { step: "technical_assessment", condition: "interview_passed" },
    { step: "background_check", condition: "assessment_passed" },
    { step: "offer_generation", output: "offer_id" },
    { step: "onboarding_setup", input: "offer_accepted" }
  ]
  output: "recruitment_result"
  error_handling: {
    qualification_mismatch: "return_rejection",
    background_check_failed: "return_rejection",
    offer_declined: "return_decline"
  }
}

# CRM销售流程规则引擎映射到通用功能模型
rule_engine SalesAutomation {
  rules: [
    {
      name: "lead_scoring_rule",
      condition: "company_size > 100 AND industry = 'technology'",
      action: "assign_high_priority",
      priority: 1
    },
    {
      name: "follow_up_rule",
      condition: "last_contact > 7_days",
      action: "schedule_follow_up",
      priority: 2
    },
    {
      name: "opportunity_creation_rule",
      condition: "budget_approved AND decision_maker_identified",
      action: "create_opportunity",
      priority: 3
    }
  ]
  aggregation: "lead_score_calculation"
  threshold: 0.7
  output: "sales_decision"
}
```

### 2.3 交互模型映射

```dsl
# HR API接口映射到通用交互模型
api HRAPI {
  endpoints: [
    {
      path: "/employees/{employee_id}",
      method: "GET",
      response: "EmployeeInfo",
      security: "oauth2"
    },
    {
      path: "/employees",
      method: "POST",
      request: "EmployeeCreate",
      response: "EmployeeCreated",
      security: "oauth2"
    },
    {
      path: "/employees/{employee_id}/attendance",
      method: "GET",
      response: "AttendanceRecord",
      security: "oauth2"
    }
  ]
  security: {
    authentication: "oauth2",
    authorization: "role_based",
    rate_limiting: "per_user_per_minute"
  }
}

# CRM API接口映射到通用交互模型
api CRMAPI {
  endpoints: [
    {
      path: "/customers/{customer_id}",
      method: "GET",
      response: "CustomerInfo",
      security: "oauth2"
    },
    {
      path: "/opportunities",
      method: "POST",
      request: "OpportunityCreate",
      response: "OpportunityCreated",
      security: "oauth2"
    },
    {
      path: "/leads/{lead_id}/convert",
      method: "POST",
      request: "LeadConversion",
      response: "ConversionResult",
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

## 3. HR管理核心建模

### 3.1 组织架构

```dsl
# 部门实体
entity Department {
  id: int primary key auto_increment
  department_id: string unique
  department_name: string not null
  description: text
  parent_department_id: int references Department(id)
  manager_id: int references Employee(id)
  budget: decimal(12,2)
  status: enum["active", "inactive"]
  created_at: datetime default now
}

# 职位实体
entity Position {
  id: int primary key auto_increment
  position_id: string unique
  position_title: string not null
  department_id: int references Department(id)
  job_description: text
  requirements: text
  salary_range_min: decimal(10,2)
  salary_range_max: decimal(10,2)
  status: enum["open", "filled", "closed"]
  created_at: datetime default now
}

# 薪资结构
entity SalaryStructure {
  id: int primary key auto_increment
  position_id: int references Position(id)
  base_salary: decimal(10,2)
  bonus_percentage: decimal(5,2)
  benefits: json
  effective_date: date
  created_at: datetime default now
}
```

### 3.2 考勤管理

```dsl
# 考勤记录
entity AttendanceRecord {
  id: int primary key auto_increment
  employee_id: int references Employee(id)
  date: date not null
  check_in_time: datetime
  check_out_time: datetime
  work_hours: decimal(4,2)
  overtime_hours: decimal(4,2)
  leave_type: enum["none", "sick", "vacation", "personal", "maternity"]
  status: enum["present", "absent", "late", "early_leave"]
  created_at: datetime default now
}

# 请假申请
entity LeaveRequest {
  id: int primary key auto_increment
  employee_id: int references Employee(id)
  leave_type: enum["sick", "vacation", "personal", "maternity", "paternity"]
  start_date: date not null
  end_date: date not null
  days_requested: int
  reason: text
  status: enum["pending", "approved", "rejected", "cancelled"]
  approved_by: int references Employee(id)
  created_at: datetime default now
}
```

## 4. CRM管理核心建模

### 4.1 销售流程

```dsl
# 销售线索
entity Lead {
  id: int primary key auto_increment
  lead_id: string unique
  company_name: string
  contact_person: string
  email: string
  phone: string
  source: enum["website", "referral", "cold_call", "event", "social_media"]
  status: enum["new", "contacted", "qualified", "unqualified", "converted"]
  assigned_to: int references Employee(id)
  score: int
  created_at: datetime default now
}

# 销售机会
entity Opportunity {
  id: int primary key auto_increment
  opportunity_id: string unique
  lead_id: int references Lead(id)
  customer_id: int references Customer(id)
  title: string not null
  description: text
  amount: decimal(12,2)
  probability: decimal(5,2)
  stage: enum["prospecting", "qualification", "proposal", "negotiation", "closed_won", "closed_lost"]
  expected_close_date: date
  assigned_to: int references Employee(id)
  created_at: datetime default now
}

# 销售活动
entity SalesActivity {
  id: int primary key auto_increment
  opportunity_id: int references Opportunity(id)
  activity_type: enum["call", "email", "meeting", "presentation", "proposal"]
  subject: string
  description: text
  scheduled_date: datetime
  completed_date: datetime
  outcome: text
  next_action: text
  created_at: datetime default now
}
```

### 4.2 客户服务

```dsl
# 服务工单
entity ServiceTicket {
  id: int primary key auto_increment
  ticket_id: string unique
  customer_id: int references Customer(id)
  subject: string not null
  description: text
  priority: enum["low", "medium", "high", "critical"]
  status: enum["open", "in_progress", "waiting", "resolved", "closed"]
  category: enum["technical", "billing", "general", "feature_request"]
  assigned_to: int references Employee(id)
  created_at: datetime default now
  resolved_at: datetime
}

# 客户反馈
entity CustomerFeedback {
  id: int primary key auto_increment
  customer_id: int references Customer(id)
  rating: int  # 1-5
  feedback_type: enum["satisfaction", "complaint", "suggestion"]
  subject: string
  description: text
  response: text
  status: enum["new", "in_review", "responded", "closed"]
  created_at: datetime default now
}
```

## 5. 采购管理核心建模

### 5.1 采购流程

```dsl
# 采购申请
entity PurchaseRequest {
  id: int primary key auto_increment
  request_id: string unique
  requester_id: int references Employee(id)
  department_id: int references Department(id)
  title: string not null
  description: text
  urgency: enum["low", "medium", "high", "critical"]
  status: enum["draft", "submitted", "approved", "rejected", "ordered"]
  total_amount: decimal(12,2)
  created_at: datetime default now
}

# 采购订单
entity PurchaseOrder {
  id: int primary key auto_increment
  po_id: string unique
  request_id: int references PurchaseRequest(id)
  supplier_id: int references Supplier(id)
  order_date: date
  expected_delivery: date
  status: enum["draft", "sent", "confirmed", "shipped", "received", "cancelled"]
  total_amount: decimal(12,2)
  created_at: datetime default now
}

# 采购项目
entity PurchaseItem {
  id: int primary key auto_increment
  po_id: int references PurchaseOrder(id)
  item_name: string not null
  description: text
  quantity: int
  unit_price: decimal(10,2)
  total_price: decimal(10,2)
  received_quantity: int default 0
  created_at: datetime default now
}
```

### 5.2 供应商管理

```dsl
# 供应商评估
entity SupplierEvaluation {
  id: int primary key auto_increment
  supplier_id: int references Supplier(id)
  evaluator_id: int references Employee(id)
  evaluation_date: date
  quality_score: int  # 1-5
  delivery_score: int  # 1-5
  price_score: int  # 1-5
  communication_score: int  # 1-5
  overall_score: decimal(3,2)
  comments: text
  created_at: datetime default now
}

# 合同管理
entity Contract {
  id: int primary key auto_increment
  contract_id: string unique
  supplier_id: int references Supplier(id)
  contract_type: enum["goods", "services", "maintenance", "consulting"]
  start_date: date
  end_date: date
  total_value: decimal(12,2)
  status: enum["draft", "active", "expired", "terminated"]
  terms_conditions: text
  created_at: datetime default now
}
```

## 6. 资产管理核心建模

### 6.1 资产分类

```dsl
# 资产分类
entity AssetCategory {
  id: int primary key auto_increment
  category_id: string unique
  category_name: string not null
  parent_category_id: int references AssetCategory(id)
  description: text
  depreciation_method: enum["straight_line", "declining_balance", "sum_of_years"]
  useful_life: int  # years
  created_at: datetime default now
}

# 资产维护
entity AssetMaintenance {
  id: int primary key auto_increment
  asset_id: int references Asset(id)
  maintenance_type: enum["preventive", "corrective", "emergency"]
  description: text
  scheduled_date: date
  completed_date: date
  cost: decimal(10,2)
  performed_by: string
  status: enum["scheduled", "in_progress", "completed", "cancelled"]
  created_at: datetime default now
}
```

### 6.2 资产追踪

```dsl
# 资产移动记录
entity AssetMovement {
  id: int primary key auto_increment
  asset_id: int references Asset(id)
  from_location: string
  to_location: string
  from_employee: int references Employee(id)
  to_employee: int references Employee(id)
  movement_date: datetime
  reason: text
  approved_by: int references Employee(id)
  created_at: datetime default now
}

# 资产折旧
entity AssetDepreciation {
  id: int primary key auto_increment
  asset_id: int references Asset(id)
  depreciation_date: date
  depreciation_amount: decimal(10,2)
  accumulated_depreciation: decimal(10,2)
  book_value: decimal(10,2)
  created_at: datetime default now
}
```

## 7. 项目管理核心建模

### 7.1 项目计划

```dsl
# 项目任务
entity ProjectTask {
  id: int primary key auto_increment
  project_id: int references Project(id)
  task_name: string not null
  description: text
  start_date: date
  end_date: date
  duration: int  # days
  progress: decimal(5,2) default 0.0
  priority: enum["low", "medium", "high", "critical"]
  status: enum["not_started", "in_progress", "completed", "on_hold"]
  assigned_to: int references Employee(id)
  parent_task_id: int references ProjectTask(id)
  created_at: datetime default now
}

# 项目资源
entity ProjectResource {
  id: int primary key auto_increment
  project_id: int references Project(id)
  resource_type: enum["employee", "equipment", "material", "external"]
  resource_id: int  # references Employee(id) or Asset(id)
  role: string
  start_date: date
  end_date: date
  allocation_percentage: decimal(5,2)
  cost_per_hour: decimal(8,2)
  created_at: datetime default now
}
```

### 7.2 项目监控

```dsl
# 项目里程碑
entity ProjectMilestone {
  id: int primary key auto_increment
  project_id: int references Project(id)
  milestone_name: string not null
  description: text
  due_date: date
  status: enum["pending", "completed", "delayed"]
  completion_date: date
  created_at: datetime default now
}

# 项目风险
entity ProjectRisk {
  id: int primary key auto_increment
  project_id: int references Project(id)
  risk_name: string not null
  description: text
  probability: enum["low", "medium", "high"]
  impact: enum["low", "medium", "high", "critical"]
  status: enum["identified", "mitigated", "occurred", "closed"]
  mitigation_plan: text
  created_at: datetime default now
}
```

## 8. AI自动化推理能力

### 8.1 智能招聘

```dsl
# AI简历筛选
ai_resume_screening ResumeScreening {
  screening_criteria: [
    "skills_match",
    "experience_level",
    "education_requirements",
    "cultural_fit"
  ]
  
  ai_analysis: {
    skill_extraction: true,
    experience_assessment: true,
    cultural_fit_prediction: true,
    interview_recommendation: true
  }
  
  auto_scoring: {
    enabled: true,
    threshold: 0.7,
    ranking_algorithm: "weighted_score"
  }
}
```

### 8.2 智能销售

```dsl
# AI销售预测
ai_sales_prediction SalesPrediction {
  prediction_features: [
    "lead_score",
    "company_size",
    "industry",
    "interaction_history",
    "market_conditions"
  ]
  
  ai_analysis: {
    lead_scoring: true,
    opportunity_prioritization: true,
    close_probability: true,
    revenue_forecasting: true
  }
  
  auto_recommendations: {
    enabled: true,
    next_best_action: true,
    optimal_timing: true,
    personalized_content: true
  }
}
```

### 8.3 智能采购

```dsl
# AI供应商推荐
ai_supplier_recommendation SupplierRecommendation {
  recommendation_factors: [
    "historical_performance",
    "price_competitiveness",
    "quality_rating",
    "delivery_reliability",
    "financial_stability"
  ]
  
  ai_analysis: {
    supplier_scoring: true,
    risk_assessment: true,
    cost_optimization: true,
    market_analysis: true
  }
  
  auto_selection: {
    enabled: true,
    multi_criteria_analysis: true,
    negotiation_support: true
  }
}
```

## 9. 安全与合规

### 9.1 数据安全

```dsl
# 企业管理数据安全
enterprise_security EnterpriseSecurity {
  data_classification: {
    public: ["company_info", "product_catalog"],
    internal: ["employee_data", "project_info"],
    confidential: ["salary_data", "customer_contracts"],
    restricted: ["financial_data", "trade_secrets"]
  }
  
  access_control: {
    role_based_access: true,
    data_encryption: true,
    audit_logging: true,
    data_retention: true
  }
  
  compliance_standards: [
    "gdpr",
    "sox",
    "iso_27001",
    "pci_dss"
  ]
}
```

### 9.2 审计追踪

```dsl
# 审计日志
audit_logging EnterpriseAudit {
  tracked_actions: [
    "data_access",
    "data_modification",
    "user_authentication",
    "privilege_changes",
    "system_configuration"
  ]
  
  retention_policy: {
    audit_logs: "7_years",
    system_logs: "2_years",
    access_logs: "1_year"
  }
  
  alerting: {
    suspicious_activity: true,
    unauthorized_access: true,
    data_breach: true
  }
}
```

## 10. 与开源项目映射

### 10.1 与ERP系统映射

```dsl
# SAP ERP映射
sap_erp_mapping: {
  employee: "Employee",
  customer: "Customer",
  supplier: "Supplier",
  asset: "Asset",
  project: "Project"
}
```

### 10.2 与CRM系统映射

```dsl
# Salesforce CRM映射
salesforce_mapping: {
  lead: "Lead",
  opportunity: "Opportunity",
  account: "Customer",
  contact: "Contact",
  activity: "SalesActivity"
}
```

---

本节递归扩展了企业管理模型DSL，涵盖与通用模型的深度映射、AI自动化推理、HR管理、CRM、采购、资产、项目管理等内容，为企业管理系统的工程实现提供了全链路建模支撑。
