# CRM客户关系管理系统 DSL 草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述客户管理、销售管理、营销管理、服务管理等CRM核心业务要素，支持递归组合。
- 支持自动生成CRM系统代码、业务规则、报表、工作流等。
- 支持与通用数据模型、功能模型、交互模型的深度映射。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 与通用模型映射关系

### 2.1 数据模型映射

```dsl
# 客户实体映射到通用数据模型
entity Customer {
  id: int primary key auto_increment
  customer_id: string unique
  customer_name: string not null
  customer_type: enum["individual", "company", "partner", "prospect"]
  industry: string
  company_size: enum["startup", "small", "medium", "large", "enterprise"]
  status: enum["active", "inactive", "prospect", "lead", "customer"]
  source: enum["website", "referral", "cold_call", "event", "social_media"]
  created_at: datetime default now
  updated_at: datetime default now
}

# 联系人实体映射到通用数据模型
entity Contact {
  id: int primary key auto_increment
  contact_id: string unique
  customer_id: int references Customer(id)
  first_name: string not null
  last_name: string not null
  title: string
  email: string
  phone: string
  mobile: string
  is_primary: boolean default false
  is_decision_maker: boolean default false
  status: enum["active", "inactive", "unsubscribed"]
  created_at: datetime default now
}

# 销售机会实体映射到通用数据模型
entity Opportunity {
  id: int primary key auto_increment
  opportunity_id: string unique
  customer_id: int references Customer(id)
  opportunity_name: string not null
  description: text
  amount: decimal(15,2)
  currency: string default "USD"
  stage: enum["prospecting", "qualification", "proposal", "negotiation", "closed_won", "closed_lost"]
  probability: decimal(5,2)
  expected_close_date: date
  assigned_to: int references Employee(id)
  created_at: datetime default now
}
```

### 2.2 功能模型映射

```dsl
# 客户创建业务逻辑映射到通用功能模型
business_logic CustomerCreation {
  input: [customer_data, contact_info, source_info]
  validation: [
    { field: "customer_name", rule: "unique_customer_name" },
    { field: "email", rule: "valid_email_format" },
    { field: "phone", rule: "valid_phone_format" },
    { field: "source", rule: "valid_source_type" }
  ]
  process: [
    { step: "validate_customer_data", condition: "all_valid" },
    { step: "create_customer_record", output: "customer_id" },
    { step: "create_primary_contact", input: "customer_id" },
    { step: "assign_sales_representative", input: "customer_id" },
    { step: "create_initial_opportunity", input: "customer_id" },
    { step: "send_welcome_email", input: "customer_id" }
  ]
  output: "customer_creation_result"
  error_handling: {
    duplicate_customer: "return_error_message",
    invalid_contact: "return_error_message",
    system_error: "rollback_and_retry"
  }
}

# 销售机会评分规则引擎映射到通用功能模型
rule_engine OpportunityScoring {
  rules: [
    {
      name: "budget_rule",
      condition: "budget_amount > 10000",
      action: "increase_score(20)",
      priority: 1
    },
    {
      name: "authority_rule",
      condition: "decision_maker_contacted",
      action: "increase_score(15)",
      priority: 2
    },
    {
      name: "timeline_rule",
      condition: "close_date <= 30_days",
      action: "increase_score(10)",
      priority: 3
    }
  ]
  aggregation: "total_opportunity_score"
  output: "opportunity_priority"
}
```

### 2.3 交互模型映射

```dsl
# CRM API接口映射到通用交互模型
api CRMAPI {
  endpoints: [
    {
      path: "/customers",
      method: "GET",
      response: "CustomerList",
      security: "oauth2"
    },
    {
      path: "/customers",
      method: "POST",
      request: "CustomerCreateRequest",
      response: "CustomerCreated",
      security: "oauth2"
    },
    {
      path: "/opportunities",
      method: "GET",
      response: "OpportunityList",
      security: "oauth2"
    },
    {
      path: "/opportunities/{opportunity_id}/update-stage",
      method: "POST",
      request: "StageUpdateRequest",
      response: "StageUpdated",
      security: "oauth2"
    },
    {
      path: "/leads",
      method: "GET",
      response: "LeadList",
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

### 3.1 客户管理

```dsl
# 客户画像
entity CustomerProfile {
  id: int primary key auto_increment
  customer_id: int references Customer(id)
  profile_data: {
    demographics: {
      age_range: string,
      gender: enum["male", "female", "other"],
      location: string,
      income_level: string
    },
    preferences: {
      communication_channel: enum["email", "phone", "sms", "social"],
      preferred_time: string,
      language: string
    },
    behavior: {
      purchase_frequency: string,
      average_order_value: decimal(10,2),
      loyalty_level: enum["bronze", "silver", "gold", "platinum"]
    }
  }
  created_at: datetime default now
  updated_at: datetime default now
}

# 客户状态机
state_machine CustomerState {
  states: [
    { name: "lead", initial: true },
    { name: "prospect" },
    { name: "qualified" },
    { name: "customer" },
    { name: "lapsed", final: true }
  ]
  transitions: [
    { from: "lead", to: "prospect", event: "initial_contact" },
    { from: "prospect", to: "qualified", event: "qualification_complete" },
    { from: "qualified", to: "customer", event: "first_purchase" },
    { from: "customer", to: "lapsed", event: "inactivity_period" }
  ]
}
```

### 3.2 销售管理

```dsl
# 销售管道
entity SalesPipeline {
  id: int primary key auto_increment
  pipeline_id: string unique
  pipeline_name: string not null
  stages: [{
    stage_name: string,
    stage_order: int,
    probability: decimal(5,2),
    average_duration: int
  }]
  total_value: decimal(15,2)
  active_opportunities: int
  created_at: datetime default now
}

# 销售活动
entity SalesActivity {
  id: int primary key auto_increment
  activity_id: string unique
  opportunity_id: int references Opportunity(id)
  activity_type: enum["call", "email", "meeting", "presentation", "proposal"]
  subject: string
  description: text
  scheduled_date: datetime
  completed_date: datetime
  duration: int  # minutes
  outcome: enum["positive", "neutral", "negative"]
  next_action: text
  assigned_to: int references Employee(id)
  created_at: datetime default now
}

# 销售预测
rule_engine SalesForecasting {
  rules: [
    {
      name: "stage_probability_rule",
      condition: "stage = 'negotiation'",
      action: "apply_stage_probability(0.7)",
      priority: 1
    },
    {
      name: "historical_performance_rule",
      condition: "sales_rep_performance > 0.8",
      action: "increase_probability(0.1)",
      priority: 2
    },
    {
      name: "customer_relationship_rule",
      condition: "customer_lifetime_value > 50000",
      action: "increase_probability(0.15)",
      priority: 3
    }
  ]
  aggregation: "weighted_forecast"
  output: "sales_forecast"
}
```

### 3.3 营销管理

```dsl
# 营销活动
entity MarketingCampaign {
  id: int primary key auto_increment
  campaign_id: string unique
  campaign_name: string not null
  campaign_type: enum["email", "social_media", "webinar", "event", "content"]
  target_audience: [string]
  start_date: date
  end_date: date
  budget: decimal(10,2)
  status: enum["draft", "active", "paused", "completed"]
  metrics: {
    impressions: int,
    clicks: int,
    conversions: int,
    roi: decimal(5,2)
  }
  created_at: datetime default now
}

# 营销自动化
workflow MarketingAutomation {
  steps: [
    {
      name: "lead_capture",
      type: "trigger",
      required: ["lead_source", "contact_info"]
    },
    {
      name: "lead_scoring",
      type: "automated",
      required: ["scoring_rules", "threshold"],
      depends_on: ["lead_capture"]
    },
    {
      name: "lead_nurturing",
      type: "automated",
      required: ["nurturing_sequence", "content"],
      depends_on: ["lead_scoring"]
    },
    {
      name: "sales_handoff",
      type: "automated",
      required: ["handoff_criteria", "sales_rep"],
      depends_on: ["lead_nurturing"]
    }
  ]
  timeouts: {
    lead_capture: "immediate",
    lead_scoring: "5m",
    lead_nurturing: "variable",
    sales_handoff: "1h"
  }
}
```

### 3.4 服务管理

```dsl
# 服务工单
entity ServiceTicket {
  id: int primary key auto_increment
  ticket_id: string unique
  customer_id: int references Customer(id)
  contact_id: int references Contact(id)
  ticket_type: enum["support", "bug", "feature_request", "billing", "general"]
  priority: enum["low", "medium", "high", "critical"]
  status: enum["open", "in_progress", "waiting", "resolved", "closed"]
  subject: string
  description: text
  assigned_to: int references Employee(id)
  created_at: datetime default now
  resolved_at: datetime
  satisfaction_score: int
}

# 服务级别协议
entity ServiceLevelAgreement {
  id: int primary key auto_increment
  sla_id: string unique
  sla_name: string not null
  priority_level: enum["low", "medium", "high", "critical"]
  response_time: int  # hours
  resolution_time: int  # hours
  business_hours: {
    start_time: time,
    end_time: time,
    timezone: string
  }
  created_at: datetime default now
}

# 服务质量监控
rule_engine ServiceQualityMonitoring {
  rules: [
    {
      name: "response_time_rule",
      condition: "response_time > sla_response_time",
      action: "escalate_ticket",
      priority: 1
    },
    {
      name: "resolution_time_rule",
      condition: "resolution_time > sla_resolution_time",
      action: "escalate_ticket",
      priority: 2
    },
    {
      name: "satisfaction_rule",
      condition: "satisfaction_score < 3",
      action: "flag_for_review",
      priority: 3
    }
  ]
  aggregation: "service_quality_score"
  output: "quality_alerts"
}
```

## 4. AI自动化推理能力

### 4.1 智能客户分析

```dsl
# 客户价值预测
ai_customer_value_prediction CustomerValuePrediction {
  features: [
    "purchase_history",
    "interaction_frequency",
    "product_preferences",
    "payment_behavior"
  ]
  prediction_horizon: "12_months"
  confidence_interval: 0.9
  output: "customer_lifetime_value"
}

# 客户流失预测
ai_churn_prediction ChurnPrediction {
  features: [
    "usage_patterns",
    "support_interactions",
    "payment_history",
    "engagement_metrics"
  ]
  risk_threshold: 0.6
  output: "churn_probability"
}
```

### 4.2 智能销售优化

```dsl
# 销售机会评分
ai_opportunity_scoring OpportunityScoring {
  features: [
    "customer_profile",
    "interaction_history",
    "market_conditions",
    "competitive_factors"
  ]
  scoring_model: "gradient_boosting"
  output: "opportunity_score"
}

# 销售预测
ai_sales_forecasting SalesForecasting {
  features: [
    "pipeline_data",
    "historical_performance",
    "market_trends",
    "seasonal_factors"
  ]
  forecasting_method: "time_series_analysis"
  forecast_period: "6_months"
  output: "sales_forecast"
}
```

### 4.3 智能营销优化

```dsl
# 客户细分
ai_customer_segmentation CustomerSegmentation {
  features: [
    "demographics",
    "behavior_patterns",
    "purchase_history",
    "engagement_metrics"
  ]
  segmentation_method: "clustering_algorithm"
  output: "customer_segments"
}

# 营销活动优化
ai_campaign_optimization CampaignOptimization {
  optimization_algorithm: "multi_armed_bandit"
  objectives: [
    "maximize_conversions",
    "minimize_cost",
    "maximize_roi"
  ]
  constraints: [
    "budget_limit",
    "audience_size",
    "campaign_duration"
  ]
  output: "optimal_campaign_strategy"
}
```

## 5. 安全与合规

```dsl
# CRM数据安全
crm_security CRMSecurity {
  data_protection: {
    encryption: "AES-256",
    access_control: "role_based",
    data_masking: true
  }
  privacy_compliance: {
    gdpr_compliance: true,
    data_consent: true,
    right_to_forget: true
  }
  audit_trail: {
    data_access: true,
    data_modifications: true,
    user_actions: true
  }
}

# CRM合规检查
crm_compliance CRMCompliance {
  regulatory_compliance: {
    data_protection: true,
    financial_regulations: true,
    industry_standards: true
  }
  data_governance: {
    data_quality: true,
    data_lineage: true,
    data_catalog: true
  }
}
```

## 6. 监控与报告

```dsl
# CRM指标监控
crm_metrics CRMMetrics {
  sales_metrics: [
    "revenue",
    "conversion_rate",
    "sales_cycle_length",
    "average_deal_size"
  ]
  marketing_metrics: [
    "lead_generation",
    "campaign_performance",
    "cost_per_lead",
    "marketing_roi"
  ]
  service_metrics: [
    "customer_satisfaction",
    "response_time",
    "resolution_time",
    "ticket_volume"
  ]
}

# 自动化报告
automated_reports CRMReports {
  reports: [
    {
      name: "daily_sales_summary",
      schedule: "daily",
      recipients: ["sales_manager", "sales_team"]
    },
    {
      name: "weekly_crm_performance",
      schedule: "weekly",
      recipients: ["crm_manager", "executive_team"]
    },
    {
      name: "monthly_customer_analysis",
      schedule: "monthly",
      recipients: ["marketing_manager", "customer_success"]
    }
  ]
}
```

---

本节递归扩展了CRM客户关系管理系统DSL，涵盖与通用模型的深度映射、AI自动化推理、核心业务建模、安全合规等内容，为CRM系统的工程实现提供了全链路建模支撑。
