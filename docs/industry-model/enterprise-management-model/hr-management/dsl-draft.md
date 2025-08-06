# HR管理系统 DSL 草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述员工管理、薪资管理、绩效管理、培训管理等HR核心业务要素，支持递归组合。
- 支持自动生成HR系统代码、业务规则、报表、工作流等。
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
  status: enum["active", "inactive", "terminated"]
  manager_id: int references Employee(id)
  created_at: datetime default now
  updated_at: datetime default now
}

# 部门实体映射到通用数据模型
entity Department {
  id: int primary key auto_increment
  department_code: string unique
  department_name: string not null
  parent_department_id: int references Department(id)
  manager_id: int references Employee(id)
  budget: decimal(15,2)
  status: enum["active", "inactive"]
  created_at: datetime default now
}

# 职位实体映射到通用数据模型
entity Position {
  id: int primary key auto_increment
  position_code: string unique
  position_name: string not null
  department_id: int references Department(id)
  level: int
  salary_range_min: decimal(10,2)
  salary_range_max: decimal(10,2)
  status: enum["active", "inactive"]
}
```

### 2.2 功能模型映射

```dsl
# 员工入职业务逻辑映射到通用功能模型
business_logic EmployeeOnboarding {
  input: [employee_data, position_data, department_data]
  validation: [
    { field: "employee_id", rule: "unique_employee_id" },
    { field: "email", rule: "valid_email_format" },
    { field: "department", rule: "department_exists" },
    { field: "position", rule: "position_exists" }
  ]
  process: [
    { step: "validate_employee_data", condition: "all_valid" },
    { step: "create_employee_record", output: "employee_id" },
    { step: "assign_department", input: "employee_id" },
    { step: "assign_position", input: "employee_id" },
    { step: "setup_system_access", input: "employee_id" },
    { step: "send_welcome_email", input: "employee_id" }
  ]
  output: "onboarding_result"
  error_handling: {
    duplicate_employee: "return_error_message",
    invalid_department: "return_error_message",
    system_error: "rollback_and_retry"
  }
}

# 薪资计算规则引擎映射到通用功能模型
rule_engine SalaryCalculation {
  rules: [
    {
      name: "base_salary_rule",
      condition: "position_level = 1",
      action: "set_base_salary(5000)",
      priority: 1
    },
    {
      name: "experience_bonus_rule",
      condition: "years_of_experience > 5",
      action: "add_experience_bonus(1000)",
      priority: 2
    },
    {
      name: "performance_bonus_rule",
      condition: "performance_rating >= 4.5",
      action: "add_performance_bonus(2000)",
      priority: 3
    }
  ]
  aggregation: "total_salary_calculation"
  output: "salary_structure"
}
```

### 2.3 交互模型映射

```dsl
# HR API接口映射到通用交互模型
api HRManagementAPI {
  endpoints: [
    {
      path: "/employees",
      method: "GET",
      response: "EmployeeList",
      security: "oauth2"
    },
    {
      path: "/employees/{employee_id}",
      method: "GET",
      response: "EmployeeDetails",
      security: "oauth2"
    },
    {
      path: "/employees",
      method: "POST",
      request: "EmployeeCreateRequest",
      response: "EmployeeCreated",
      security: "oauth2"
    },
    {
      path: "/departments",
      method: "GET",
      response: "DepartmentList",
      security: "oauth2"
    },
    {
      path: "/salary/calculate",
      method: "POST",
      request: "SalaryCalculationRequest",
      response: "SalaryCalculationResult",
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

### 3.1 员工管理

```dsl
# 员工信息管理
entity EmployeeProfile {
  id: int primary key auto_increment
  employee_id: int references Employee(id)
  personal_info: {
    date_of_birth: date,
    gender: enum["male", "female", "other"],
    nationality: string,
    id_number: string,
    address: text
  }
  emergency_contact: {
    name: string,
    relationship: string,
    phone: string,
    email: string
  }
  bank_info: {
    bank_name: string,
    account_number: string,
    routing_number: string
  }
  created_at: datetime default now
  updated_at: datetime default now
}

# 员工状态机
state_machine EmployeeStatus {
  states: [
    { name: "candidate", initial: true },
    { name: "onboarded" },
    { name: "probation" },
    { name: "active" },
    { name: "on_leave" },
    { name: "terminated", final: true }
  ]
  transitions: [
    { from: "candidate", to: "onboarded", event: "complete_onboarding" },
    { from: "onboarded", to: "probation", event: "start_probation" },
    { from: "probation", to: "active", event: "pass_probation" },
    { from: "active", to: "on_leave", event: "request_leave" },
    { from: "on_leave", to: "active", event: "return_from_leave" },
    { from: "active", to: "terminated", event: "terminate_employment" }
  ]
}
```

### 3.2 薪资管理

```dsl
# 薪资结构
entity SalaryStructure {
  id: int primary key auto_increment
  employee_id: int references Employee(id)
  base_salary: decimal(10,2) not null
  allowances: {
    housing_allowance: decimal(8,2),
    transportation_allowance: decimal(8,2),
    meal_allowance: decimal(8,2)
  }
  deductions: {
    tax: decimal(8,2),
    insurance: decimal(8,2),
    pension: decimal(8,2)
  }
  effective_date: date not null
  end_date: date
  status: enum["active", "inactive"]
}

# 薪资计算规则
rule_engine SalaryRules {
  rules: [
    {
      name: "tax_calculation",
      condition: "monthly_income > 5000",
      action: "calculate_tax(progressive_rate)",
      priority: 1
    },
    {
      name: "overtime_pay",
      condition: "weekly_hours > 40",
      action: "calculate_overtime(1.5_rate)",
      priority: 2
    },
    {
      name: "bonus_calculation",
      condition: "performance_rating >= 4.0",
      action: "calculate_bonus(performance_based)",
      priority: 3
    }
  ]
  aggregation: "total_salary"
  output: "payroll_statement"
}
```

### 3.3 绩效管理

```dsl
# 绩效评估
entity PerformanceReview {
  id: int primary key auto_increment
  employee_id: int references Employee(id)
  reviewer_id: int references Employee(id)
  review_period: {
    start_date: date,
    end_date: date
  }
  performance_metrics: {
    quality_score: decimal(3,2),
    productivity_score: decimal(3,2),
    teamwork_score: decimal(3,2),
    innovation_score: decimal(3,2)
  }
  overall_rating: decimal(3,2)
  comments: text
  goals: [text]
  review_date: date
  status: enum["draft", "submitted", "approved", "completed"]
}

# 绩效评估工作流
workflow PerformanceReviewWorkflow {
  steps: [
    {
      name: "self_assessment",
      type: "employee_input",
      required: ["performance_metrics", "self_comments"]
    },
    {
      name: "manager_review",
      type: "manager_input",
      required: ["performance_metrics", "manager_comments"],
      depends_on: ["self_assessment"]
    },
    {
      name: "hr_review",
      type: "hr_input",
      required: ["hr_comments", "goals_setting"],
      depends_on: ["manager_review"]
    },
    {
      name: "final_approval",
      type: "approval",
      required: ["final_rating", "approval"],
      depends_on: ["hr_review"]
    }
  ]
  timeouts: {
    self_assessment: "7d",
    manager_review: "5d",
    hr_review: "3d",
    final_approval: "2d"
  }
}
```

### 3.4 培训管理

```dsl
# 培训课程
entity TrainingCourse {
  id: int primary key auto_increment
  course_code: string unique
  course_name: string not null
  description: text
  category: enum["technical", "soft_skills", "compliance", "leadership"]
  duration: int  # hours
  cost: decimal(8,2)
  instructor: string
  max_participants: int
  status: enum["active", "inactive"]
}

# 培训计划
entity TrainingPlan {
  id: int primary key auto_increment
  employee_id: int references Employee(id)
  course_id: int references TrainingCourse(id)
  enrollment_date: date
  completion_date: date
  status: enum["enrolled", "in_progress", "completed", "dropped"]
  score: decimal(5,2)
  certificate_url: string
}

# 培训推荐规则
rule_engine TrainingRecommendation {
  rules: [
    {
      name: "skill_gap_rule",
      condition: "required_skills != current_skills",
      action: "recommend_skill_courses",
      priority: 1
    },
    {
      name: "career_path_rule",
      condition: "career_level = 'junior'",
      action: "recommend_leadership_courses",
      priority: 2
    },
    {
      name: "compliance_rule",
      condition: "compliance_training_due",
      action: "recommend_compliance_courses",
      priority: 3
    }
  ]
  aggregation: "personalized_training_plan"
  output: "recommended_courses"
}
```

## 4. AI自动化推理能力

### 4.1 智能招聘

```dsl
# AI简历筛选
ai_resume_screening ResumeScreening {
  features: [
    "skills_match",
    "experience_level",
    "education_qualification",
    "cultural_fit"
  ]
  model_type: "random_forest"
  training_data: "historical_hiring_data"
  threshold: 0.7
  output: "candidate_score"
}

# 智能面试安排
ai_interview_scheduling InterviewScheduling {
  optimization_algorithm: "genetic_algorithm"
  constraints: [
    "interviewer_availability",
    "candidate_availability",
    "interview_room_availability",
    "interview_type_requirements"
  ]
  output: "optimal_schedule"
}
```

### 4.2 智能绩效分析

```dsl
# 绩效预测模型
ai_performance_prediction PerformancePrediction {
  features: [
    "historical_performance",
    "training_completion",
    "project_participation",
    "peer_feedback"
  ]
  prediction_horizon: "6_months"
  confidence_interval: 0.9
  output: "performance_prediction"
}

# 离职风险预测
ai_turnover_prediction TurnoverPrediction {
  features: [
    "job_satisfaction",
    "salary_comparison",
    "promotion_history",
    "workload_stress"
  ]
  risk_threshold: 0.6
  output: "turnover_risk_score"
}
```

### 4.3 智能薪资优化

```dsl
# 市场薪资分析
ai_salary_analysis MarketSalaryAnalysis {
  data_sources: [
    "industry_surveys",
    "market_reports",
    "competitor_data"
  ]
  analysis_method: "regression_analysis"
  output: "market_salary_benchmark"
}

# 薪资公平性检测
ai_salary_fairness SalaryFairness {
  protected_attributes: ["gender", "age", "ethnicity"]
  fairness_metrics: [
    "statistical_parity",
    "equalized_odds",
    "demographic_parity"
  ]
  output: "fairness_report"
}
```

## 5. 安全与合规

```dsl
# 数据隐私保护
data_privacy HRDataPrivacy {
  sensitive_fields: [
    "salary",
    "performance_rating",
    "personal_address",
    "emergency_contact"
  ]
  encryption: {
    algorithm: "AES-256",
    key_rotation: "monthly"
  }
  access_control: {
    role_based: true,
    data_masking: true,
    audit_logging: true
  }
}

# 合规检查
compliance_checks HRCompliance {
  labor_law: {
    working_hours: "max_8_hours_per_day",
    overtime_pay: "1.5x_rate",
    leave_entitlement: "annual_leave_calculation"
  }
  data_protection: {
    gdpr_compliance: true,
    data_retention: "7_years",
    consent_management: true
  }
  equal_opportunity: {
    anti_discrimination: true,
    diversity_tracking: true,
    bias_detection: true
  }
}
```

## 6. 监控与报告

```dsl
# HR指标监控
hr_metrics HRMetrics {
  employee_metrics: [
    "headcount",
    "turnover_rate",
    "diversity_ratio",
    "satisfaction_score"
  ]
  performance_metrics: [
    "average_performance_rating",
    "promotion_rate",
    "training_completion_rate"
  ]
  cost_metrics: [
    "salary_cost",
    "training_cost",
    "recruitment_cost"
  ]
}

# 自动化报告
automated_reports HRReports {
  reports: [
    {
      name: "monthly_hr_summary",
      schedule: "monthly",
      recipients: ["hr_director", "ceo"]
    },
    {
      name: "quarterly_performance_review",
      schedule: "quarterly",
      recipients: ["department_managers"]
    },
    {
      name: "annual_compensation_analysis",
      schedule: "annually",
      recipients: ["hr_team", "finance_team"]
    }
  ]
}
```

---

本节递归扩展了HR管理系统DSL，涵盖与通用模型的深度映射、AI自动化推理、核心业务建模、安全合规等内容，为HR管理系统的工程实现提供了全链路建模支撑。
