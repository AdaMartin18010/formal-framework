# 项目管理系统 DSL 草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述项目规划、任务管理、资源分配、进度跟踪等项目管理核心业务要素，支持递归组合。
- 支持自动生成项目系统代码、业务规则、报表、工作流等。
- 支持与通用数据模型、功能模型、交互模型的深度映射。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 与通用模型映射关系

### 2.1 数据模型映射

```dsl
# 项目实体映射到通用数据模型
entity Project {
  id: int primary key auto_increment
  project_id: string unique
  project_name: string not null
  project_code: string unique
  description: text
  project_type: enum["development", "research", "consulting", "maintenance", "migration"]
  status: enum["planning", "active", "on_hold", "completed", "cancelled"]
  priority: enum["low", "medium", "high", "critical"]
  start_date: date not null
  end_date: date
  budget: decimal(15,2)
  currency: string default "USD"
  manager_id: int references Employee(id)
  client_id: int references Client(id)
  created_at: datetime default now
  updated_at: datetime default now
}

# 任务实体映射到通用数据模型
entity Task {
  id: int primary key auto_increment
  task_id: string unique
  project_id: int references Project(id)
  task_name: string not null
  description: text
  task_type: enum["milestone", "deliverable", "activity", "subtask"]
  status: enum["not_started", "in_progress", "review", "completed", "cancelled"]
  priority: enum["low", "medium", "high", "critical"]
  estimated_hours: decimal(8,2)
  actual_hours: decimal(8,2)
  start_date: date
  due_date: date
  assigned_to: int references Employee(id)
  parent_task_id: int references Task(id)
  created_at: datetime default now
}

# 资源实体映射到通用数据模型
entity Resource {
  id: int primary key auto_increment
  resource_id: string unique
  resource_name: string not null
  resource_type: enum["human", "equipment", "material", "software", "facility"]
  category: string
  cost_per_hour: decimal(8,2)
  availability: {
    start_date: date,
    end_date: date,
    working_hours: int,
    capacity: decimal(5,2)
  }
  skills: [string]
  status: enum["available", "allocated", "unavailable"]
  created_at: datetime default now
}
```

### 2.2 功能模型映射

```dsl
# 项目创建业务逻辑映射到通用功能模型
business_logic ProjectCreation {
  input: [project_data, resource_requirements, timeline_constraints]
  validation: [
    { field: "project_name", rule: "unique_project_name" },
    { field: "start_date", rule: "valid_start_date" },
    { field: "budget", rule: "positive_budget_amount" },
    { field: "manager", rule: "valid_manager_assignment" }
  ]
  process: [
    { step: "validate_project_data", condition: "all_valid" },
    { step: "create_project_record", output: "project_id" },
    { step: "assign_project_manager", input: "project_id" },
    { step: "create_initial_tasks", input: "project_id" },
    { step: "allocate_resources", input: "project_id" },
    { step: "send_notifications", input: "project_id" }
  ]
  output: "project_creation_result"
  error_handling: {
    duplicate_project: "return_error_message",
    invalid_dates: "return_error_message",
    insufficient_budget: "return_error_message"
  }
}

# 任务分配规则引擎映射到通用功能模型
rule_engine TaskAssignment {
  rules: [
    {
      name: "skill_match_rule",
      condition: "required_skills matches available_skills",
      action: "assign_to_qualified_resource",
      priority: 1
    },
    {
      name: "availability_rule",
      condition: "resource_available_during_task_period",
      action: "assign_to_available_resource",
      priority: 2
    },
    {
      name: "workload_balance_rule",
      condition: "current_workload < max_capacity",
      action: "assign_to_underutilized_resource",
      priority: 3
    }
  ]
  aggregation: "optimal_assignment"
  output: "task_assignment_result"
}
```

### 2.3 交互模型映射

```dsl
# 项目管理API接口映射到通用交互模型
api ProjectManagementAPI {
  endpoints: [
    {
      path: "/projects",
      method: "GET",
      response: "ProjectList",
      security: "oauth2"
    },
    {
      path: "/projects",
      method: "POST",
      request: "ProjectCreateRequest",
      response: "ProjectCreated",
      security: "oauth2"
    },
    {
      path: "/projects/{project_id}/tasks",
      method: "GET",
      response: "TaskList",
      security: "oauth2"
    },
    {
      path: "/tasks/{task_id}/assign",
      method: "POST",
      request: "TaskAssignmentRequest",
      response: "TaskAssigned",
      security: "oauth2"
    },
    {
      path: "/projects/{project_id}/progress",
      method: "GET",
      response: "ProjectProgress",
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

### 3.1 项目规划

```dsl
# 项目计划
entity ProjectPlan {
  id: int primary key auto_increment
  project_id: int references Project(id)
  plan_version: string
  planning_methodology: enum["waterfall", "agile", "hybrid", "lean"]
  phases: [{
    phase_name: string,
    start_date: date,
    end_date: date,
    deliverables: [string],
    milestones: [string]
  }]
  risk_assessment: [{
    risk_id: string,
    risk_description: text,
    probability: enum["low", "medium", "high"],
    impact: enum["low", "medium", "high"],
    mitigation_strategy: text
  }]
  quality_standards: [string]
  created_at: datetime default now
}

# 项目计划状态机
state_machine ProjectPlanState {
  states: [
    { name: "draft", initial: true },
    { name: "review" },
    { name: "approved" },
    { name: "executing" },
    { name: "monitoring" },
    { name: "completed", final: true }
  ]
  transitions: [
    { from: "draft", to: "review", event: "submit_for_review" },
    { from: "review", to: "approved", event: "approve_plan" },
    { from: "approved", to: "executing", event: "start_execution" },
    { from: "executing", to: "monitoring", event: "begin_monitoring" },
    { from: "monitoring", to: "completed", event: "complete_project" }
  ]
}
```

### 3.2 任务管理

```dsl
# 任务依赖关系
entity TaskDependency {
  id: int primary key auto_increment
  dependent_task_id: int references Task(id)
  prerequisite_task_id: int references Task(id)
  dependency_type: enum["finish_to_start", "start_to_start", "finish_to_finish", "start_to_finish"]
  lag_days: int default 0
  created_at: datetime default now
}

# 任务工作流
workflow TaskWorkflow {
  steps: [
    {
      name: "task_creation",
      type: "user_input",
      required: ["task_name", "description", "estimated_hours", "due_date"]
    },
    {
      name: "task_assignment",
      type: "resource_assignment",
      required: ["assigned_to", "resource_allocation"],
      depends_on: ["task_creation"]
    },
    {
      name: "task_execution",
      type: "execution",
      required: ["progress_updates", "time_tracking"],
      depends_on: ["task_assignment"]
    },
    {
      name: "task_review",
      type: "review",
      required: ["quality_check", "acceptance_criteria"],
      depends_on: ["task_execution"]
    },
    {
      name: "task_completion",
      type: "completion",
      required: ["final_approval", "documentation"],
      depends_on: ["task_review"]
    }
  ]
  timeouts: {
    task_creation: "1d",
    task_assignment: "2d",
    task_execution: "variable",
    task_review: "1d",
    task_completion: "1d"
  }
}
```

### 3.3 资源管理

```dsl
# 资源分配
entity ResourceAllocation {
  id: int primary key auto_increment
  resource_id: int references Resource(id)
  project_id: int references Project(id)
  task_id: int references Task(id)
  allocation_start: date not null
  allocation_end: date not null
  allocation_percentage: decimal(5,2) not null
  allocation_type: enum["full_time", "part_time", "overtime"]
  cost_rate: decimal(8,2)
  status: enum["planned", "active", "completed", "cancelled"]
  created_at: datetime default now
}

# 资源优化规则
rule_engine ResourceOptimization {
  rules: [
    {
      name: "capacity_optimization_rule",
      condition: "resource_utilization < 80%",
      action: "increase_allocation",
      priority: 1
    },
    {
      name: "cost_optimization_rule",
      condition: "cost_per_hour > budget_threshold",
      action: "find_lower_cost_alternative",
      priority: 2
    },
    {
      name: "skill_optimization_rule",
      condition: "skill_mismatch_detected",
      action: "reassign_to_better_match",
      priority: 3
    }
  ]
  aggregation: "optimal_resource_allocation"
  output: "resource_optimization_plan"
}
```

### 3.4 进度跟踪

```dsl
# 进度报告
entity ProgressReport {
  id: int primary key auto_increment
  project_id: int references Project(id)
  report_date: date not null
  report_period: {
    start_date: date,
    end_date: date
  }
  progress_metrics: {
    overall_progress: decimal(5,2),
    schedule_variance: decimal(8,2),
    cost_variance: decimal(8,2),
    quality_score: decimal(3,2)
  }
  completed_tasks: int
  total_tasks: int
  issues: [{
    issue_id: string,
    description: text,
    severity: enum["low", "medium", "high", "critical"],
    status: enum["open", "in_progress", "resolved"]
  }]
  created_at: datetime default now
}

# 进度跟踪规则
rule_engine ProgressTracking {
  rules: [
    {
      name: "schedule_variance_rule",
      condition: "schedule_variance > 10%",
      action: "trigger_schedule_alert",
      priority: 1
    },
    {
      name: "cost_variance_rule",
      condition: "cost_variance > 5%",
      action: "trigger_cost_alert",
      priority: 2
    },
    {
      name: "quality_rule",
      condition: "quality_score < 0.8",
      action: "trigger_quality_alert",
      priority: 3
    }
  ]
  aggregation: "project_health_assessment"
  output: "progress_alerts"
}
```

## 4. AI自动化推理能力

### 4.1 智能项目规划

```dsl
# 自动项目估算
ai_project_estimation ProjectEstimation {
  features: [
    "project_complexity",
    "team_experience",
    "technology_stack",
    "historical_data"
  ]
  estimation_method: "machine_learning"
  confidence_interval: 0.9
  output: "project_estimate"
}

# 自动资源推荐
ai_resource_recommendation ResourceRecommendation {
  features: [
    "required_skills",
    "project_timeline",
    "resource_availability",
    "cost_constraints"
  ]
  recommendation_algorithm: "collaborative_filtering"
  output: "recommended_resources"
}
```

### 4.2 智能进度预测

```dsl
# 进度预测模型
ai_progress_prediction ProgressPrediction {
  features: [
    "current_progress",
    "team_velocity",
    "task_complexity",
    "resource_availability"
  ]
  prediction_horizon: "project_duration"
  confidence_interval: 0.85
  output: "progress_forecast"
}

# 风险预测
ai_risk_prediction RiskPrediction {
  features: [
    "project_metrics",
    "team_performance",
    "external_factors",
    "historical_risks"
  ]
  risk_model: "ensemble_classifier"
  risk_threshold: 0.7
  output: "risk_probability"
}
```

### 4.3 智能优化建议

```dsl
# 项目优化建议
ai_project_optimization ProjectOptimization {
  optimization_algorithm: "genetic_algorithm"
  objectives: [
    "minimize_duration",
    "minimize_cost",
    "maximize_quality",
    "maximize_resource_utilization"
  ]
  constraints: [
    "budget_limit",
    "resource_availability",
    "quality_requirements"
  ]
  output: "optimization_recommendations"
}

# 自动任务调度
ai_task_scheduling TaskScheduling {
  scheduling_algorithm: "constraint_satisfaction"
  constraints: [
    "task_dependencies",
    "resource_availability",
    "skill_requirements",
    "deadlines"
  ]
  output: "optimal_schedule"
}
```

## 5. 安全与合规

```dsl
# 项目数据安全
project_security ProjectSecurity {
  data_protection: {
    encryption: "AES-256",
    access_control: "role_based",
    audit_logging: true
  }
  intellectual_property: {
    confidentiality: true,
    non_disclosure: true,
    patent_protection: true
  }
  compliance: {
    industry_standards: true,
    regulatory_requirements: true,
    quality_management: true
  }
}

# 项目审计
project_audit ProjectAudit {
  audit_scope: [
    "project_planning",
    "resource_allocation",
    "progress_tracking",
    "cost_management"
  ]
  audit_frequency: "quarterly"
  compliance_check: "automated"
}
```

## 6. 监控与报告

```dsl
# 项目指标监控
project_metrics ProjectMetrics {
  performance_metrics: [
    "schedule_performance",
    "cost_performance",
    "quality_performance",
    "resource_utilization"
  ]
  efficiency_metrics: [
    "team_velocity",
    "task_completion_rate",
    "defect_rate",
    "customer_satisfaction"
  ]
  risk_metrics: [
    "risk_exposure",
    "issue_resolution_time",
    "change_request_rate"
  ]
}

# 自动化报告
automated_reports ProjectReports {
  reports: [
    {
      name: "weekly_progress_report",
      schedule: "weekly",
      recipients: ["project_manager", "stakeholders"]
    },
    {
      name: "monthly_project_summary",
      schedule: "monthly",
      recipients: ["project_director", "executive_team"]
    },
    {
      name: "quarterly_portfolio_review",
      schedule: "quarterly",
      recipients: ["portfolio_manager", "ceo"]
    }
  ]
}
```

---

本节递归扩展了项目管理系统DSL，涵盖与通用模型的深度映射、AI自动化推理、核心业务建模、安全合规等内容，为项目管理系统的工程实现提供了全链路建模支撑。
