# 服务业架构DSL草案

## 1. 概述

服务业架构DSL用于统一描述服务行业系统：服务目录、预约排班、工单派工、SLA监控、CRM与计费结算，适用于上门维修、保洁保养、咨询培训等。

## 2. 核心语法定义

### 2.1 服务目录与定价

```yaml
service_catalog:
  categories:
    - name: "maintenance"
      subcategories: ["hvac", "plumbing", "electrical", "appliance"]
    - name: "cleaning"
      subcategories: ["residential", "commercial", "deep_cleaning", "regular"]
    - name: "consulting"
      subcategories: ["business", "technical", "training", "audit"]
  offerings:
    - id: "svc_001"
      name: "AC Maintenance"
      category: "maintenance"
      subcategory: "hvac"
      duration_min: 90
      base_price: 79
      description: "Complete AC system inspection and maintenance"
      requirements:
        - "access_to_unit"
        - "power_available"
      parts_included: ["filter", "cleaning_supplies"]
    - id: "svc_010"
      name: "Home Cleaning"
      category: "cleaning"
      subcategory: "residential"
      duration_min: 120
      base_price: 99
      description: "Standard home cleaning service"
      requirements:
        - "vacant_home"
        - "supplies_provided"
  pricing_tiers:
    - name: "standard"
      markup: 0.0
    - name: "premium"
      markup: 0.25
      features: ["priority_scheduling", "guaranteed_satisfaction"]
    - name: "vip"
      markup: 0.50
      features: ["dedicated_technician", "same_day_service"]
```

### 2.2 预约与排班系统

```yaml
scheduling_system:
  resources:
    technicians:
      - id: "tech_001"
        name: "John Smith"
        skills: ["hvac", "electrical"]
        certifications: ["EPA", "HVAC_License"]
        shifts: ["Mon", "Wed", "Fri"]
        availability:
          - day: "Mon"; start: "08:00"; end: "17:00"
          - day: "Wed"; start: "08:00"; end: "17:00"
          - day: "Fri"; start: "08:00"; end: "17:00"
        max_daily_jobs: 6
        travel_radius_miles: 50
      - id: "tech_002"
        name: "Maria Garcia"
        skills: ["cleaning", "organization"]
        certifications: ["Cleaning_Cert"]
        shifts: ["Tue", "Thu", "Sat"]
        availability:
          - day: "Tue"; start: "09:00"; end: "18:00"
          - day: "Thu"; start: "09:00"; end: "18:00"
          - day: "Sat"; start: "08:00"; end: "16:00"
        max_daily_jobs: 4
        travel_radius_miles: 30
  booking:
    rules:
      - name: "skill_match"
        required: true
        description: "Technician must have required skills"
      - name: "max_daily_jobs"
        value: 6
        description: "Maximum jobs per technician per day"
      - name: "travel_distance"
        max_miles: 50
        description: "Maximum travel distance for technician"
    time_slots:
      start_time: "08:00"
      end_time: "20:00"
      interval_min: 30
      buffer_min: 15
  optimization:
    algorithm: "genetic_algorithm"
    objectives: ["minimize_travel", "maximize_utilization", "customer_satisfaction"]
    constraints: ["skill_match", "time_availability", "travel_distance"]
```

### 2.3 工单与派工管理

```yaml
work_order_management:
  status_flow:
    - status: "created"
      description: "Service request created"
      allowed_transitions: ["assigned", "cancelled"]
    - status: "assigned"
      description: "Technician assigned to job"
      allowed_transitions: ["en_route", "reassigned"]
    - status: "en_route"
      description: "Technician traveling to location"
      allowed_transitions: ["in_progress", "delayed"]
    - status: "in_progress"
      description: "Service work in progress"
      allowed_transitions: ["completed", "paused", "escalated"]
    - status: "completed"
      description: "Service work completed"
      allowed_transitions: ["closed", "follow_up"]
    - status: "closed"
      description: "Work order closed"
      allowed_transitions: []
  dispatch:
    strategy: "score_based"
    scoring:
      weights:
        distance: 0.4
        skill_fit: 0.3
        workload: 0.2
        customer_priority: 0.1
      factors:
        distance_formula: "1 / (1 + distance_miles)"
        skill_fit_formula: "matching_skills / total_required_skills"
        workload_formula: "1 - (current_jobs / max_daily_jobs)"
        priority_formula: "customer_tier_multiplier"
  work_orders:
    - id: "wo_001"
      customer: "cust_001"
      service: "svc_001"
      scheduled_time: "2025-03-15T10:00:00"
      location:
        address: "123 Main St, City, State"
        coordinates: [40.7128, -74.0060]
        access_notes: "Gate code: 1234"
      priority: "standard"
      estimated_duration: 90
      assigned_technician: "tech_001"
      status: "assigned"
      special_instructions: "Customer prefers afternoon appointments"
```

### 2.4 SLA监控与质量保证

```yaml
sla_quality_management:
  slas:
    - name: "on_time_arrival"
      target_pct: 95
      threshold_min: 15
      measurement: "arrival_time - scheduled_time"
      priority: "high"
    - name: "first_time_fix"
      target_pct: 85
      measurement: "issues_resolved_first_visit / total_issues"
      priority: "high"
    - name: "customer_satisfaction"
      target_score: 4.5
      measurement: "average_rating"
      priority: "medium"
    - name: "response_time"
      target_minutes: 30
      measurement: "assignment_time - creation_time"
      priority: "medium"
  quality_metrics:
    - name: "work_quality"
      measurement: "inspection_score"
      target: 90
      frequency: "per_job"
    - name: "customer_feedback"
      measurement: "nps_score"
      target: 75
      frequency: "monthly"
    - name: "repeat_business"
      measurement: "repeat_customer_rate"
      target: 80
      frequency: "quarterly"
  alerts:
    - name: "eta_risk"
      condition: "eta_delay > 10"
      actions: ["notify_customer", "reassign_if_possible"]
      priority: "high"
    - name: "sla_breach_risk"
      condition: "sla_compliance < 90"
      actions: ["notify_management", "review_processes"]
      priority: "medium"
    - name: "quality_issue"
      condition: "quality_score < 85"
      actions: ["retrain_technician", "review_standards"]
      priority: "high"
```

### 2.5 CRM与客户管理

```yaml
crm_customer_management:
  customer_segments:
    - name: "standard"
      criteria: ["new_customers", "basic_services"]
      service_level: "standard"
      response_time: "24_hours"
    - name: "vip"
      criteria: ["high_value", "loyal_customers"]
      service_level: "premium"
      response_time: "4_hours"
      features: ["priority_scheduling", "dedicated_account_manager"]
    - name: "b2b"
      criteria: ["business_customers", "contract_services"]
      service_level: "enterprise"
      response_time: "2_hours"
      features: ["custom_contracts", "volume_discounts"]
  customer_profiles:
    - id: "cust_001"
      name: "John Doe"
      email: "john.doe@email.com"
      phone: "555-123-4567"
      address: "123 Main St, City, State"
      segment: "vip"
      join_date: "2023-01-15"
      total_spent: 2500
      service_history:
        - service: "svc_001"
          date: "2024-12-15"
          rating: 5
          feedback: "Excellent service, very professional"
      preferences:
        - preferred_time: "afternoon"
        - preferred_technician: "tech_001"
        - communication_method: "email"
  nps_management:
    target_score: 75
    survey_frequency: "post_service"
    follow_up:
      promoters: "thank_you_email"
      passives: "improvement_survey"
      detractors: "immediate_callback"
```

### 2.6 计费与财务管理

```yaml
billing_financial_management:
  pricing_rules:
    - name: "weekend_surcharge"
      condition: "is_weekend"
      action:
        type: "percent"
        value: 10
        description: "10% surcharge for weekend service"
    - name: "vip_discount"
      condition: "segment == 'vip'"
      action:
        type: "percent"
        value: -15
        description: "15% discount for VIP customers"
    - name: "volume_discount"
      condition: "monthly_spend > 500"
      action:
        type: "percent"
        value: -5
        description: "5% discount for high volume customers"
    - name: "emergency_surcharge"
      condition: "service_type == 'emergency'"
      action:
        type: "fixed"
        value: 50
        description: "$50 emergency service fee"
  invoicing:
    terms: "net_15"
    tax_rate: 0.08
    late_fee_rate: 0.015
    payment_methods: ["credit_card", "bank_transfer", "check"]
    auto_billing: true
  invoices:
    - id: "inv_001"
      customer: "cust_001"
      work_order: "wo_001"
      amount: 86.90
      tax: 6.95
      total: 93.85
      due_date: "2025-03-30"
      status: "pending"
      line_items:
        - description: "AC Maintenance"
          quantity: 1
          unit_price: 79.00
          total: 79.00
        - description: "Weekend Surcharge"
          quantity: 1
          unit_price: 7.90
          total: 7.90
  revenue_analytics:
    metrics:
      - name: "monthly_revenue"
        calculation: "sum(invoice_total)"
        frequency: "monthly"
      - name: "average_ticket_size"
        calculation: "avg(invoice_total)"
        frequency: "weekly"
      - name: "customer_lifetime_value"
        calculation: "sum(customer_total_spent)"
        frequency: "quarterly"
```

### 2.7 库存与供应链管理

```yaml
inventory_supply_management:
  inventory:
    - item: "air_filter_16x20"
      sku: "AF-1620"
      category: "hvac_parts"
      current_stock: 45
      reorder_point: 20
      reorder_quantity: 50
      unit_cost: 12.50
      supplier: "supplier_001"
      lead_time_days: 3
    - item: "cleaning_supplies_kit"
      sku: "CS-KIT-01"
      category: "cleaning_supplies"
      current_stock: 30
      reorder_point: 15
      reorder_quantity: 25
      unit_cost: 25.00
      supplier: "supplier_002"
      lead_time_days: 5
  suppliers:
    - id: "supplier_001"
      name: "HVAC Parts Co"
      contact: "sales@hvacparts.com"
      payment_terms: "net_30"
      reliability_score: 0.95
    - id: "supplier_002"
      name: "Cleaning Supplies Inc"
      contact: "orders@cleaningsupplies.com"
      payment_terms: "net_30"
      reliability_score: 0.90
  procurement:
    auto_reorder: true
    approval_threshold: 1000
    preferred_suppliers: ["supplier_001", "supplier_002"]
```

## 3. 高级特性

```yaml
advanced_features:
  mobile_app:
    features: ["job_details", "time_tracking", "photo_documentation", "customer_signature"]
    offline_capability: true
    gps_tracking: true
  analytics:
    real_time_dashboard: true
    predictive_analytics: true
    customer_insights: true
    operational_efficiency: true
  integration:
    accounting_systems: ["QuickBooks", "Xero", "Sage"]
    crm_systems: ["Salesforce", "HubSpot", "Zoho"]
    payment_processors: ["Stripe", "Square", "PayPal"]
  automation:
    auto_scheduling: true
    smart_dispatch: true
    invoice_generation: true
    customer_communications: true
```

## 4. 自动化生成示例

```python
# 智能派工算法
def intelligent_dispatch(job, available_technicians):
    scores = []
    for tech in available_technicians:
        # 距离评分
        distance_score = 1 / (1 + calculate_distance(job.location, tech.current_location))
        
        # 技能匹配评分
        skill_match = len(set(job.required_skills) & set(tech.skills)) / len(job.required_skills)
        
        # 工作负载评分
        workload_score = 1 - (tech.current_jobs / tech.max_daily_jobs)
        
        # 客户优先级评分
        priority_score = get_customer_priority_multiplier(job.customer.segment)
        
        # 综合评分
        total_score = (
            0.4 * distance_score +
            0.3 * skill_match +
            0.2 * workload_score +
            0.1 * priority_score
        )
        
        scores.append((tech, total_score))
    
    # 返回评分最高的技师
    return max(scores, key=lambda x: x[1])[0]

# 动态定价算法
def dynamic_pricing(service, customer, time_slot):
    base_price = service.base_price
    
    # 时间因素
    if is_weekend(time_slot):
        base_price *= 1.1  # 周末加价10%
    elif is_peak_hour(time_slot):
        base_price *= 1.05  # 高峰时段加价5%
    
    # 客户等级因素
    if customer.segment == "vip":
        base_price *= 0.85  # VIP客户85折
    elif customer.segment == "b2b":
        base_price *= 0.90  # B2B客户9折
    
    # 需求因素
    demand_factor = get_current_demand(time_slot)
    if demand_factor > 0.8:  # 高需求时段
        base_price *= 1.15
    
    return round(base_price, 2)

# SLA监控与预警
def sla_monitoring():
    active_jobs = get_active_jobs()
    alerts = []
    
    for job in active_jobs:
        # 检查到达时间SLA
        if job.status == "en_route":
            eta_delay = calculate_eta_delay(job)
            if eta_delay > 10:  # 延迟超过10分钟
                alerts.append({
                    "type": "eta_risk",
                    "job_id": job.id,
                    "technician": job.assigned_technician,
                    "delay_minutes": eta_delay,
                    "actions": ["notify_customer", "reassign_if_possible"]
                })
        
        # 检查首次修复率
        if job.status == "completed":
            if not job.first_time_fix:
                alerts.append({
                    "type": "quality_issue",
                    "job_id": job.id,
                    "technician": job.assigned_technician,
                    "actions": ["retrain_technician", "review_standards"]
                })
    
    return alerts
```

## 5. 验证与测试

```python
class ServiceDSLValidator:
    def validate_service_catalog(self, catalog):
        assert 'categories' in catalog, "Service catalog must have categories"
        assert 'offerings' in catalog, "Service catalog must have offerings"
        for offering in catalog['offerings']:
            assert 'id' in offering, "Offering must have ID"
            assert 'name' in offering, "Offering must have name"
            assert 'base_price' in offering and offering['base_price'] > 0, "Invalid base price"
    
    def validate_scheduling(self, scheduling):
        assert 'resources' in scheduling, "Scheduling must define resources"
        assert 'booking' in scheduling, "Scheduling must define booking rules"
        for tech in scheduling['resources']['technicians']:
            assert 'skills' in tech, "Technician must have skills"
            assert 'availability' in tech, "Technician must have availability"
    
    def validate_work_orders(self, work_orders):
        assert 'status_flow' in work_orders, "Work orders must define status flow"
        assert 'dispatch' in work_orders, "Work orders must define dispatch strategy"
        for status in work_orders['status_flow']:
            assert 'status' in status, "Status must have name"
            assert 'allowed_transitions' in status, "Status must define allowed transitions"
    
    def validate_sla(self, sla_config):
        assert 'slas' in sla_config, "SLA config must define SLAs"
        for sla in sla_config['slas']:
            assert 'target_pct' in sla or 'target_score' in sla, "SLA must have target"
            assert 'measurement' in sla, "SLA must define measurement method"
    
    def validate_billing(self, billing):
        assert 'pricing_rules' in billing, "Billing must define pricing rules"
        assert 'invoicing' in billing, "Billing must define invoicing terms"
        for rule in billing['pricing_rules']:
            assert 'condition' in rule, "Pricing rule must have condition"
            assert 'action' in rule, "Pricing rule must have action"
```

## 6. 总结

本DSL覆盖服务行业的关键域模型与流程，包括服务目录管理、智能排班调度、工单派工优化、SLA监控预警、客户关系管理、计费财务管理等，可自动生成预约排班、派工策略、SLA监控与计费配置，支持服务行业的数字化转型和运营优化。
