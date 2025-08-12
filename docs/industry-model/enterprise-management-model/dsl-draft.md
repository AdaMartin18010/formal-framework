# 企业管理模型DSL草案

## 1. 概述

企业管理模型DSL用于统一描述企业管理系统：资产管理、CRM、HR管理、采购、项目管理等，支持与ERP、CRM、HRIS、SCM系统对接。

## 2. 核心语法定义

### 2.1 资产管理

```yaml
asset_management:
  asset_categories:
    - name: "equipment"
      depreciation_method: "straight_line"
      useful_life_years: 10
    - name: "buildings"
      depreciation_method: "straight_line"
      useful_life_years: 30
    - name: "vehicles"
      depreciation_method: "declining_balance"
      useful_life_years: 5
  
  assets:
    - id: "asset_001"
      name: "CNC Machine"
      category: "equipment"
      location: "Factory A"
      purchase_date: "2023-01-15"
      purchase_cost: 500000
      current_value: 450000
      status: "in_use"
      maintenance_schedule: "monthly"
      responsible_person: "eng_001"
      insurance:
        provider: "Insurance Co"
        policy_number: "POL-001"
        coverage_amount: 600000
        expiry_date: "2024-12-31"
```

### 2.2 CRM客户关系管理

```yaml
crm:
  customer_segments:
    - name: "enterprise"
      criteria: ["annual_revenue > 1000000", "employee_count > 100"]
      priority: "high"
    - name: "sme"
      criteria: ["annual_revenue < 1000000", "employee_count < 100"]
      priority: "medium"
    - name: "startup"
      criteria: ["founded_after 2020", "funding_round < B"]
      priority: "low"
  
  customers:
    - id: "cust_001"
      name: "ABC Corp"
      segment: "enterprise"
      contact_person: "John Doe"
      email: "john@abccorp.com"
      phone: "+1-555-0123"
      address: "123 Business St, City, State"
      annual_revenue: 5000000
      industry: "manufacturing"
      lead_source: "website"
      status: "active"
      tags: ["vip", "long_term"]
  
  sales_pipeline:
    stages:
      - name: "lead"; probability: 10
      - name: "qualified"; probability: 25
      - name: "proposal"; probability: 50
      - name: "negotiation"; probability: 75
      - name: "closed_won"; probability: 100
      - name: "closed_lost"; probability: 0
```

### 2.3 HR人力资源管理

```yaml
hr_management:
  departments:
    - name: "engineering"
      manager: "mgr_001"
      budget: 2000000
    - name: "sales"
      manager: "mgr_002"
      budget: 1500000
    - name: "marketing"
      manager: "mgr_003"
      budget: 800000
  
  employees:
    - id: "emp_001"
      name: "Alice Johnson"
      department: "engineering"
      position: "senior_engineer"
      hire_date: "2022-03-15"
      salary: 80000
      benefits: ["health_insurance", "401k", "stock_options"]
      performance_rating: 4.5
      skills: ["python", "machine_learning", "aws"]
      manager: "mgr_001"
  
  recruitment:
    positions:
      - title: "software_engineer"
        department: "engineering"
        requirements: ["bachelor_degree", "3_years_experience", "python"]
        salary_range: [70000, 90000]
        status: "open"
        applications: 15
        interviews_scheduled: 5
```

### 2.4 采购管理

```yaml
procurement:
  suppliers:
    - id: "supp_001"
      name: "Tech Supplies Inc"
      category: "electronics"
      rating: 4.2
      lead_time_days: 7
      payment_terms: "net_30"
      contact: "supplier@techsupplies.com"
      address: "456 Supply Ave, City, State"
  
  purchase_orders:
    - id: "po_001"
      supplier: "supp_001"
      items:
        - sku: "SKU-001"; qty: 100; unit_price: 25.50
        - sku: "SKU-002"; qty: 50; unit_price: 15.75
      total_amount: 3825.00
      status: "approved"
      delivery_date: "2024-02-15"
      approver: "mgr_001"
  
  contracts:
    - id: "contract_001"
      supplier: "supp_001"
      type: "service"
      start_date: "2024-01-01"
      end_date: "2024-12-31"
      value: 50000
      terms: "monthly_payment"
      auto_renewal: true
```

### 2.5 项目管理

```yaml
project_management:
  projects:
    - id: "proj_001"
      name: "ERP Implementation"
      description: "Implement new ERP system"
      start_date: "2024-01-01"
      end_date: "2024-06-30"
      budget: 500000
      status: "in_progress"
      priority: "high"
      manager: "pm_001"
      
      phases:
        - name: "planning"; duration_weeks: 4; status: "completed"
        - name: "development"; duration_weeks: 12; status: "in_progress"
        - name: "testing"; duration_weeks: 4; status: "not_started"
        - name: "deployment"; duration_weeks: 2; status: "not_started"
      
      resources:
        - employee: "emp_001"; role: "developer"; allocation_pct: 100
        - employee: "emp_002"; role: "tester"; allocation_pct: 50
      
      risks:
        - description: "Vendor delay"
          probability: "medium"
          impact: "high"
          mitigation: "Alternative vendor identified"
  
  methodologies:
    - name: "agile"
      ceremonies: ["daily_standup", "sprint_planning", "retrospective"]
      artifacts: ["product_backlog", "sprint_backlog", "burndown_chart"]
    - name: "waterfall"
      phases: ["requirements", "design", "implementation", "testing", "deployment"]
```

## 3. 自动化生成示例

```python
# 基于项目进度自动生成资源分配建议
def optimize_resource_allocation(projects, employees):
    # 使用线性规划优化资源分配
    from pulp import *
    
    prob = LpProblem("Resource_Allocation", LpMinimize)
    
    # 决策变量：员工i在项目j上的分配比例
    x = LpVariable.dicts("allocation",
                        [(i, j) for i in employees for j in projects],
                        lowBound=0, upBound=1)
    
    # 目标函数：最小化总成本
    prob += lpSum([x[i,j] * employees[i].cost * projects[j].duration 
                   for i in employees for j in projects])
    
    # 约束条件
    for i in employees:
        prob += lpSum([x[i,j] for j in projects]) <= 1  # 总分配不超过100%
    
    for j in projects:
        prob += lpSum([x[i,j] * employees[i].skills 
                      for i in employees]) >= projects[j].required_skills
    
    prob.solve()
    return x
```

## 4. 验证与测试

```python
class EnterpriseManagementValidator:
    def validate_asset(self, asset):
        assert asset["purchase_cost"] > 0, "purchase cost must be positive"
        assert asset["current_value"] >= 0, "current value cannot be negative"
    
    def validate_employee(self, employee):
        assert employee["salary"] > 0, "salary must be positive"
        assert employee["performance_rating"] >= 1 and employee["performance_rating"] <= 5
```

## 5. 总结

本DSL覆盖企业管理领域的核心业务模块，支持资产管理、CRM、HR管理、采购、项目管理的自动化配置生成，可与ERP、CRM、HRIS等企业系统无缝集成。
