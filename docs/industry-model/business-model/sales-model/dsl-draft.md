# 销售模型DSL草案

## 1. 概述

销售模型DSL用于统一描述销售管理系统：销售线索、客户管理、销售流程、报价管理、合同管理、销售预测等，支持与CRM、ERP、财务系统对接。

## 2. 核心语法定义

### 2.1 销售线索管理

```yaml
lead_management:
  lead_sources:
    - name: "website"
      description: "官网"
      conversion_rate: 0.15
      cost_per_lead: 50
    - name: "referral"
      description: "推荐"
      conversion_rate: 0.35
      cost_per_lead: 0
    - name: "cold_call"
      description: "冷电话"
      conversion_rate: 0.05
      cost_per_lead: 100
    - name: "trade_show"
      description: "展会"
      conversion_rate: 0.25
      cost_per_lead: 200
  lead_scoring:
    criteria:
      - name: "company_size"
        weight: 20
        values:
          "enterprise": 100
          "mid_market": 75
          "small_business": 50
          "startup": 25
      - name: "budget"
        weight: 25
        values:
          "high": 100
          "medium": 75
          "low": 50
          "unknown": 25
      - name: "decision_maker"
        weight: 30
        values:
          "yes": 100
          "no": 0
      - name: "timeline"
        weight: 25
        values:
          "immediate": 100
          "3_months": 75
          "6_months": 50
          "12_months": 25
  leads:
    - id: "lead_001"
      company: "ABC Corp"
      contact:
        name: "John Smith"
        title: "CTO"
        email: "john.smith@abccorp.com"
        phone: "+1-555-123-4567"
      source: "website"
      score: 85
      status: "qualified"
      created_date: "2025-01-15"
      assigned_to: "sales_rep_001"
      notes: "Interested in enterprise solution"
```

### 2.2 客户管理

```yaml
customer_management:
  customer_segments:
    - name: "enterprise"
      description: "大型企业"
      criteria:
        - "annual_revenue > 1000000000"
        - "employee_count > 1000"
      sales_cycle_days: 90
      average_deal_size: 500000
    - name: "mid_market"
      description: "中型企业"
      criteria:
        - "annual_revenue between 10000000 and 1000000000"
        - "employee_count between 100 and 1000"
      sales_cycle_days: 60
      average_deal_size: 100000
    - name: "small_business"
      description: "小型企业"
      criteria:
        - "annual_revenue < 10000000"
        - "employee_count < 100"
      sales_cycle_days: 30
      average_deal_size: 25000
  customers:
    - id: "cust_001"
      name: "ABC Corporation"
      segment: "enterprise"
      industry: "technology"
      annual_revenue: 2000000000
      employee_count: 5000
      address:
        street: "123 Business Ave"
        city: "San Francisco"
        state: "CA"
        zip: "94105"
        country: "USA"
      contacts:
        - name: "John Smith"
          title: "CTO"
          email: "john.smith@abccorp.com"
          phone: "+1-555-123-4567"
          is_primary: true
        - name: "Jane Doe"
          title: "Procurement Manager"
          email: "jane.doe@abccorp.com"
          phone: "+1-555-123-4568"
          is_primary: false
      status: "active"
      created_date: "2024-01-15"
      total_revenue: 1500000
      last_purchase_date: "2024-12-15"
```

### 2.3 销售流程管理

```yaml
sales_process_management:
  sales_stages:
    - name: "prospecting"
      description: "潜在客户开发"
      probability: 10
      duration_days: 30
      activities:
        - "lead_research"
        - "initial_contact"
        - "qualification_call"
    - name: "qualification"
      description: "客户资格确认"
      probability: 25
      duration_days: 15
      activities:
        - "needs_assessment"
        - "budget_verification"
        - "decision_maker_identification"
    - name: "proposal"
      description: "方案制定"
      probability: 50
      duration_days: 20
      activities:
        - "solution_design"
        - "proposal_creation"
        - "presentation_preparation"
    - name: "negotiation"
      description: "商务谈判"
      probability: 75
      duration_days: 15
      activities:
        - "price_negotiation"
        - "terms_discussion"
        - "objection_handling"
    - name: "closed_won"
      description: "成交"
      probability: 100
      duration_days: 5
      activities:
        - "contract_signing"
        - "payment_processing"
        - "handoff_to_implementation"
    - name: "closed_lost"
      description: "失败"
      probability: 0
      duration_days: 0
      activities:
        - "loss_analysis"
        - "follow_up_planning"
  opportunities:
    - id: "opp_001"
      customer: "cust_001"
      name: "Enterprise Software License"
      stage: "negotiation"
      probability: 75
      expected_close_date: "2025-03-15"
      amount: 500000
      currency: "USD"
      assigned_to: "sales_rep_001"
      created_date: "2024-12-01"
      last_activity: "2025-01-15"
      activities:
        - date: "2025-01-15"
          type: "meeting"
          description: "Final presentation to CTO"
          outcome: "positive_feedback"
        - date: "2025-01-10"
          type: "proposal_sent"
          description: "Detailed proposal delivered"
          outcome: "proposal_reviewed"
```

### 2.4 报价管理

```yaml
quote_management:
  quote_templates:
    - name: "enterprise_software"
      description: "企业软件许可报价模板"
      validity_days: 30
      components:
        - name: "software_license"
          type: "perpetual"
          pricing_model: "per_user"
          base_price: 1000
          volume_discounts:
            - threshold: 100
              discount: 0.10
            - threshold: 500
              discount: 0.20
            - threshold: 1000
              discount: 0.30
        - name: "implementation_services"
          type: "professional_services"
          pricing_model: "fixed_price"
          base_price: 50000
        - name: "annual_maintenance"
          type: "subscription"
          pricing_model: "percentage_of_license"
          base_price: 0.20
  quotes:
    - id: "quote_001"
      customer: "cust_001"
      opportunity: "opp_001"
      template: "enterprise_software"
      created_date: "2025-01-10"
      valid_until: "2025-02-09"
      status: "sent"
      line_items:
        - component: "software_license"
          quantity: 500
          unit_price: 700
          discount: 0.30
          total: 245000
        - component: "implementation_services"
          quantity: 1
          unit_price: 50000
          discount: 0.10
          total: 45000
        - component: "annual_maintenance"
          quantity: 1
          unit_price: 49000
          discount: 0.00
          total: 49000
      subtotal: 339000
      tax_rate: 0.08
      tax_amount: 27120
      total: 366120
      terms:
        payment_terms: "net_30"
        delivery_terms: "fob_destination"
        warranty: "1_year"
```

### 2.5 合同管理

```yaml
contract_management:
  contract_templates:
    - name: "software_license_agreement"
      description: "软件许可协议模板"
      sections:
        - name: "license_grant"
          content: "template_license_grant"
          required: true
        - name: "payment_terms"
          content: "template_payment_terms"
          required: true
        - name: "warranty"
          content: "template_warranty"
          required: true
        - name: "limitation_of_liability"
          content: "template_liability"
          required: true
  contracts:
    - id: "contract_001"
      customer: "cust_001"
      opportunity: "opp_001"
      quote: "quote_001"
      template: "software_license_agreement"
      status: "draft"
      created_date: "2025-01-15"
      effective_date: "2025-03-01"
      expiration_date: "2030-03-01"
      total_value: 366120
      currency: "USD"
      terms:
        payment_schedule:
          - amount: 183060
            due_date: "2025-03-01"
            description: "50% upon signing"
          - amount: 183060
            due_date: "2025-06-01"
            description: "50% upon delivery"
        deliverables:
          - name: "Software License"
            due_date: "2025-03-15"
            description: "Software license keys and documentation"
          - name: "Implementation Services"
            due_date: "2025-05-15"
            description: "Complete system implementation"
        milestones:
          - name: "Contract Signing"
            date: "2025-03-01"
            status: "pending"
          - name: "Software Delivery"
            date: "2025-03-15"
            status: "pending"
          - name: "Implementation Complete"
            date: "2025-05-15"
            status: "pending"
          - name: "Final Payment"
            date: "2025-06-01"
            status: "pending"
```

### 2.6 销售预测

```yaml
sales_forecasting:
  forecast_models:
    - name: "pipeline_forecast"
      description: "基于销售管道的预测"
      method: "weighted_probability"
      factors:
        - name: "stage_probability"
          weight: 0.6
        - name: "historical_conversion"
          weight: 0.3
        - name: "seasonal_adjustment"
          weight: 0.1
      update_frequency: "weekly"
    - name: "trend_forecast"
      description: "基于历史趋势的预测"
      method: "time_series"
      algorithm: "arima"
      parameters:
        p: 1
        d: 1
        q: 1
      forecast_horizon: 12
      update_frequency: "monthly"
  forecasts:
    - id: "forecast_001"
      period: "Q1_2025"
      model: "pipeline_forecast"
      created_date: "2025-01-15"
      total_forecast: 2500000
      breakdown:
        - stage: "prospecting"
          amount: 500000
          probability: 0.10
        - stage: "qualification"
          amount: 750000
          probability: 0.25
        - stage: "proposal"
          amount: 1000000
          probability: 0.50
        - stage: "negotiation"
          amount: 250000
          probability: 0.75
      confidence_interval:
        low: 2000000
        high: 3000000
  sales_targets:
    - id: "target_001"
      period: "Q1_2025"
      total_target: 3000000
      breakdown:
        - sales_rep: "sales_rep_001"
          target: 1000000
        - sales_rep: "sales_rep_002"
          target: 800000
        - sales_rep: "sales_rep_003"
          target: 1200000
      kpis:
        - name: "quota_achievement"
          target: 100
          calculation: "actual_sales / target_sales * 100"
        - name: "pipeline_velocity"
          target: 30
          calculation: "avg_days_in_pipeline"
        - name: "win_rate"
          target: 25
          calculation: "closed_won / total_opportunities * 100"
```

### 2.7 销售活动管理

```yaml
sales_activity_management:
  activity_types:
    - name: "call"
      description: "电话沟通"
      duration_minutes: 30
      required_fields: ["contact", "outcome", "next_steps"]
    - name: "meeting"
      description: "会议"
      duration_minutes: 60
      required_fields: ["attendees", "agenda", "outcome", "next_steps"]
    - name: "email"
      description: "邮件沟通"
      required_fields: ["recipient", "subject", "content", "outcome"]
    - name: "presentation"
      description: "产品演示"
      duration_minutes: 90
      required_fields: ["audience", "demo_scope", "feedback", "next_steps"]
  activities:
    - id: "activity_001"
      type: "meeting"
      customer: "cust_001"
      opportunity: "opp_001"
      assigned_to: "sales_rep_001"
      scheduled_date: "2025-01-20T10:00:00"
      duration_minutes: 60
      attendees:
        - name: "John Smith"
          title: "CTO"
          email: "john.smith@abccorp.com"
        - name: "Jane Doe"
          title: "Procurement Manager"
          email: "jane.doe@abccorp.com"
      agenda: "Final contract discussion and pricing negotiation"
      location: "ABC Corp Headquarters"
      status: "scheduled"
      notes: "Prepare final proposal with updated pricing"
  follow_up_system:
    - name: "quote_follow_up"
      trigger: "quote_sent"
      delay_days: 3
      action: "send_follow_up_email"
      template: "quote_follow_up_template"
    - name: "proposal_follow_up"
      trigger: "proposal_sent"
      delay_days: 7
      action: "schedule_follow_up_call"
      template: "proposal_follow_up_template"
    - name: "contract_follow_up"
      trigger: "contract_sent"
      delay_days: 5
      action: "schedule_contract_review"
      template: "contract_follow_up_template"
```

## 3. 高级特性

```yaml
advanced_features:
  sales_analytics:
    real_time_dashboard: true
    pipeline_analytics: true
    performance_tracking: true
    predictive_analytics: true
  automation:
    lead_scoring: true
    quote_generation: true
    follow_up_scheduling: true
    contract_generation: true
  integration:
    crm_systems: ["Salesforce", "HubSpot", "Pipedrive"]
    erp_systems: ["SAP", "Oracle", "NetSuite"]
    accounting_systems: ["QuickBooks", "Xero"]
    communication_tools: ["Outlook", "Gmail", "Slack"]
  ai_assistance:
    lead_qualification: true
    opportunity_scoring: true
    next_best_action: true
    sales_coaching: true
```

## 4. 自动化生成示例

```python
# 智能销售线索评分
def intelligent_lead_scoring(lead_data):
    score = 0
    
    # 公司规模评分
    company_size_scores = {
        'enterprise': 100,
        'mid_market': 75,
        'small_business': 50,
        'startup': 25
    }
    score += company_size_scores.get(lead_data['company_size'], 0) * 0.2
    
    # 预算评分
    budget_scores = {
        'high': 100,
        'medium': 75,
        'low': 50,
        'unknown': 25
    }
    score += budget_scores.get(lead_data['budget'], 0) * 0.25
    
    # 决策者评分
    if lead_data['is_decision_maker']:
        score += 100 * 0.3
    else:
        score += 0 * 0.3
    
    # 时间线评分
    timeline_scores = {
        'immediate': 100,
        '3_months': 75,
        '6_months': 50,
        '12_months': 25
    }
    score += timeline_scores.get(lead_data['timeline'], 0) * 0.25
    
    return round(score)

# 销售预测算法
def sales_forecast(opportunities, historical_data):
    forecast = 0
    
    for opp in opportunities:
        # 基于阶段的概率加权
        stage_probabilities = {
            'prospecting': 0.10,
            'qualification': 0.25,
            'proposal': 0.50,
            'negotiation': 0.75,
            'closed_won': 1.00,
            'closed_lost': 0.00
        }
        
        probability = stage_probabilities.get(opp['stage'], 0)
        
        # 历史转换率调整
        historical_conversion = get_historical_conversion_rate(opp['stage'])
        adjusted_probability = (probability + historical_conversion) / 2
        
        # 季节性调整
        seasonal_factor = get_seasonal_factor(opp['expected_close_date'])
        
        forecast += opp['amount'] * adjusted_probability * seasonal_factor
    
    return round(forecast, 2)

# 智能报价生成
def generate_quote(opportunity, customer, products):
    quote = {
        'customer': customer['id'],
        'opportunity': opportunity['id'],
        'line_items': [],
        'subtotal': 0,
        'discount': 0,
        'total': 0
    }
    
    for product in products:
        # 基础价格
        base_price = product['base_price']
        
        # 客户等级折扣
        customer_discount = get_customer_discount(customer['segment'])
        
        # 数量折扣
        quantity_discount = get_quantity_discount(product['quantity'])
        
        # 总折扣
        total_discount = min(customer_discount + quantity_discount, 0.5)
        
        # 最终价格
        final_price = base_price * (1 - total_discount)
        
        line_item = {
            'product': product['id'],
            'quantity': product['quantity'],
            'unit_price': base_price,
            'discount': total_discount,
            'total': final_price * product['quantity']
        }
        
        quote['line_items'].append(line_item)
        quote['subtotal'] += line_item['total']
    
    # 应用整体折扣
    quote['discount'] = get_overall_discount(quote['subtotal'])
    quote['total'] = quote['subtotal'] * (1 - quote['discount'])
    
    return quote
```

## 5. 验证与测试

```python
class SalesDSLValidator:
    def validate_lead(self, lead):
        assert 'company' in lead, "Lead must have company name"
        assert 'contact' in lead, "Lead must have contact information"
        assert 'source' in lead, "Lead must specify source"
        assert 0 <= lead['score'] <= 100, "Lead score must be between 0-100"
    
    def validate_opportunity(self, opportunity):
        assert 'customer' in opportunity, "Opportunity must have customer"
        assert 'stage' in opportunity, "Opportunity must specify stage"
        assert 'amount' in opportunity and opportunity['amount'] > 0, "Invalid opportunity amount"
        assert 0 <= opportunity['probability'] <= 100, "Probability must be 0-100"
    
    def validate_quote(self, quote):
        assert 'customer' in quote, "Quote must have customer"
        assert 'line_items' in quote, "Quote must have line items"
        assert len(quote['line_items']) > 0, "Quote must have at least one line item"
        assert quote['total'] > 0, "Quote total must be positive"
    
    def validate_contract(self, contract):
        assert 'customer' in contract, "Contract must have customer"
        assert 'total_value' in contract, "Contract must specify total value"
        assert contract['total_value'] > 0, "Contract value must be positive"
        assert 'effective_date' in contract, "Contract must have effective date"
        assert 'expiration_date' in contract, "Contract must have expiration date"
    
    def validate_forecast(self, forecast):
        assert 'period' in forecast, "Forecast must specify period"
        assert 'total_forecast' in forecast, "Forecast must specify total amount"
        assert forecast['total_forecast'] >= 0, "Forecast amount must be non-negative"
        assert 'breakdown' in forecast, "Forecast must have breakdown"
```

## 6. 总结

本DSL覆盖销售管理的核心业务流程，包括销售线索管理、客户关系管理、销售流程控制、报价合同管理、销售预测分析等，支持销售流程的自动化配置和智能化管理，可与CRM、ERP等系统无缝集成，提升销售效率和业绩。
