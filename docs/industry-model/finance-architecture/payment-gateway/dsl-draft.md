# 支付网关DSL草案

## 1. 概述

支付网关DSL用于统一描述支付网关系统：支付渠道、交易处理、风控规则、结算清算、对账核销等，支持与支付宝、微信支付、银联、Visa、Mastercard等主流支付渠道对接。

## 2. 核心语法定义

### 2.1 支付渠道配置

```yaml
payment_channels:
  domestic_channels:
    - name: "alipay"
      provider: "支付宝"
      type: "mobile_payment"
      version: "2.0"
      configuration:
        app_id: "${ALIPAY_APP_ID}"
        private_key: "${ALIPAY_PRIVATE_KEY}"
        public_key: "${ALIPAY_PUBLIC_KEY}"
        gateway_url: "https://openapi.alipay.com/gateway.do"
        notify_url: "https://api.company.com/payment/notify/alipay"
        return_url: "https://www.company.com/payment/return"
        sign_type: "RSA2"
        charset: "utf-8"
        format: "json"
        version: "1.0"
      supported_methods:
        - "APP"
        - "WAP"
        - "WEB"
        - "QR_CODE"
        - "BAR_CODE"
      transaction_limits:
        min_amount: 0.01
        max_amount: 50000
        daily_limit: 100000
        monthly_limit: 1000000
    - name: "wechat_pay"
      provider: "微信支付"
      type: "mobile_payment"
      version: "v3"
      configuration:
        app_id: "${WECHAT_APP_ID}"
        mch_id: "${WECHAT_MCH_ID}"
        api_key: "${WECHAT_API_KEY}"
        cert_path: "/path/to/wechat_cert.pem"
        key_path: "/path/to/wechat_key.pem"
        notify_url: "https://api.company.com/payment/notify/wechat"
        return_url: "https://www.company.com/payment/return"
        sign_type: "HMAC-SHA256"
      supported_methods:
        - "JSAPI"
        - "NATIVE"
        - "APP"
        - "H5"
        - "MICROPAY"
      transaction_limits:
        min_amount: 0.01
        max_amount: 50000
        daily_limit: 100000
        monthly_limit: 1000000
  international_channels:
    - name: "visa"
      provider: "Visa"
      type: "credit_card"
      version: "3.0"
      configuration:
        merchant_id: "${VISA_MERCHANT_ID}"
        api_key: "${VISA_API_KEY}"
        secret_key: "${VISA_SECRET_KEY}"
        gateway_url: "https://api.visa.com/cybersource/payments/v1"
        webhook_url: "https://api.company.com/payment/webhook/visa"
        currency: "USD"
        country_code: "US"
      supported_methods:
        - "AUTHORIZATION"
        - "CAPTURE"
        - "REFUND"
        - "VOID"
      transaction_limits:
        min_amount: 1.00
        max_amount: 100000
        daily_limit: 500000
        monthly_limit: 5000000
    - name: "mastercard"
      provider: "Mastercard"
      type: "credit_card"
      version: "3.0"
      configuration:
        merchant_id: "${MASTERCARD_MERCHANT_ID}"
        api_key: "${MASTERCARD_API_KEY}"
        secret_key: "${MASTERCARD_SECRET_KEY}"
        gateway_url: "https://api.mastercard.com/payments/v1"
        webhook_url: "https://api.company.com/payment/webhook/mastercard"
        currency: "USD"
        country_code: "US"
      supported_methods:
        - "AUTHORIZATION"
        - "CAPTURE"
        - "REFUND"
        - "VOID"
      transaction_limits:
        min_amount: 1.00
        max_amount: 100000
        daily_limit: 500000
        monthly_limit: 5000000
```

### 2.2 交易处理流程

```yaml
transaction_processing:
  payment_flows:
    - name: "standard_payment"
      description: "标准支付流程"
      steps:
        - name: "payment_initiation"
          description: "支付发起"
          action: "create_payment_order"
          required_fields:
            - "merchant_id"
            - "order_id"
            - "amount"
            - "currency"
            - "payment_method"
            - "customer_info"
          validation:
            - "amount_range_check"
            - "currency_support_check"
            - "merchant_validation"
        - name: "risk_assessment"
          description: "风险评估"
          action: "risk_check"
          rules:
            - name: "fraud_detection"
              type: "ml_model"
              model: "fraud_detection_v2"
              threshold: 0.8
            - name: "velocity_check"
              type: "rule_based"
              rules:
                - "transaction_count_per_hour <= 10"
                - "transaction_amount_per_day <= 10000"
            - name: "location_check"
              type: "rule_based"
              rules:
                - "ip_country = card_country"
                - "distance_from_last_transaction <= 100km"
        - name: "payment_processing"
          description: "支付处理"
          action: "process_payment"
          channels:
            - "alipay"
            - "wechat_pay"
            - "visa"
            - "mastercard"
          timeout: 30
          retry_count: 3
        - name: "result_handling"
          description: "结果处理"
          action: "handle_payment_result"
          success_actions:
            - "update_order_status"
            - "send_confirmation_email"
            - "trigger_fulfillment"
          failure_actions:
            - "update_order_status"
            - "send_failure_notification"
            - "trigger_refund_if_needed"
    - name: "subscription_payment"
      description: "订阅支付流程"
      steps:
        - name: "subscription_setup"
          description: "订阅设置"
          action: "create_subscription"
          required_fields:
            - "customer_id"
            - "plan_id"
            - "payment_method_id"
            - "billing_cycle"
        - name: "recurring_payment"
          description: "定期支付"
          action: "process_recurring_payment"
          schedule: "monthly"
          retry_policy:
            max_attempts: 3
            retry_interval: "1 day"
        - name: "subscription_management"
          description: "订阅管理"
          actions:
            - "pause_subscription"
            - "resume_subscription"
            - "cancel_subscription"
            - "update_payment_method"
  transaction_states:
    - name: "pending"
      description: "待处理"
      next_states: ["processing", "failed", "cancelled"]
      actions: ["cancel"]
    - name: "processing"
      description: "处理中"
      next_states: ["success", "failed"]
      actions: ["timeout"]
    - name: "success"
      description: "成功"
      next_states: ["refunded"]
      actions: ["refund"]
    - name: "failed"
      description: "失败"
      next_states: ["retry", "cancelled"]
      actions: ["retry", "cancel"]
    - name: "refunded"
      description: "已退款"
      next_states: []
      actions: []
    - name: "cancelled"
      description: "已取消"
      next_states: []
      actions: []
```

### 2.3 风控规则配置

```yaml
risk_management:
  fraud_detection:
    - name: "transaction_velocity"
      description: "交易频率检测"
      type: "rule_based"
      rules:
        - name: "high_frequency_transactions"
          condition: "transaction_count_per_hour > 10"
          action: "flag_for_review"
          severity: "medium"
        - name: "unusual_amount_pattern"
          condition: "amount > avg_amount * 3"
          action: "require_verification"
          severity: "high"
        - name: "rapid_successive_transactions"
          condition: "time_between_transactions < 60 seconds"
          action: "block_transaction"
          severity: "high"
    - name: "location_anomaly"
      description: "地理位置异常检测"
      type: "rule_based"
      rules:
        - name: "cross_country_transaction"
          condition: "ip_country != card_country"
          action: "require_verification"
          severity: "medium"
        - name: "unusual_location"
          condition: "distance_from_last_transaction > 1000km"
          action: "flag_for_review"
          severity: "high"
    - name: "device_fingerprinting"
      description: "设备指纹检测"
      type: "ml_based"
      model: "device_risk_model"
      features:
        - "device_id"
        - "browser_fingerprint"
        - "ip_address"
        - "user_agent"
      threshold: 0.7
      action: "block_if_high_risk"
  risk_scoring:
    - name: "transaction_risk_score"
      description: "交易风险评分"
      algorithm: "weighted_sum"
      factors:
        - name: "amount_risk"
          weight: 0.3
          calculation: "amount / max_amount"
        - name: "velocity_risk"
          weight: 0.25
          calculation: "transaction_count_per_hour / 10"
        - name: "location_risk"
          weight: 0.2
          calculation: "distance_from_last_transaction / 1000"
        - name: "device_risk"
          weight: 0.15
          calculation: "device_risk_score"
        - name: "customer_risk"
          weight: 0.1
          calculation: "customer_risk_score"
      thresholds:
        low_risk: 0.3
        medium_risk: 0.6
        high_risk: 0.8
  risk_actions:
    - name: "auto_approve"
      description: "自动批准"
      conditions: ["risk_score < 0.3"]
      action: "approve_transaction"
    - name: "manual_review"
      description: "人工审核"
      conditions: ["0.3 <= risk_score < 0.8"]
      action: "flag_for_manual_review"
    - name: "block_transaction"
      description: "阻止交易"
      conditions: ["risk_score >= 0.8"]
      action: "reject_transaction"
```

### 2.4 结算清算配置

```yaml
settlement_clearing:
  settlement_schedules:
    - name: "daily_settlement"
      description: "日结算"
      frequency: "daily"
      time: "23:00"
      timezone: "Asia/Shanghai"
      channels:
        - "alipay"
        - "wechat_pay"
      process:
        - "calculate_settlement_amount"
        - "generate_settlement_file"
        - "send_to_bank"
        - "update_settlement_status"
    - name: "weekly_settlement"
      description: "周结算"
      frequency: "weekly"
      day: "sunday"
      time: "23:00"
      timezone: "Asia/Shanghai"
      channels:
        - "visa"
        - "mastercard"
      process:
        - "calculate_settlement_amount"
        - "generate_settlement_file"
        - "send_to_bank"
        - "update_settlement_status"
  clearing_rules:
    - name: "t1_settlement"
      description: "T+1结算"
      channels: ["alipay", "wechat_pay"]
      settlement_delay: 1
      currency: "CNY"
    - name: "t3_settlement"
      description: "T+3结算"
      channels: ["visa", "mastercard"]
      settlement_delay: 3
      currency: "USD"
  settlement_fees:
    - name: "alipay_fees"
      channel: "alipay"
      fee_structure:
        - range: [0, 1000]
          rate: 0.006
          min_fee: 0.1
        - range: [1000, 10000]
          rate: 0.005
          min_fee: 6.0
        - range: [10000, 100000]
          rate: 0.004
          min_fee: 50.0
    - name: "wechat_fees"
      channel: "wechat_pay"
      fee_structure:
        - range: [0, 1000]
          rate: 0.006
          min_fee: 0.1
        - range: [1000, 10000]
          rate: 0.005
          min_fee: 6.0
        - range: [10000, 100000]
          rate: 0.004
          min_fee: 50.0
```

### 2.5 对账核销配置

```yaml
reconciliation:
  reconciliation_rules:
    - name: "daily_reconciliation"
      description: "日对账"
      frequency: "daily"
      time: "02:00"
      timezone: "Asia/Shanghai"
      process:
        - name: "download_settlement_files"
          description: "下载结算文件"
          sources:
            - "alipay_settlement_file"
            - "wechat_settlement_file"
            - "bank_settlement_file"
        - name: "match_transactions"
          description: "匹配交易"
          matching_rules:
            - "transaction_id_match"
            - "amount_match"
            - "date_match"
        - name: "identify_discrepancies"
          description: "识别差异"
          discrepancy_types:
            - "missing_transaction"
            - "amount_mismatch"
            - "duplicate_transaction"
            - "status_mismatch"
        - name: "generate_reconciliation_report"
          description: "生成对账报告"
          report_format: "excel"
          recipients: ["finance_team@company.com"]
    - name: "monthly_reconciliation"
      description: "月对账"
      frequency: "monthly"
      day: "first"
      time: "02:00"
      timezone: "Asia/Shanghai"
      process:
        - "comprehensive_reconciliation"
        - "generate_monthly_report"
        - "resolve_outstanding_issues"
  reconciliation_matching:
    - name: "transaction_id_match"
      description: "交易ID匹配"
      primary_key: "transaction_id"
      tolerance: "exact"
    - name: "amount_match"
      description: "金额匹配"
      field: "amount"
      tolerance: 0.01
      currency: "CNY"
    - name: "date_match"
      description: "日期匹配"
      field: "transaction_date"
      tolerance: "1 day"
      format: "YYYY-MM-DD"
  discrepancy_handling:
    - name: "missing_transaction"
      description: "缺失交易"
      action: "investigate"
      escalation: "manual_review"
      sla: "24 hours"
    - name: "amount_mismatch"
      description: "金额不匹配"
      action: "investigate"
      escalation: "manual_review"
      sla: "24 hours"
    - name: "duplicate_transaction"
      description: "重复交易"
      action: "deduplicate"
      escalation: "automatic"
      sla: "1 hour"
    - name: "status_mismatch"
      description: "状态不匹配"
      action: "investigate"
      escalation: "manual_review"
      sla: "24 hours"
```

### 2.6 通知回调配置

```yaml
notification_callbacks:
  webhook_configurations:
    - name: "payment_success_webhook"
      description: "支付成功回调"
      trigger: "payment_success"
      url: "https://api.company.com/payment/webhook/success"
      method: "POST"
      headers:
        - name: "Content-Type"
          value: "application/json"
        - name: "X-Signature"
          value: "${WEBHOOK_SIGNATURE}"
      retry_policy:
        max_attempts: 5
        retry_interval: "5 minutes"
        backoff_multiplier: 2
      timeout: 30
      security:
        signature_algorithm: "HMAC-SHA256"
        signature_key: "${WEBHOOK_SECRET}"
    - name: "payment_failure_webhook"
      description: "支付失败回调"
      trigger: "payment_failure"
      url: "https://api.company.com/payment/webhook/failure"
      method: "POST"
      headers:
        - name: "Content-Type"
          value: "application/json"
        - name: "X-Signature"
          value: "${WEBHOOK_SIGNATURE}"
      retry_policy:
        max_attempts: 3
        retry_interval: "10 minutes"
        backoff_multiplier: 2
      timeout: 30
      security:
        signature_algorithm: "HMAC-SHA256"
        signature_key: "${WEBHOOK_SECRET}"
  notification_templates:
    - name: "payment_success_email"
      description: "支付成功邮件模板"
      type: "email"
      template_id: "payment_success_template"
      variables:
        - "customer_name"
        - "order_id"
        - "amount"
        - "payment_method"
        - "transaction_id"
        - "payment_date"
      recipients:
        - "customer_email"
        - "merchant_email"
    - name: "payment_failure_email"
      description: "支付失败邮件模板"
      type: "email"
      template_id: "payment_failure_template"
      variables:
        - "customer_name"
        - "order_id"
        - "amount"
        - "payment_method"
        - "failure_reason"
        - "retry_link"
      recipients:
        - "customer_email"
        - "merchant_email"
  real_time_notifications:
    - name: "payment_status_sms"
      description: "支付状态短信通知"
      type: "sms"
      provider: "aliyun_sms"
      template_code: "SMS_PAYMENT_STATUS"
      variables:
        - "order_id"
        - "status"
        - "amount"
      recipients:
        - "customer_phone"
```

### 2.7 监控告警配置

```yaml
monitoring_alerting:
  performance_monitoring:
    - name: "transaction_throughput"
      description: "交易吞吐量监控"
      metric: "transactions_per_second"
      threshold: 100
      window: "5 minutes"
      alert: "high_throughput_alert"
    - name: "response_time"
      description: "响应时间监控"
      metric: "average_response_time"
      threshold: 2000
      unit: "milliseconds"
      window: "5 minutes"
      alert: "high_response_time_alert"
    - name: "error_rate"
      description: "错误率监控"
      metric: "error_rate"
      threshold: 0.05
      window: "5 minutes"
      alert: "high_error_rate_alert"
  business_monitoring:
    - name: "payment_success_rate"
      description: "支付成功率监控"
      metric: "payment_success_rate"
      threshold: 0.95
      window: "1 hour"
      alert: "low_success_rate_alert"
    - name: "revenue_monitoring"
      description: "收入监控"
      metric: "total_revenue"
      threshold: 100000
      window: "1 hour"
      alert: "revenue_alert"
    - name: "fraud_rate"
      description: "欺诈率监控"
      metric: "fraud_rate"
      threshold: 0.01
      window: "1 hour"
      alert: "high_fraud_rate_alert"
  alert_channels:
    - name: "email_alerts"
      description: "邮件告警"
      type: "email"
      recipients:
        - "payment_team@company.com"
        - "ops_team@company.com"
      template: "alert_email_template"
    - name: "slack_alerts"
      description: "Slack告警"
      type: "slack"
      channel: "#payment-alerts"
      webhook_url: "https://hooks.slack.com/services/xxx/yyy/zzz"
    - name: "sms_alerts"
      description: "短信告警"
      type: "sms"
      recipients:
        - "+8613800138000"
        - "+8613900139000"
      provider: "aliyun_sms"
```

## 3. 高级特性

```yaml
advanced_features:
  artificial_intelligence:
    fraud_detection_ml: true
    risk_scoring_ai: true
    customer_behavior_analysis: true
    predictive_analytics: true
  automation:
    auto_settlement: true
    auto_reconciliation: true
    smart_routing: true
    dynamic_pricing: true
  security:
    tokenization: true
    encryption_at_rest: true
    encryption_in_transit: true
    pci_compliance: true
  integration:
    erp_systems: ["SAP", "Oracle", "NetSuite"]
    accounting_systems: ["QuickBooks", "Xero", "FreshBooks"]
    ecommerce_platforms: ["Shopify", "Magento", "WooCommerce"]
    banking_apis: ["Open Banking", "Plaid", "Yodlee"]
```

## 4. 自动化生成示例

```python
# 支付网关配置自动化
def configure_payment_gateway(gateway_config, platform_config):
    """根据配置自动配置支付网关"""
    
    # 配置支付渠道
    for channel in gateway_config['payment_channels']:
        configure_payment_channel(channel, platform_config)
    
    # 配置风控规则
    for risk_rule in gateway_config['risk_management']:
        configure_risk_rule(risk_rule, platform_config)
    
    # 配置结算规则
    for settlement_rule in gateway_config['settlement_clearing']:
        configure_settlement_rule(settlement_rule, platform_config)
    
    # 配置对账规则
    for reconciliation_rule in gateway_config['reconciliation']:
        configure_reconciliation_rule(reconciliation_rule, platform_config)
    
    return "Payment gateway configured successfully"

def configure_payment_channel(channel_config, platform_config):
    """配置支付渠道"""
    
    # 创建渠道连接
    connection = create_channel_connection(
        channel_config['name'],
        channel_config['configuration'],
        platform_config
    )
    
    # 设置交易限制
    set_transaction_limits(
        connection,
        channel_config['transaction_limits']
    )
    
    # 配置支持的方法
    configure_payment_methods(
        connection,
        channel_config['supported_methods']
    )
    
    return f"Channel {channel_config['name']} configured successfully"

# 交易处理自动化
def process_payment_transaction(transaction_config, gateway_config):
    """处理支付交易"""
    
    # 创建交易记录
    transaction = create_transaction_record(transaction_config)
    
    # 执行风险评估
    risk_score = assess_transaction_risk(transaction, gateway_config)
    
    # 根据风险分数决定处理方式
    if risk_score < 0.3:
        result = auto_approve_transaction(transaction)
    elif risk_score < 0.8:
        result = flag_for_manual_review(transaction)
    else:
        result = reject_transaction(transaction)
    
    # 发送通知
    send_transaction_notification(transaction, result)
    
    return result

def assess_transaction_risk(transaction, gateway_config):
    """评估交易风险"""
    
    risk_factors = {}
    
    # 金额风险
    risk_factors['amount_risk'] = calculate_amount_risk(
        transaction['amount'],
        gateway_config['risk_management']
    )
    
    # 频率风险
    risk_factors['velocity_risk'] = calculate_velocity_risk(
        transaction['customer_id'],
        gateway_config['risk_management']
    )
    
    # 位置风险
    risk_factors['location_risk'] = calculate_location_risk(
        transaction['ip_address'],
        transaction['customer_id'],
        gateway_config['risk_management']
    )
    
    # 计算综合风险分数
    risk_score = calculate_weighted_risk_score(
        risk_factors,
        gateway_config['risk_management']['risk_scoring']
    )
    
    return risk_score

# 结算清算自动化
def process_settlement(settlement_config, gateway_config):
    """处理结算清算"""
    
    for schedule in settlement_config['settlement_schedules']:
        # 计算结算金额
        settlement_amount = calculate_settlement_amount(
            schedule['channels'],
            schedule['frequency']
        )
        
        # 生成结算文件
        settlement_file = generate_settlement_file(
            settlement_amount,
            schedule['channels']
        )
        
        # 发送到银行
        send_settlement_to_bank(settlement_file, schedule)
        
        # 更新结算状态
        update_settlement_status(schedule['channels'], 'completed')
    
    return "Settlement processed successfully"

# 对账核销自动化
def process_reconciliation(reconciliation_config, gateway_config):
    """处理对账核销"""
    
    for rule in reconciliation_config['reconciliation_rules']:
        # 下载结算文件
        settlement_files = download_settlement_files(rule['process'][0])
        
        # 匹配交易
        matched_transactions = match_transactions(
            settlement_files,
            reconciliation_config['reconciliation_matching']
        )
        
        # 识别差异
        discrepancies = identify_discrepancies(
            matched_transactions,
            reconciliation_config['reconciliation_matching']
        )
        
        # 处理差异
        for discrepancy in discrepancies:
            handle_discrepancy(
                discrepancy,
                reconciliation_config['discrepancy_handling']
            )
        
        # 生成对账报告
        generate_reconciliation_report(
            matched_transactions,
            discrepancies,
            rule
        )
    
    return "Reconciliation processed successfully"
```

## 5. 验证与测试

```python
class PaymentGatewayDSLValidator:
    def validate_channel_config(self, channel):
        assert 'name' in channel, "Channel must have name"
        assert 'provider' in channel, "Channel must specify provider"
        assert 'configuration' in channel, "Channel must have configuration"
        assert 'supported_methods' in channel, "Channel must define supported methods"
        assert 'transaction_limits' in channel, "Channel must define transaction limits"
    
    def validate_transaction_flow(self, flow):
        assert 'name' in flow, "Flow must have name"
        assert 'steps' in flow, "Flow must define steps"
        assert len(flow['steps']) > 0, "Flow must have at least one step"
        for step in flow['steps']:
            assert 'name' in step, "Step must have name"
            assert 'action' in step, "Step must specify action"
    
    def validate_risk_rule(self, rule):
        assert 'name' in rule, "Risk rule must have name"
        assert 'type' in rule, "Risk rule must specify type"
        assert 'rules' in rule, "Risk rule must define rules"
        for sub_rule in rule['rules']:
            assert 'name' in sub_rule, "Sub-rule must have name"
            assert 'condition' in sub_rule, "Sub-rule must specify condition"
            assert 'action' in sub_rule, "Sub-rule must specify action"
    
    def validate_settlement_config(self, settlement):
        assert 'settlement_schedules' in settlement, "Settlement must define schedules"
        for schedule in settlement['settlement_schedules']:
            assert 'name' in schedule, "Schedule must have name"
            assert 'frequency' in schedule, "Schedule must specify frequency"
            assert 'channels' in schedule, "Schedule must define channels"
    
    def validate_reconciliation_config(self, reconciliation):
        assert 'reconciliation_rules' in reconciliation, "Reconciliation must define rules"
        for rule in reconciliation['reconciliation_rules']:
            assert 'name' in rule, "Rule must have name"
            assert 'frequency' in rule, "Rule must specify frequency"
            assert 'process' in rule, "Rule must define process"
```

## 6. 总结

本DSL覆盖支付网关的核心技术栈，包括支付渠道、交易处理、风控规则、结算清算、对账核销、通知回调、监控告警等，支持支付网关的自动化配置和管理，可与支付宝、微信支付、银联、Visa、Mastercard等主流支付渠道无缝集成，为企业支付业务提供统一的形式化描述框架。
