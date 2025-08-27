# 告警建模DSL设计

## 设计目标

告警建模DSL旨在提供声明式语言定义复杂的告警规则配置，支持多种告警条件、通知策略、升级机制、抑制规则，并与主流告警平台无缝集成。

## 基本语法

### 核心结构

```dsl
alerting_model "web_service_alerting" {
  description: "Web服务告警模型"
  version: "1.0.0"
  
  namespace: "web_service"
  labels: {
    service: "web-service"
    environment: "production"
    team: "platform"
  }
  
  rules: [
    {
      name: "high_error_rate"
      condition: "error_rate > 0.05"
      duration: "2m"
      severity: "warning"
    }
  ]
  
  notifications: [
    {
      name: "slack_notification"
      type: "slack"
      channel: "#alerts"
    }
  ]
}
```

### 告警规则

```dsl
alert_rule "high_error_rate" {
  description: "高错误率告警"
  
  condition: {
    expression: "rate(http_requests_total{status_code=~\"5..\"}[5m]) / rate(http_requests_total[5m]) > 0.05"
    duration: "2m"
    evaluation_interval: "30s"
  }
  
  severity: "warning"
  priority: 2
  
  labels: {
    alert_type: "error_rate"
    service: "web-service"
    team: "platform"
    environment: "production"
  }
  
  annotations: {
    summary: "High error rate detected"
    description: "Error rate is {{ $value | humanizePercentage }} for service {{ $labels.service }}"
    runbook_url: "https://runbook.company.com/high-error-rate"
    dashboard_url: "https://grafana.company.com/d/web-service"
  }
  
  for: "2m"
  keep_firing_for: "5m"
  
  alerting: {
    enabled: true
    group_by: ["service", "environment"]
    group_wait: "30s"
    group_interval: "5m"
    repeat_interval: "4h"
  }
}
```

### 通知配置

```dsl
notification_config "slack_notification" {
  description: "Slack通知配置"
  
  type: "slack"
  name: "slack_alerts"
  
  config: {
    webhook_url: "https://hooks.slack.com/services/xxx/yyy/zzz"
    channel: "#alerts"
    username: "AlertManager"
    icon_emoji: ":warning:"
    icon_url: "https://alertmanager.company.com/icon.png"
  }
  
  templates: {
    title: "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}"
    text: |
      {{ range .Alerts }}
      *Alert:* {{ .Annotations.summary }}
      *Description:* {{ .Annotations.description }}
      *Severity:* {{ .Labels.severity }}
      *Service:* {{ .Labels.service }}
      *Environment:* {{ .Labels.environment }}
      *Started:* {{ .StartsAt | since }}
      {{ if .Annotations.runbook_url }}*Runbook:* {{ .Annotations.runbook_url }}{{ end }}
      {{ if .Annotations.dashboard_url }}*Dashboard:* {{ .Annotations.dashboard_url }}{{ end }}
      {{ end }}
    
    color: {
      critical: "#FF0000"
      warning: "#FFA500"
      info: "#0000FF"
    }
  }
  
  routing: {
    severity_mapping: {
      critical: ["#alerts-critical", "#oncall"]
      warning: ["#alerts"]
      info: ["#alerts-info"]
    }
    
    time_based: {
      business_hours: {
        start: "09:00"
        end: "18:00"
        timezone: "UTC"
        channels: ["#alerts", "#team-platform"]
      }
      after_hours: {
        channels: ["#alerts", "#oncall"]
        escalation: "pagerduty"
      }
    }
  }
}
```

### 升级策略

```dsl
escalation_policy "service_escalation" {
  description: "服务告警升级策略"
  
  name: "service_escalation_policy"
  
  levels: [
    {
      level: 1
      name: "immediate"
      delay: "0s"
      notifications: [
        {
          type: "slack"
          channel: "#alerts"
          template: "immediate_alert"
        }
      ]
      timeout: "5m"
    },
    {
      level: 2
      name: "5_minute"
      delay: "5m"
      notifications: [
        {
          type: "slack"
          channel: "#oncall"
          template: "escalation_alert"
        },
        {
          type: "email"
          recipients: ["oncall@company.com"]
          template: "escalation_email"
        }
      ]
      timeout: "15m"
    },
    {
      level: 3
      name: "15_minute"
      delay: "15m"
      notifications: [
        {
          type: "pagerduty"
          service_id: "xxx"
          urgency: "high"
        },
        {
          type: "phone"
          recipients: ["+1234567890"]
          template: "phone_alert"
        }
      ]
      timeout: "30m"
    },
    {
      level: 4
      name: "30_minute"
      delay: "30m"
      notifications: [
        {
          type: "pagerduty"
          service_id: "xxx"
          urgency: "high"
          escalation_policy: "manager"
        },
        {
          type: "email"
          recipients: ["manager@company.com", "cto@company.com"]
          template: "management_alert"
        }
      ]
      timeout: "1h"
    }
  ]
  
  auto_resolve: {
    enabled: true
    condition: "alert resolved for 5m"
    notification: {
      type: "slack"
      channel: "#alerts"
      template: "resolution_alert"
    }
  }
}
```

### 抑制规则

```dsl
inhibition_rule "service_inhibition" {
  description: "服务告警抑制规则"
  
  name: "service_inhibition"
  
  source_match: {
    severity: "critical"
    service: "web-service"
  }
  
  target_match: {
    severity: "warning"
    service: "web-service"
  }
  
  equal: ["service", "environment"]
  
  conditions: [
    {
      type: "service_down"
      expression: "up{service=\"web-service\"} == 0"
      duration: "1m"
    },
    {
      type: "maintenance_window"
      expression: "maintenance_mode == 1"
      duration: "0s"
    }
  ]
  
  exceptions: [
    {
      name: "critical_errors"
      labels: {
        alert_type: "critical_error"
        severity: "critical"
      }
    }
  ]
}
```

## 高级用法

### 复合告警

```dsl
composite_alert "service_degradation" {
  description: "服务降级复合告警"
  
  name: "service_degradation"
  
  conditions: [
    {
      name: "high_error_rate"
      expression: "error_rate > 0.05"
      weight: 0.4
      duration: "2m"
    },
    {
      name: "high_latency"
      expression: "p95_latency > 2"
      weight: 0.3
      duration: "2m"
    },
    {
      name: "low_throughput"
      expression: "request_rate < 100"
      weight: 0.3
      duration: "2m"
    }
  ]
  
  aggregation: {
    strategy: "weighted_sum"
    threshold: 0.7
    window: "5m"
  }
  
  severity: "warning"
  priority: 3
  
  labels: {
    alert_type: "service_degradation"
    service: "web-service"
    team: "platform"
  }
  
  annotations: {
    summary: "Service degradation detected"
    description: "Multiple performance indicators show degradation"
    runbook_url: "https://runbook.company.com/service-degradation"
  }
  
  alerting: {
    group_by: ["service"]
    group_wait: "30s"
    group_interval: "2m"
    repeat_interval: "1h"
  }
}
```

### 智能告警

```dsl
intelligent_alert "anomaly_detection" {
  description: "异常检测智能告警"
  
  name: "anomaly_detection"
  
  ml_model: {
    type: "anomaly_detection"
    algorithm: "isolation_forest"
    features: [
      "error_rate",
      "response_time",
      "cpu_usage",
      "memory_usage",
      "disk_usage"
    ]
    parameters: {
      contamination: 0.1
      n_estimators: 100
      random_state: 42
    }
  }
  
  training: {
    data_source: "historical_metrics"
    time_window: "30d"
    update_frequency: "1d"
    validation_split: 0.2
  }
  
  detection: {
    window_size: "10m"
    slide_interval: "1m"
    confidence_threshold: 0.8
    min_anomaly_duration: "2m"
  }
  
  severity_mapping: {
    low: {
      threshold: 0.6
      severity: "info"
      notifications: ["slack"]
    },
    medium: {
      threshold: 0.8
      severity: "warning"
      notifications: ["slack", "email"]
    },
    high: {
      threshold: 0.95
      severity: "critical"
      notifications: ["slack", "pagerduty"]
    }
  }
  
  auto_remediation: {
    enabled: true
    actions: [
      {
        name: "restart_service"
        condition: "anomaly_score > 0.9 AND service_health < 0.5"
        action: "kubectl rollout restart deployment/web-service"
        timeout: "5m"
      },
      {
        name: "scale_up"
        condition: "anomaly_score > 0.8 AND cpu_usage > 0.8"
        action: "kubectl scale deployment web-service --replicas=5"
        timeout: "2m"
      }
    ]
  }
}
```

### 业务告警

```dsl
business_alert "business_impact" {
  description: "业务影响告警"
  
  name: "business_impact"
  
  business_metrics: [
    {
      name: "order_success_rate"
      slo_target: 0.999
      current_value: "rate(orders_completed_total[5m]) / rate(orders_created_total[5m])"
      impact: "revenue_loss"
    },
    {
      name: "user_experience_score"
      slo_target: 0.95
      current_value: "avg(user_satisfaction_score[1h])"
      impact: "customer_satisfaction"
    },
    {
      name: "system_availability"
      slo_target: 0.9999
      current_value: "avg(up[5m])"
      impact: "service_availability"
    }
  ]
  
  impact_assessment: {
    revenue_impact: {
      calculation: "estimated_revenue_loss_per_minute * downtime_minutes"
      thresholds: {
        low: 100
        medium: 1000
        high: 10000
      }
    },
    customer_impact: {
      calculation: "affected_users * impact_score"
      thresholds: {
        low: 100
        medium: 1000
        high: 10000
      }
    }
  }
  
  severity_mapping: {
    critical: {
      condition: "revenue_impact > 10000 OR customer_impact > 10000"
      notifications: ["pagerduty", "cto_email", "emergency_phone"]
      escalation: "immediate"
    },
    high: {
      condition: "revenue_impact > 1000 OR customer_impact > 1000"
      notifications: ["pagerduty", "manager_email"]
      escalation: "15m"
    },
    medium: {
      condition: "revenue_impact > 100 OR customer_impact > 100"
      notifications: ["slack", "email"]
      escalation: "1h"
    }
  }
  
  business_continuity: {
    enabled: true
    actions: [
      {
        name: "activate_backup_system"
        condition: "system_availability < 0.9"
        action: "switch_to_backup_datacenter"
        approval_required: false
      },
      {
        name: "notify_customers"
        condition: "customer_impact > 1000"
        action: "send_customer_notification"
        approval_required: true
      }
    ]
  }
}
```

## 代码生成模板

### Prometheus告警规则

```yaml
# 生成的Prometheus告警规则
groups:
  - name: web_service_alerts
    rules:
      - alert: HighErrorRate
        expr: rate(http_requests_total{status_code=~"5.."}[5m]) / rate(http_requests_total[5m]) > 0.05
        for: 2m
        labels:
          severity: warning
          alert_type: error_rate
          service: web-service
          team: platform
          environment: production
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value | humanizePercentage }} for service {{ $labels.service }}"
          runbook_url: "https://runbook.company.com/high-error-rate"
          dashboard_url: "https://grafana.company.com/d/web-service"

      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 2
        for: 2m
        labels:
          severity: warning
          alert_type: latency
          service: web-service
          team: platform
          environment: production
        annotations:
          summary: "High latency detected"
          description: "95th percentile latency is {{ $value }}s for service {{ $labels.service }}"
          runbook_url: "https://runbook.company.com/high-latency"
          dashboard_url: "https://grafana.company.com/d/web-service"

      - alert: ServiceDown
        expr: up{service="web-service"} == 0
        for: 1m
        labels:
          severity: critical
          alert_type: service_down
          service: web-service
          team: platform
          environment: production
        annotations:
          summary: "Service is down"
          description: "Service {{ $labels.service }} is down"
          runbook_url: "https://runbook.company.com/service-down"
          dashboard_url: "https://grafana.company.com/d/web-service"

      - alert: HighCPUUsage
        expr: cpu_usage > 0.8
        for: 5m
        labels:
          severity: warning
          alert_type: resource_usage
          service: web-service
          team: platform
          environment: production
        annotations:
          summary: "High CPU usage"
          description: "CPU usage is {{ $value | humanizePercentage }} for service {{ $labels.service }}"
          runbook_url: "https://runbook.company.com/high-cpu-usage"
          dashboard_url: "https://grafana.company.com/d/web-service"
```

### Alertmanager配置

```yaml
# 生成的Alertmanager配置
global:
  resolve_timeout: 5m
  slack_api_url: 'https://hooks.slack.com/services/xxx/yyy/zzz'

route:
  group_by: ['service', 'environment']
  group_wait: 30s
  group_interval: 5m
  repeat_interval: 4h
  receiver: 'slack-notifications'
  routes:
    - match:
        severity: critical
      receiver: 'pagerduty-critical'
      continue: true
    - match:
        severity: warning
      receiver: 'slack-warnings'
      continue: true
    - match:
        severity: info
      receiver: 'slack-info'

inhibit_rules:
  - source_match:
      severity: 'critical'
      service: 'web-service'
    target_match:
      severity: 'warning'
      service: 'web-service'
    equal: ['service', 'environment']

receivers:
  - name: 'slack-notifications'
    slack_configs:
      - channel: '#alerts'
        title: '{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}'
        text: |
          {{ range .Alerts }}
          *Alert:* {{ .Annotations.summary }}
          *Description:* {{ .Annotations.description }}
          *Severity:* {{ .Labels.severity }}
          *Service:* {{ .Labels.service }}
          *Environment:* {{ .Labels.environment }}
          *Started:* {{ .StartsAt | since }}
          {{ if .Annotations.runbook_url }}*Runbook:* {{ .Annotations.runbook_url }}{{ end }}
          {{ if .Annotations.dashboard_url }}*Dashboard:* {{ .Annotations.dashboard_url }}{{ end }}
          {{ end }}
        color: '{{ if eq .GroupLabels.severity "critical" }}danger{{ else if eq .GroupLabels.severity "warning" }}warning{{ else }}good{{ end }}'

  - name: 'slack-warnings'
    slack_configs:
      - channel: '#alerts'
        title: '{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}'
        text: |
          {{ range .Alerts }}
          *Warning:* {{ .Annotations.summary }}
          *Description:* {{ .Annotations.description }}
          *Service:* {{ .Labels.service }}
          {{ end }}
        color: 'warning'

  - name: 'slack-info'
    slack_configs:
      - channel: '#alerts-info'
        title: '{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}'
        text: |
          {{ range .Alerts }}
          *Info:* {{ .Annotations.summary }}
          *Description:* {{ .Annotations.description }}
          *Service:* {{ .Labels.service }}
          {{ end }}
        color: 'good'

  - name: 'pagerduty-critical'
    pagerduty_configs:
      - service_key: 'xxx'
        description: '{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}'
        client: 'AlertManager'
        client_url: '{{ template "pagerduty.default.clientURL" . }}'
        severity: '{{ if eq .GroupLabels.severity "critical" }}critical{{ else }}warning{{ end }}'
        class: '{{ template "pagerduty.default.class" . }}'
        group: '{{ template "pagerduty.default.group" . }}'
        details:
          firing: '{{ template "pagerduty.default.firing" . }}'
          num_firing: '{{ .Alerts.Firing | len }}'
          num_resolved: '{{ .Alerts.Resolved | len }}'
          resolved: '{{ template "pagerduty.default.resolved" . }}'
          group_labels: '{{ template "pagerduty.default.groupLabels" . }}'
          common_labels: '{{ template "pagerduty.default.commonLabels" . }}'
          common_annotations: '{{ template "pagerduty.default.commonAnnotations" . }}'
          external_url: '{{ template "pagerduty.default.externalURL" . }}'

templates:
  - '/etc/alertmanager/template/*.tmpl'
```

### Python实现

```python
import time
import json
import requests
from typing import Dict, List, Any
from dataclasses import dataclass
from datetime import datetime, timedelta

@dataclass
class AlertRule:
    name: str
    condition: str
    duration: str
    severity: str
    labels: Dict[str, str]
    annotations: Dict[str, str]

@dataclass
class Alert:
    name: str
    severity: str
    labels: Dict[str, str]
    annotations: Dict[str, str]
    starts_at: datetime
    ends_at: datetime = None
    status: str = "firing"

class AlertingEngine:
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.rules = self._load_rules()
        self.notifications = self._load_notifications()
        self.active_alerts = {}
    
    def _load_rules(self) -> List[AlertRule]:
        """加载告警规则"""
        rules = []
        for rule_config in self.config.get('rules', []):
            rule = AlertRule(
                name=rule_config['name'],
                condition=rule_config['condition'],
                duration=rule_config.get('duration', '0s'),
                severity=rule_config['severity'],
                labels=rule_config.get('labels', {}),
                annotations=rule_config.get('annotations', {})
            )
            rules.append(rule)
        return rules
    
    def _load_notifications(self) -> Dict[str, Any]:
        """加载通知配置"""
        return self.config.get('notifications', {})
    
    def evaluate_condition(self, condition: str, metrics: Dict[str, float]) -> bool:
        """评估告警条件"""
        try:
            # 简单的条件评估逻辑
            if '>' in condition:
                metric, threshold = condition.split('>')
                metric = metric.strip()
                threshold = float(threshold.strip())
                return metrics.get(metric, 0) > threshold
            elif '<' in condition:
                metric, threshold = condition.split('<')
                metric = metric.strip()
                threshold = float(threshold.strip())
                return metrics.get(metric, 0) < threshold
            elif '==' in condition:
                metric, value = condition.split('==')
                metric = metric.strip()
                value = value.strip()
                return metrics.get(metric, 0) == float(value)
            return False
        except Exception as e:
            print(f"Error evaluating condition {condition}: {e}")
            return False
    
    def check_alerts(self, metrics: Dict[str, float]) -> List[Alert]:
        """检查告警"""
        new_alerts = []
        resolved_alerts = []
        
        for rule in self.rules:
            alert_key = f"{rule.name}_{rule.severity}"
            
            # 评估条件
            is_firing = self.evaluate_condition(rule.condition, metrics)
            
            if is_firing:
                if alert_key not in self.active_alerts:
                    # 新告警
                    alert = Alert(
                        name=rule.name,
                        severity=rule.severity,
                        labels=rule.labels.copy(),
                        annotations=rule.annotations.copy(),
                        starts_at=datetime.now(),
                        status="firing"
                    )
                    self.active_alerts[alert_key] = alert
                    new_alerts.append(alert)
                else:
                    # 更新现有告警
                    self.active_alerts[alert_key].status = "firing"
            else:
                if alert_key in self.active_alerts:
                    # 告警恢复
                    alert = self.active_alerts[alert_key]
                    alert.status = "resolved"
                    alert.ends_at = datetime.now()
                    resolved_alerts.append(alert)
                    del self.active_alerts[alert_key]
        
        return new_alerts, resolved_alerts
    
    def send_notification(self, alert: Alert, notification_type: str = "slack"):
        """发送通知"""
        if notification_type == "slack":
            self._send_slack_notification(alert)
        elif notification_type == "email":
            self._send_email_notification(alert)
        elif notification_type == "pagerduty":
            self._send_pagerduty_notification(alert)
    
    def _send_slack_notification(self, alert: Alert):
        """发送Slack通知"""
        slack_config = self.notifications.get('slack', {})
        webhook_url = slack_config.get('webhook_url')
        
        if not webhook_url:
            return
        
        message = {
            "channel": slack_config.get('channel', '#alerts'),
            "username": slack_config.get('username', 'AlertManager'),
            "icon_emoji": slack_config.get('icon_emoji', ':warning:'),
            "attachments": [
                {
                    "color": self._get_severity_color(alert.severity),
                    "title": alert.annotations.get('summary', alert.name),
                    "text": alert.annotations.get('description', ''),
                    "fields": [
                        {
                            "title": "Severity",
                            "value": alert.severity,
                            "short": True
                        },
                        {
                            "title": "Service",
                            "value": alert.labels.get('service', 'unknown'),
                            "short": True
                        },
                        {
                            "title": "Started",
                            "value": alert.starts_at.strftime('%Y-%m-%d %H:%M:%S'),
                            "short": True
                        }
                    ],
                    "footer": "AlertManager",
                    "ts": int(alert.starts_at.timestamp())
                }
            ]
        }
        
        try:
            response = requests.post(webhook_url, json=message)
            response.raise_for_status()
            print(f"Slack notification sent for alert {alert.name}")
        except Exception as e:
            print(f"Failed to send Slack notification: {e}")
    
    def _send_email_notification(self, alert: Alert):
        """发送邮件通知"""
        # 实现邮件发送逻辑
        pass
    
    def _send_pagerduty_notification(self, alert: Alert):
        """发送PagerDuty通知"""
        # 实现PagerDuty通知逻辑
        pass
    
    def _get_severity_color(self, severity: str) -> str:
        """获取严重程度对应的颜色"""
        colors = {
            'critical': '#FF0000',
            'warning': '#FFA500',
            'info': '#0000FF'
        }
        return colors.get(severity, '#808080')

# 使用示例
config = {
    "rules": [
        {
            "name": "high_error_rate",
            "condition": "error_rate > 0.05",
            "duration": "2m",
            "severity": "warning",
            "labels": {
                "service": "web-service",
                "team": "platform"
            },
            "annotations": {
                "summary": "High error rate detected",
                "description": "Error rate is above 5%"
            }
        },
        {
            "name": "service_down",
            "condition": "up == 0",
            "duration": "1m",
            "severity": "critical",
            "labels": {
                "service": "web-service",
                "team": "platform"
            },
            "annotations": {
                "summary": "Service is down",
                "description": "Service is not responding"
            }
        }
    ],
    "notifications": {
        "slack": {
            "webhook_url": "https://hooks.slack.com/services/xxx/yyy/zzz",
            "channel": "#alerts",
            "username": "AlertManager"
        }
    }
}

# 创建告警引擎
alerting_engine = AlertingEngine(config)

# 模拟指标数据
metrics = {
    "error_rate": 0.08,
    "up": 1,
    "response_time": 1.5
}

# 检查告警
new_alerts, resolved_alerts = alerting_engine.check_alerts(metrics)

# 发送通知
for alert in new_alerts:
    alerting_engine.send_notification(alert, "slack")

print(f"New alerts: {len(new_alerts)}")
print(f"Resolved alerts: {len(resolved_alerts)}")
```

## 验证规则

### 语法验证

```dsl
validation_rules "alerting_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "version", "namespace", "rules"]
      message: "必须包含描述、版本、命名空间和告警规则"
    },
    {
      rule: "valid_severity"
      allowed_values: ["critical", "warning", "info"]
      message: "严重程度必须是支持的值"
    },
    {
      rule: "valid_condition"
      condition: "condition expression is valid"
      message: "告警条件表达式必须有效"
    }
  ]
  
  semantic: [
    {
      rule: "rule_uniqueness"
      condition: "rule names are unique within namespace"
      message: "告警规则名称在命名空间内必须唯一"
    },
    {
      rule: "notification_configuration"
      condition: "all referenced notifications are configured"
      message: "所有引用的通知配置必须存在"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "alerting_performance" {
  constraints: [
    {
      metric: "evaluation_latency"
      threshold: "100ms"
      action: "warn"
    },
    {
      metric: "notification_delay"
      threshold: "30s"
      action: "error"
    },
    {
      metric: "false_positive_rate"
      threshold: "0.1"
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "condition_optimization"
      enabled: true
      target_efficiency: 0.95
    },
    {
      strategy: "notification_batching"
      enabled: true
      batch_size: 10
      batch_interval: "30s"
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "alerting_patterns" {
  patterns: [
    {
      name: "slo_based_alerting"
      description: "基于SLO的告警模式"
      implementation: {
        strategy: "slo_breach_detection"
        burn_rate: "calculated"
        error_budget: "tracked"
        alerting: "progressive"
      }
    },
    {
      name: "anomaly_based_alerting"
      description: "基于异常的告警模式"
      implementation: {
        strategy: "ml_anomaly_detection"
        training: "continuous"
        confidence: "adaptive"
        alerting: "intelligent"
      }
    },
    {
      name: "progressive_alerting"
      description: "渐进式告警模式"
      implementation: {
        strategy: "escalation_based"
        levels: ["immediate", "delayed", "escalated"]
        notifications: "progressive"
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "alert_storm"
      description: "告警风暴"
      symptoms: ["too_many_alerts", "notification_flood"]
      solution: "implement_suppression"
    },
    {
      name: "alert_fatigue"
      description: "告警疲劳"
      symptoms: ["ignored_alerts", "low_response_rate"]
      solution: "reduce_noise"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "alerting_monitoring" {
  metrics: [
    {
      name: "alert_evaluation_rate"
      type: "counter"
      labels: ["rule_name", "status"]
      unit: "evaluations/sec"
    },
    {
      name: "alert_firing_duration"
      type: "histogram"
      labels: ["rule_name", "severity"]
      buckets: [1, 5, 15, 30, 60, 300, 600]
    },
    {
      name: "notification_success_rate"
      type: "gauge"
      labels: ["notification_type"]
      range: [0, 1]
    }
  ]
  
  alerts: [
    {
      name: "alert_evaluation_failure"
      condition: "alert_evaluation_errors > 0"
      severity: "critical"
      action: "restart_evaluator"
    },
    {
      name: "notification_failure"
      condition: "notification_success_rate < 0.9"
      severity: "warning"
      action: "investigate_notifications"
    }
  ]
}
```

## 主流标准映射

### Prometheus集成

```dsl
prometheus_integration "prometheus_alerting" {
  metrics: [
    {
      name: "alert_evaluation_duration_seconds"
      type: "histogram"
      help: "Alert evaluation execution time"
      labels: ["rule_name", "status"]
    },
    {
      name: "alert_firing_total"
      type: "counter"
      help: "Total number of alert firings"
      labels: ["rule_name", "severity"]
    },
    {
      name: "notification_sent_total"
      type: "counter"
      help: "Total number of notifications sent"
      labels: ["notification_type", "status"]
    }
  ]
  
  rules: [
    {
      name: "Alert Evaluation Failure"
      expr: "rate(alert_evaluation_errors_total[5m]) > 0"
      for: "1m"
      labels: { severity: critical }
      annotations: { summary: "Alert evaluation is failing" }
    },
    {
      name: "High Notification Failure Rate"
      expr: "rate(notification_failures_total[5m]) / rate(notification_sent_total[5m]) > 0.1"
      for: "2m"
      labels: { severity: warning }
      annotations: { summary: "High notification failure rate" }
    }
  ]
  
  alertmanager: {
    receivers: [
      {
        name: "slack"
        slack_configs: [
          {
            channel: "#alerts"
            title: "Alerting System Alert"
            text: "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}"
          }
        ]
      }
    ]
  }
}
```

## 工程实践示例

### 微服务告警

```dsl
microservice_alerting "order_service_alerting" {
  description: "订单服务告警"
  
  namespace: "order_service"
  
  services: [
    {
      name: "order-service"
      instances: 3
      rules: [
        {
          name: "order_service_down"
          condition: "up{service=\"order-service\"} == 0"
          duration: "1m"
          severity: "critical"
          notifications: ["pagerduty", "slack"]
        },
        {
          name: "high_order_error_rate"
          condition: "rate(order_requests_total{status=\"error\"}[5m]) / rate(order_requests_total[5m]) > 0.05"
          duration: "2m"
          severity: "warning"
          notifications: ["slack", "email"]
        },
        {
          name: "slow_order_processing"
          condition: "histogram_quantile(0.95, rate(order_processing_duration_seconds_bucket[5m])) > 30"
          duration: "2m"
          severity: "warning"
          notifications: ["slack"]
        }
      ]
    },
    {
      name: "payment-service"
      instances: 2
      rules: [
        {
          name: "payment_service_down"
          condition: "up{service=\"payment-service\"} == 0"
          duration: "1m"
          severity: "critical"
          notifications: ["pagerduty", "slack"]
        },
        {
          name: "low_payment_success_rate"
          condition: "rate(payment_requests_total{status=\"success\"}[5m]) / rate(payment_requests_total[5m]) < 0.95"
          duration: "2m"
          severity: "critical"
          notifications: ["pagerduty", "slack", "email"]
        }
      ]
    },
    {
      name: "inventory-service"
      instances: 2
      rules: [
        {
          name: "inventory_service_down"
          condition: "up{service=\"inventory-service\"} == 0"
          duration: "1m"
          severity: "critical"
          notifications: ["pagerduty", "slack"]
        },
        {
          name: "low_inventory_level"
          condition: "inventory_level < 10"
          duration: "5m"
          severity: "warning"
          notifications: ["slack", "email"]
        }
      ]
    }
  ]
  
  business_rules: [
    {
      name: "order_workflow_failure"
      condition: "order_success_rate < 0.95 OR payment_success_rate < 0.95"
      duration: "5m"
      severity: "critical"
      notifications: ["pagerduty", "cto_email"]
      business_impact: "revenue_loss"
    },
    {
      name: "customer_experience_degradation"
      condition: "avg_response_time > 2 OR error_rate > 0.1"
      duration: "2m"
      severity: "warning"
      notifications: ["slack", "manager_email"]
      business_impact: "customer_satisfaction"
    }
  ]
  
  escalation: {
    levels: [
      {
        level: 1
        delay: "0s"
        notifications: ["slack"]
        timeout: "5m"
      },
      {
        level: 2
        delay: "5m"
        notifications: ["pagerduty"]
        timeout: "15m"
      },
      {
        level: 3
        delay: "15m"
        notifications: ["pagerduty", "phone"]
        timeout: "30m"
      }
    ]
  }
  
  suppression: [
    {
      name: "maintenance_window"
      condition: "maintenance_mode == 1"
      duration: "0s"
      rules: ["*"]
    },
    {
      name: "service_cascade"
      source: "service_down"
      target: "high_error_rate"
      equal: ["service"]
    }
  ]
  
  monitoring: {
    metrics: [
      "alert_firing_rate",
      "notification_success_rate",
      "escalation_rate",
      "suppression_rate"
    ]
    alerting: {
      on_high_false_positive: {
        threshold: 0.1
        severity: "warning"
        notification: "slack"
      }
      on_notification_failure: {
        threshold: 0.05
        severity: "critical"
        notification: "pagerduty"
      }
    }
  }
}
```

### 实时流告警

```dsl
stream_alerting "real_time_alerting" {
  description: "实时流告警"
  
  streaming: {
    engine: "kafka_streams"
    mode: "real_time"
    parallelism: 8
  }
  
  sources: [
    {
      name: "metrics_stream"
      type: "kafka"
      topic: "metrics-stream"
      consumer_group: "alert-processor"
      auto_offset_reset: "latest"
    },
    {
      name: "log_stream"
      type: "kafka"
      topic: "log-stream"
      consumer_group: "alert-processor"
      auto_offset_reset: "latest"
    }
  ]
  
  processing: [
    {
      name: "metric_alert_evaluation"
      type: "stream_processor"
      input: "metrics_stream"
      output: "metric_alerts"
      operations: [
        {
          type: "window"
          size: "5m"
          slide: "30s"
        },
        {
          type: "alert_evaluation"
          rules: [
            {
              name: "high_error_rate"
              condition: "error_rate > 0.05"
              severity: "warning"
            },
            {
              name: "high_latency"
              condition: "p95_latency > 2"
              severity: "warning"
            },
            {
              name: "service_down"
              condition: "up == 0"
              severity: "critical"
            }
          ]
        }
      ]
    },
    {
      name: "log_alert_evaluation"
      type: "stream_processor"
      input: "log_stream"
      output: "log_alerts"
      operations: [
        {
          type: "pattern_detection"
          patterns: [
            {
              name: "error_spike"
              pattern: "level:ERROR"
              threshold: 10
              window: "1m"
              severity: "warning"
            },
            {
              name: "exception_pattern"
              pattern: "Exception|Error|Failed"
              threshold: 5
              window: "5m"
              severity: "critical"
            }
          ]
        }
      ]
    },
    {
      name: "alert_correlation"
      type: "stream_processor"
      input: ["metric_alerts", "log_alerts"]
      output: "correlated_alerts"
      operations: [
        {
          type: "correlation"
          strategy: "temporal"
          window: "5m"
          correlation_key: "service"
        },
        {
          type: "deduplication"
          strategy: "time_based"
          window: "1m"
        }
      ]
    },
    {
      name: "intelligent_routing"
      type: "stream_processor"
      input: "correlated_alerts"
      output: "routed_alerts"
      operations: [
        {
          type: "routing"
          rules: [
            {
              condition: "severity == 'critical'"
              notifications: ["pagerduty", "slack"]
              escalation: "immediate"
            },
            {
              condition: "severity == 'warning'"
              notifications: ["slack"]
              escalation: "delayed"
            }
          ]
        }
      ]
    }
  ]
  
  outputs: [
    {
      name: "notification_sink"
      type: "multiple"
      outputs: [
        {
          type: "slack"
          webhook_url: "https://hooks.slack.com/services/xxx"
          channel: "#alerts"
        },
        {
          type: "pagerduty"
          api_key: "xxx"
          service_id: "xxx"
        },
        {
          type: "email"
          smtp_server: "smtp.company.com"
          from: "alerts@company.com"
          to: ["oncall@company.com"]
        }
      ]
    },
    {
      name: "alert_store"
      type: "elasticsearch"
      topic: "routed_alerts"
      endpoint: "http://elasticsearch:9200"
      index: "alerts"
      batch_size: 100
      flush_interval: "10s"
    }
  ]
  
  performance: {
    latency: {
      p95: "100ms"
      p99: "500ms"
    }
    throughput: {
      events_per_second: 50000
      max_lag: "1m"
    }
    scalability: {
      auto_scaling: true
      min_instances: 2
      max_instances: 20
      scale_up_threshold: 0.8
      scale_down_threshold: 0.3
      scale_up_cooldown: "5m"
      scale_down_cooldown: "10m"
    }
  }
  
  monitoring: {
    metrics: [
      "alert_evaluation_latency",
      "alert_correlation_rate",
      "notification_success_rate",
      "false_positive_rate",
      "alert_volume",
      "processing_lag"
    ]
    health_checks: [
      "kafka_connectivity",
      "elasticsearch_connectivity",
      "notification_connectivity",
      "processing_pipeline_health"
    ]
    alerting: {
      on_high_latency: {
        threshold: "100ms"
        severity: "warning"
      }
      on_high_false_positive: {
        threshold: 0.1
        severity: "warning"
      }
      on_notification_failure: {
        threshold: 0.05
        severity: "critical"
      }
      on_pipeline_failure: {
        severity: "critical"
        notification: "pagerduty"
      }
    }
  }
}
```

这个DSL设计提供了完整的告警建模能力，支持多种告警条件、通知策略、升级机制、抑制规则，并能够与主流告警平台无缝集成。
