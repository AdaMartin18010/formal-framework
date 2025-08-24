# 告警建模DSL草案

## 1. 设计目标

- 用声明式语法描述告警规则、分级、抑制、通知、闭环等流程
- 支持多源多级告警统一建模
- 便于自动生成告警与通知配置
- 支持告警聚合、降噪、自愈等高级特性

## 2. 基本语法结构

```dsl
alert "high_cpu_usage" {
  description: "CPU使用率过高告警"
  version: "1.0.0"
  author: "system"
  
  rule: {
    expression: "cpu_usage > 90"
    duration: "5m"
    evaluation_interval: "30s"
    severity: "critical"
    priority: 1
  }
  
  labels: {
    service: "web-service"
    environment: "production"
    team: "platform"
    component: "cpu"
  }
  
  annotations: {
    summary: "CPU使用率超过90%"
    description: "服务器 {{ $labels.instance }} 的CPU使用率已达到 {{ $value }}%"
    runbook_url: "https://runbook.example.com/cpu-high"
    dashboard_url: "https://grafana.example.com/d/cpu-metrics"
  }
  
  suppression: {
    enabled: true
    conditions: [
      {
        type: "time_window"
        condition: "hour >= 0 AND hour < 6"
        duration: "6h"
        reason: "维护窗口"
      },
      {
        type: "dependency"
        condition: "parent_alert_firing"
        duration: "until_parent_resolved"
        reason: "依赖告警已触发"
      }
    ]
  }
  
  notification: {
    channels: [
      {
        name: "ops-team"
        type: "email"
        recipients: ["ops@example.com", "oncall@example.com"]
        template: "critical_alert"
        escalation: {
          enabled: true
          delay: "10m"
          next_level: "manager"
        }
      },
      {
        name: "slack-alerts"
        type: "slack"
        channel: "#alerts"
        template: "slack_alert"
        mentions: ["@here"]
      },
      {
        name: "pagerduty"
        type: "pagerduty"
        service: "platform-service"
        urgency: "high"
        auto_resolve: true
      }
    ]
    grouping: {
      enabled: true
      group_by: ["service", "environment"]
      group_wait: "30s"
      group_interval: "5m"
      repeat_interval: "4h"
    }
  }
  
  escalation: {
    enabled: true
    levels: [
      {
        level: 1
        delay: "5m"
        notification: "ops-team"
      },
      {
        level: 2
        delay: "15m"
        notification: "manager"
        auto_actions: ["scale_up", "restart_service"]
      },
      {
        level: 3
        delay: "30m"
        notification: "emergency"
        auto_actions: ["failover", "page_manager"]
      }
    ]
  }
  
  auto_recovery: {
    enabled: true
    conditions: [
      {
        expression: "cpu_usage < 70"
        duration: "2m"
        action: "resolve_alert"
      }
    ]
    actions: [
      {
        name: "scale_up"
        type: "kubernetes"
        target: "deployment/web-service"
        action: "scale"
        parameters: {
          replicas: "{{ current_replicas + 2 }}"
        }
      },
      {
        name: "restart_service"
        type: "kubernetes"
        target: "deployment/web-service"
        action: "restart"
      }
    ]
  }
  
  correlation: {
    enabled: true
    rules: [
      {
        name: "cpu_memory_correlation"
        condition: "cpu_usage > 90 AND memory_usage > 85"
        action: "escalate_to_level_2"
        reason: "CPU和内存同时告警"
      }
    ]
  }
  
  metrics: {
    enabled: true
    collection: [
      "alert_firing_duration",
      "notification_sent_count",
      "escalation_triggered_count",
      "auto_recovery_success_rate"
    ]
  }
}
```

## 3. 关键元素

- alert：告警声明
- description：描述信息
- version：版本号
- author：作者
- rule：告警规则
- labels：标签
- annotations：注解
- suppression：抑制规则
- notification：通知配置
- escalation：升级策略
- auto_recovery：自动恢复
- correlation：关联规则
- metrics：指标收集

## 4. 高级用法

### 4.1 复杂告警规则

```dsl
alert "service_unavailable" {
  description: "服务不可用告警"
  version: "1.0.0"
  author: "system"
  
  rule: {
    expression: "up{service=\"web-service\"} == 0 OR http_response_time > 5"
    duration: "2m"
    evaluation_interval: "15s"
    severity: "critical"
    priority: 1
  }
  
  labels: {
    service: "web-service"
    environment: "production"
    team: "frontend"
    component: "api"
  }
  
  annotations: {
    summary: "服务 {{ $labels.service }} 不可用"
    description: "服务 {{ $labels.service }} 在 {{ $labels.instance }} 上不可用，响应时间: {{ $value }}s"
    runbook_url: "https://runbook.example.com/service-unavailable"
    dashboard_url: "https://grafana.example.com/d/service-health"
  }
  
  suppression: {
    enabled: true
    conditions: [
      {
        type: "time_window"
        condition: "hour >= 2 AND hour < 4"
        duration: "2h"
        reason: "计划维护"
      },
      {
        type: "dependency"
        condition: "database_down OR load_balancer_down"
        duration: "until_dependency_resolved"
        reason: "依赖服务故障"
      }
    ]
  }
  
  notification: {
    channels: [
      {
        name: "emergency-pager"
        type: "pagerduty"
        service: "web-service-critical"
        urgency: "high"
        auto_resolve: false
        escalation_policy: "web-service-escalation"
      },
      {
        name: "slack-critical"
        type: "slack"
        channel: "#critical-alerts"
        template: "critical_service_alert"
        mentions: ["@here", "@oncall"]
      },
      {
        name: "email-notification"
        type: "email"
        recipients: ["ops@example.com", "dev@example.com"]
        template: "service_alert"
        cc: ["manager@example.com"]
      }
    ]
    grouping: {
      enabled: true
      group_by: ["service", "environment"]
      group_wait: "10s"
      group_interval: "2m"
      repeat_interval: "1h"
    }
    routing: {
      enabled: true
      rules: [
        {
          condition: "environment == 'production'"
          channels: ["emergency-pager", "slack-critical"]
        },
        {
          condition: "environment == 'staging'"
          channels: ["slack-critical", "email-notification"]
        }
      ]
    }
  }
  
  escalation: {
    enabled: true
    levels: [
      {
        level: 1
        delay: "2m"
        notification: "emergency-pager"
        auto_actions: ["check_health", "restart_service"]
      },
      {
        level: 2
        delay: "5m"
        notification: "manager"
        auto_actions: ["scale_up", "failover"]
      },
      {
        level: 3
        delay: "10m"
        notification: "cto"
        auto_actions: ["emergency_deployment", "rollback"]
      }
    ]
  }
  
  auto_recovery: {
    enabled: true
    conditions: [
      {
        expression: "up{service=\"web-service\"} == 1 AND http_response_time < 2"
        duration: "1m"
        action: "resolve_alert"
      }
    ]
    actions: [
      {
        name: "check_health"
        type: "http"
        url: "https://{{ $labels.instance }}/health"
        method: "GET"
        timeout: "10s"
        expected_status: 200
      },
      {
        name: "restart_service"
        type: "kubernetes"
        target: "deployment/web-service"
        action: "restart"
        namespace: "{{ $labels.namespace }}"
      },
      {
        name: "scale_up"
        type: "kubernetes"
        target: "deployment/web-service"
        action: "scale"
        parameters: {
          replicas: "{{ current_replicas + 3 }}"
        }
      },
      {
        name: "failover"
        type: "load_balancer"
        action: "disable_backend"
        target: "{{ $labels.instance }}"
        duration: "5m"
      }
    ]
  }
  
  correlation: {
    enabled: true
    rules: [
      {
        name: "multiple_services_down"
        condition: "count(up{service=~\".*\"} == 0) > 3"
        action: "escalate_to_level_3"
        reason: "多个服务同时不可用"
      },
      {
        name: "database_connection_issue"
        condition: "service_unavailable AND database_connection_errors > 10"
        action: "trigger_database_alert"
        reason: "数据库连接问题"
      }
    ]
  }
  
  metrics: {
    enabled: true
    collection: [
      "alert_firing_duration",
      "notification_sent_count",
      "escalation_triggered_count",
      "auto_recovery_success_rate",
      "mean_time_to_resolution"
    ]
    thresholds: {
      mttr_warning: "15m"
      mttr_critical: "30m"
    }
  }
}
```

### 4.2 告警聚合与降噪

```dsl
alert_group "infrastructure_alerts" {
  description: "基础设施告警组"
  version: "1.0.0"
  
  members: [
    "high_cpu_usage",
    "high_memory_usage",
    "disk_space_low",
    "network_high_latency"
  ]
  
  aggregation: {
    enabled: true
    strategy: "count_based"
    threshold: 3
    window: "10m"
    group_by: ["host", "environment"]
  }
  
  noise_reduction: {
    enabled: true
    strategies: [
      {
        type: "frequency_limit"
        max_alerts: 5
        window: "1h"
      },
      {
        type: "similarity_detection"
        similarity_threshold: 0.8
        group_similar: true
      }
    ]
  }
  
  notification: {
    channels: [
      {
        name: "infra-team"
        type: "slack"
        channel: "#infrastructure"
        template: "infra_alert_group"
      }
    ]
    grouping: {
      enabled: true
      group_by: ["environment", "severity"]
      group_wait: "1m"
      group_interval: "5m"
      repeat_interval: "2h"
    }
  }
  
  escalation: {
    enabled: true
    levels: [
      {
        level: 1
        delay: "10m"
        condition: "alert_count > 5"
        notification: "infra-team"
      },
      {
        level: 2
        delay: "30m"
        condition: "alert_count > 10"
        notification: "emergency"
      }
    ]
  }
}
```

### 4.3 智能告警

```dsl
alert "anomaly_detection" {
  description: "异常检测告警"
  version: "1.0.0"
  author: "system"
  
  rule: {
    expression: "anomaly_score > 0.8"
    duration: "5m"
    evaluation_interval: "1m"
    severity: "warning"
    priority: 2
  }
  
  labels: {
    service: "all"
    environment: "production"
    team: "mlops"
    component: "anomaly_detection"
  }
  
  annotations: {
    summary: "检测到异常行为"
    description: "服务 {{ $labels.service }} 在 {{ $labels.instance }} 上检测到异常，异常分数: {{ $value }}"
    runbook_url: "https://runbook.example.com/anomaly-detection"
  }
  
  ml_model: {
    enabled: true
    model_type: "isolation_forest"
    features: [
      "cpu_usage",
      "memory_usage",
      "network_traffic",
      "error_rate",
      "response_time"
    ]
    training_window: "7d"
    update_frequency: "1h"
    confidence_threshold: 0.8
  }
  
  notification: {
    channels: [
      {
        name: "mlops-team"
        type: "slack"
        channel: "#mlops-alerts"
        template: "anomaly_alert"
      }
    ]
  }
  
  auto_recovery: {
    enabled: true
    conditions: [
      {
        expression: "anomaly_score < 0.3"
        duration: "10m"
        action: "resolve_alert"
      }
    ]
    actions: [
      {
        name: "collect_evidence"
        type: "data_collection"
        metrics: [
          "cpu_usage",
          "memory_usage",
          "network_traffic",
          "error_rate"
        ]
        duration: "5m"
      }
    ]
  }
}
```

## 5. 代码生成模板

### 5.1 Prometheus Alertmanager生成

```yaml
# prometheus-rules.yml
groups:
  - name: web-service-alerts
    rules:
      - alert: HighCPUUsage
        expr: cpu_usage > 90
        for: 5m
        labels:
          severity: critical
          service: web-service
          environment: production
          team: platform
          component: cpu
        annotations:
          summary: "CPU使用率超过90%"
          description: "服务器 {{ $labels.instance }} 的CPU使用率已达到 {{ $value }}%"
          runbook_url: "https://runbook.example.com/cpu-high"
          dashboard_url: "https://grafana.example.com/d/cpu-metrics"

      - alert: ServiceUnavailable
        expr: up{service="web-service"} == 0 OR http_response_time > 5
        for: 2m
        labels:
          severity: critical
          service: web-service
          environment: production
          team: frontend
          component: api
        annotations:
          summary: "服务 {{ $labels.service }} 不可用"
          description: "服务 {{ $labels.service }} 在 {{ $labels.instance }} 上不可用，响应时间: {{ $value }}s"
          runbook_url: "https://runbook.example.com/service-unavailable"
          dashboard_url: "https://grafana.example.com/d/service-health"
```

```yaml
# alertmanager.yml
global:
  resolve_timeout: 5m
  slack_api_url: 'https://hooks.slack.com/services/xxx/yyy/zzz'

route:
  group_by: ['service', 'environment']
  group_wait: 30s
  group_interval: 5m
  repeat_interval: 4h
  receiver: 'ops-team'
  routes:
    - match:
        environment: production
      receiver: 'emergency-pager'
      routes:
        - match:
            severity: critical
          receiver: 'emergency-pager'
          group_wait: 10s
          group_interval: 2m
          repeat_interval: 1h
    - match:
        environment: staging
      receiver: 'slack-critical'
      group_wait: 1m
      group_interval: 5m
      repeat_interval: 2h

inhibit_rules:
  - source_match:
      alertname: 'DatabaseDown'
    target_match:
      alertname: 'ServiceUnavailable'
    equal: ['instance']

receivers:
  - name: 'ops-team'
    email_configs:
      - to: 'ops@example.com'
        send_resolved: true
    slack_configs:
      - channel: '#alerts'
        title: '{{ template "slack.title" . }}'
        text: '{{ template "slack.text" . }}'
        send_resolved: true

  - name: 'emergency-pager'
    pagerduty_configs:
      - service_key: 'xxx'
        send_resolved: true
        description: '{{ template "pagerduty.description" . }}'
        severity: '{{ if eq .GroupLabels.severity "critical" }}critical{{ else }}warning{{ end }}'

  - name: 'slack-critical'
    slack_configs:
      - channel: '#critical-alerts'
        title: '{{ template "slack.critical.title" . }}'
        text: '{{ template "slack.critical.text" . }}'
        send_resolved: true

templates:
  - '/etc/alertmanager/template/*.tmpl'
```

### 5.2 Kubernetes Operator生成

```yaml
# prometheus-rule.yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: web-service-alerts
  namespace: monitoring
  labels:
    prometheus: kube-prometheus
    role: alert-rules
spec:
  groups:
    - name: web-service-alerts
      rules:
        - alert: HighCPUUsage
          expr: cpu_usage > 90
          for: 5m
          labels:
            severity: critical
            service: web-service
            environment: production
            team: platform
            component: cpu
          annotations:
            summary: "CPU使用率超过90%"
            description: "服务器 {{ $labels.instance }} 的CPU使用率已达到 {{ $value }}%"
            runbook_url: "https://runbook.example.com/cpu-high"
            dashboard_url: "https://grafana.example.com/d/cpu-metrics"

        - alert: ServiceUnavailable
          expr: up{service="web-service"} == 0 OR http_response_time > 5
          for: 2m
          labels:
            severity: critical
            service: web-service
            environment: production
            team: frontend
            component: api
          annotations:
            summary: "服务 {{ $labels.service }} 不可用"
            description: "服务 {{ $labels.service }} 在 {{ $labels.instance }} 上不可用，响应时间: {{ $value }}s"
            runbook_url: "https://runbook.example.com/service-unavailable"
            dashboard_url: "https://grafana.example.com/d/service-health"
```

### 5.3 自定义告警处理器生成

```python
# alert_processor.py
import json
import requests
from datetime import datetime, timedelta
from typing import Dict, List, Any

class AlertProcessor:
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.alert_history = {}
        self.escalation_levels = config.get('escalation', {}).get('levels', [])
        
    def process_alert(self, alert: Dict[str, Any]) -> None:
        """处理告警"""
        alert_id = alert.get('id')
        severity = alert.get('severity')
        service = alert.get('labels', {}).get('service')
        
        # 检查抑制条件
        if self._should_suppress(alert):
            print(f"Alert {alert_id} suppressed")
            return
            
        # 检查关联规则
        correlated_alerts = self._check_correlation(alert)
        if correlated_alerts:
            self._handle_correlated_alerts(alert, correlated_alerts)
            
        # 发送通知
        self._send_notifications(alert)
        
        # 触发自动恢复
        if self._should_auto_recover(alert):
            self._trigger_auto_recovery(alert)
            
        # 记录告警历史
        self._record_alert_history(alert)
        
    def _should_suppress(self, alert: Dict[str, Any]) -> bool:
        """检查是否应该抑制告警"""
        suppression = self.config.get('suppression', {})
        if not suppression.get('enabled', False):
            return False
            
        for condition in suppression.get('conditions', []):
            if self._evaluate_condition(condition, alert):
                return True
        return False
        
    def _check_correlation(self, alert: Dict[str, Any]) -> List[Dict[str, Any]]:
        """检查关联告警"""
        correlation = self.config.get('correlation', {})
        if not correlation.get('enabled', False):
            return []
            
        correlated = []
        for rule in correlation.get('rules', []):
            if self._evaluate_correlation_rule(rule, alert):
                correlated.append(rule)
        return correlated
        
    def _send_notifications(self, alert: Dict[str, Any]) -> None:
        """发送通知"""
        notification = self.config.get('notification', {})
        channels = notification.get('channels', [])
        
        for channel in channels:
            if self._should_send_to_channel(channel, alert):
                self._send_to_channel(channel, alert)
                
    def _should_auto_recover(self, alert: Dict[str, Any]) -> bool:
        """检查是否应该自动恢复"""
        auto_recovery = self.config.get('auto_recovery', {})
        if not auto_recovery.get('enabled', False):
            return False
            
        for condition in auto_recovery.get('conditions', []):
            if self._evaluate_condition(condition, alert):
                return True
        return False
        
    def _trigger_auto_recovery(self, alert: Dict[str, Any]) -> None:
        """触发自动恢复"""
        auto_recovery = self.config.get('auto_recovery', {})
        actions = auto_recovery.get('actions', [])
        
        for action in actions:
            self._execute_action(action, alert)
            
    def _execute_action(self, action: Dict[str, Any], alert: Dict[str, Any]) -> None:
        """执行动作"""
        action_type = action.get('type')
        action_name = action.get('name')
        
        if action_type == 'kubernetes':
            self._execute_kubernetes_action(action, alert)
        elif action_type == 'http':
            self._execute_http_action(action, alert)
        elif action_type == 'load_balancer':
            self._execute_load_balancer_action(action, alert)
            
    def _execute_kubernetes_action(self, action: Dict[str, Any], alert: Dict[str, Any]) -> None:
        """执行Kubernetes动作"""
        target = action.get('target')
        action_name = action.get('action')
        
        if action_name == 'restart':
            # 重启服务
            print(f"Restarting {target}")
        elif action_name == 'scale':
            # 扩缩容
            replicas = action.get('parameters', {}).get('replicas')
            print(f"Scaling {target} to {replicas} replicas")
            
    def _send_to_channel(self, channel: Dict[str, Any], alert: Dict[str, Any]) -> None:
        """发送到指定通道"""
        channel_type = channel.get('type')
        
        if channel_type == 'slack':
            self._send_to_slack(channel, alert)
        elif channel_type == 'email':
            self._send_to_email(channel, alert)
        elif channel_type == 'pagerduty':
            self._send_to_pagerduty(channel, alert)
            
    def _send_to_slack(self, channel: Dict[str, Any], alert: Dict[str, Any]) -> None:
        """发送到Slack"""
        webhook_url = channel.get('webhook_url')
        channel_name = channel.get('channel')
        
        message = {
            "channel": channel_name,
            "text": f"Alert: {alert.get('summary')}",
            "attachments": [
                {
                    "color": "danger" if alert.get('severity') == 'critical' else "warning",
                    "fields": [
                        {
                            "title": "Service",
                            "value": alert.get('labels', {}).get('service', 'Unknown'),
                            "short": True
                        },
                        {
                            "title": "Severity",
                            "value": alert.get('severity', 'Unknown'),
                            "short": True
                        }
                    ]
                }
            ]
        }
        
        requests.post(webhook_url, json=message)
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - alert.name
    - alert.description
    - alert.version
    - alert.rule
  
  type_constraints:
    - field: "alert.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "alert.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "alert.rule.severity"
      type: "string"
      enum: ["info", "warning", "critical", "emergency"]
```

### 6.2 告警验证规则

```yaml
alert_validation:
  rule_consistency:
    - rule: "expression must be valid PromQL"
    - rule: "duration must be positive"
    - rule: "severity must be valid"
  
  notification_validation:
    - rule: "all notification channels must be configured"
    - rule: "escalation levels must be sequential"
    - rule: "auto recovery conditions must be valid"
```

## 7. 最佳实践

### 7.1 告警设计模式

```dsl
# 基础告警模式
alert "basic_alert" {
  description: "基础告警"
  version: "1.0.0"
  
  rule: {
    expression: "metric > threshold"
    duration: "5m"
    severity: "warning"
  }
  
  labels: {
    service: "service-name"
    environment: "environment"
  }
  
  notification: {
    channels: [
      {
        name: "team-notification"
        type: "slack"
        channel: "#alerts"
      }
    ]
  }
}

# 智能告警模式
alert "smart_alert" {
  description: "智能告警"
  version: "1.0.0"
  
  rule: {
    expression: "anomaly_score > threshold"
    duration: "5m"
    severity: "warning"
  }
  
  ml_model: {
    enabled: true
    model_type: "isolation_forest"
    features: ["metric1", "metric2", "metric3"]
  }
  
  auto_recovery: {
    enabled: true
    conditions: [
      {
        expression: "metric < threshold"
        duration: "2m"
        action: "resolve_alert"
      }
    ]
  }
}
```

### 7.2 告警命名规范

```dsl
# 推荐命名模式
alert "service_component_condition" {
  # 服务_组件_条件
}

alert "environment_severity_metric" {
  # 环境_严重程度_指标
}

alert "team_domain_alert" {
  # 团队_领域_告警
}
```

## 8. 与主流标准的映射

| DSL元素 | Prometheus Alertmanager | PagerDuty | Zabbix Trigger | Nagios |
|---------|------------------------|-----------|----------------|--------|
| alert | group/rule | service | trigger | service |
| suppression | inhibit/silence | schedule | maintenance | downtime |
| notification | receiver | escalation | action | contact |
| escalation | route | escalation | escalation | escalation |
| auto_recovery | n/a | auto-resolve | recovery | recovery |

## 9. 工程实践示例

```dsl
# 生产环境告警配置示例
alert "production_web_service_critical" {
  description: "生产环境Web服务严重告警"
  version: "1.0.0"
  author: "system"
  
  rule: {
    expression: "up{service=\"web-service\", environment=\"production\"} == 0 OR http_response_time{service=\"web-service\", environment=\"production\"} > 5"
    duration: "2m"
    evaluation_interval: "15s"
    severity: "critical"
    priority: 1
  }
  
  labels: {
    service: "web-service"
    environment: "production"
    team: "frontend"
    component: "api"
    datacenter: "us-east-1"
  }
  
  annotations: {
    summary: "生产环境Web服务不可用"
    description: "服务 {{ $labels.service }} 在 {{ $labels.instance }} 上不可用，响应时间: {{ $value }}s"
    runbook_url: "https://runbook.example.com/production-service-unavailable"
    dashboard_url: "https://grafana.example.com/d/production-service-health"
    jira_ticket: "OPS-{{ $labels.service }}-{{ $labels.instance }}"
  }
  
  suppression: {
    enabled: true
    conditions: [
      {
        type: "time_window"
        condition: "hour >= 2 AND hour < 4"
        duration: "2h"
        reason: "计划维护窗口"
        approved_by: "ops-manager"
      },
      {
        type: "dependency"
        condition: "database_down OR load_balancer_down OR network_issue"
        duration: "until_dependency_resolved"
        reason: "依赖服务故障"
      },
      {
        type: "maintenance"
        condition: "maintenance_mode == true"
        duration: "until_maintenance_complete"
        reason: "维护模式"
      }
    ]
  }
  
  notification: {
    channels: [
      {
        name: "emergency-pager"
        type: "pagerduty"
        service: "web-service-production"
        urgency: "high"
        auto_resolve: false
        escalation_policy: "web-service-production-escalation"
        routing_key: "{{ pagerduty_routing_key }}"
      },
      {
        name: "slack-critical"
        type: "slack"
        channel: "#critical-alerts"
        template: "critical_production_alert"
        mentions: ["@here", "@oncall", "@ops-team"]
        webhook_url: "{{ slack_webhook_url }}"
      },
      {
        name: "email-notification"
        type: "email"
        recipients: ["ops@example.com", "dev@example.com", "manager@example.com"]
        template: "production_service_alert"
        cc: ["cto@example.com"]
        smtp_server: "{{ smtp_server }}"
      },
      {
        name: "sms-notification"
        type: "sms"
        recipients: ["+1234567890", "+0987654321"]
        template: "critical_alert_sms"
        provider: "twilio"
      }
    ]
    grouping: {
      enabled: true
      group_by: ["service", "environment", "datacenter"]
      group_wait: "10s"
      group_interval: "2m"
      repeat_interval: "1h"
      max_repeat_count: 5
    }
    routing: {
      enabled: true
      rules: [
        {
          condition: "environment == 'production' AND severity == 'critical'"
          channels: ["emergency-pager", "slack-critical", "sms-notification"]
          priority: 1
        },
        {
          condition: "environment == 'production' AND severity == 'warning'"
          channels: ["slack-critical", "email-notification"]
          priority: 2
        }
      ]
    }
  }
  
  escalation: {
    enabled: true
    levels: [
      {
        level: 1
        delay: "2m"
        notification: "emergency-pager"
        auto_actions: ["check_health", "restart_service", "scale_up"]
        on_call_rotation: "primary"
      },
      {
        level: 2
        delay: "5m"
        notification: "manager"
        auto_actions: ["failover", "rollback_deployment"]
        on_call_rotation: "secondary"
      },
      {
        level: 3
        delay: "10m"
        notification: "cto"
        auto_actions: ["emergency_deployment", "activate_disaster_recovery"]
        on_call_rotation: "emergency"
      }
    ]
    auto_escalation: {
      enabled: true
      conditions: [
        {
          expression: "alert_firing_duration > 15m"
          action: "escalate_to_next_level"
        },
        {
          expression: "notification_failure_count > 3"
          action: "escalate_to_emergency"
        }
      ]
    }
  }
  
  auto_recovery: {
    enabled: true
    conditions: [
      {
        expression: "up{service=\"web-service\", environment=\"production\"} == 1 AND http_response_time{service=\"web-service\", environment=\"production\"} < 2"
        duration: "1m"
        action: "resolve_alert"
        confidence: 0.9
      }
    ]
    actions: [
      {
        name: "check_health"
        type: "http"
        url: "https://{{ $labels.instance }}/health"
        method: "GET"
        timeout: "10s"
        expected_status: 200
        retry_count: 3
        retry_interval: "5s"
      },
      {
        name: "restart_service"
        type: "kubernetes"
        target: "deployment/web-service"
        action: "restart"
        namespace: "{{ $labels.namespace }}"
        timeout: "5m"
        rollback_on_failure: true
      },
      {
        name: "scale_up"
        type: "kubernetes"
        target: "deployment/web-service"
        action: "scale"
        parameters: {
          replicas: "{{ current_replicas + 3 }}"
          max_replicas: 20
        }
        timeout: "3m"
      },
      {
        name: "failover"
        type: "load_balancer"
        action: "disable_backend"
        target: "{{ $labels.instance }}"
        duration: "5m"
        health_check_interval: "30s"
      },
      {
        name: "rollback_deployment"
        type: "kubernetes"
        target: "deployment/web-service"
        action: "rollback"
        to_revision: "previous"
        timeout: "10m"
      }
    ]
    success_criteria: {
      health_check_passed: true
      response_time_improved: true
      error_rate_reduced: true
    }
  }
  
  correlation: {
    enabled: true
    rules: [
      {
        name: "multiple_services_down"
        condition: "count(up{service=~\".*\", environment=\"production\"} == 0) > 3"
        action: "escalate_to_level_3"
        reason: "多个生产服务同时不可用"
        severity: "emergency"
      },
      {
        name: "database_connection_issue"
        condition: "service_unavailable AND database_connection_errors > 10"
        action: "trigger_database_alert"
        reason: "数据库连接问题"
        severity: "critical"
      },
      {
        name: "network_issue"
        condition: "service_unavailable AND network_latency > 1000"
        action: "trigger_network_alert"
        reason: "网络延迟问题"
        severity: "critical"
      }
    ]
    deduplication: {
      enabled: true
      strategy: "similarity_based"
      similarity_threshold: 0.8
      time_window: "5m"
    }
  }
  
  metrics: {
    enabled: true
    collection: [
      "alert_firing_duration",
      "notification_sent_count",
      "escalation_triggered_count",
      "auto_recovery_success_rate",
      "mean_time_to_resolution",
      "false_positive_rate",
      "alert_noise_level"
    ]
    thresholds: {
      mttr_warning: "15m"
      mttr_critical: "30m"
      false_positive_warning: 0.1
      false_positive_critical: 0.2
    }
    dashboards: [
      "https://grafana.example.com/d/alert-metrics"
    ]
  }
  
  compliance: {
    enabled: true
    sla: {
      response_time: "5m"
      resolution_time: "30m"
      availability: 0.999
    }
    audit: {
      enabled: true
      log_all_actions: true
      retention_period: "1y"
    }
    reporting: {
      enabled: true
      frequency: "weekly"
      recipients: ["ops-manager@example.com", "cto@example.com"]
    }
  }
}
```

这个DSL设计为告警建模提供了完整的配置语言，支持基础告警、智能告警、告警聚合等多种模式，同时保持了良好的可扩展性和可维护性。
