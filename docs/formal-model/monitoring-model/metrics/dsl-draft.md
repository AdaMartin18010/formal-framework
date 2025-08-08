# 监控指标DSL草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述监控指标、告警规则、仪表盘、报表等要素，支持递归组合与嵌套
- 支持自动生成Prometheus、Grafana、Datadog等主流监控平台配置
- 支持权限、安全、审计、AI自动化等高级特性

## 2. 基本语法结构

```dsl
metric "http_request_duration" {
  type = "histogram"
  unit = "seconds"
  description = "HTTP请求持续时间"
  labels = ["method", "endpoint", "status_code"]
  buckets = [0.1, 0.5, 1.0, 2.0, 5.0]
}

alert "high_error_rate" {
  condition = "error_rate > 0.05"
  duration = "5m"
  severity = "critical"
  message = "错误率超过5%"
}

dashboard "api_monitoring" {
  title = "API监控仪表盘"
  refresh = "30s"
  panels = [
    "request_rate",
    "error_rate", 
    "response_time",
    "throughput"
  ]
}
```

## 3. 关键元素

- metric：监控指标定义
- alert：告警规则定义
- dashboard：仪表盘定义
- query：查询表达式
- aggregation：聚合函数
- threshold：阈值设置
- notification：通知配置

## 4. 高级用法与递归扩展

### 4.1 复合指标与派生指标

```dsl
metric "error_rate" {
  type = "gauge"
  unit = "percentage"
  description = "错误率"
  expression = "error_count / total_count * 100"
  source_metrics = ["error_count", "total_count"]
}

metric "availability" {
  type = "gauge"
  unit = "percentage"
  description = "服务可用性"
  expression = "(total_requests - error_requests) / total_requests * 100"
  source_metrics = ["total_requests", "error_requests"]
}
```

### 4.2 多维度告警规则

```dsl
alert "service_degradation" {
  condition = "response_time_p95 > 2.0 OR error_rate > 0.1"
  duration = "3m"
  severity = "warning"
  message = "服务性能下降"
  labels = ["service", "environment"]
  
  escalation {
    after = "10m"
    severity = "critical"
    notify = ["oncall", "manager"]
  }
}

alert "business_impact" {
  condition = "order_success_rate < 0.95"
  duration = "1m"
  severity = "critical"
  message = "业务影响：订单成功率下降"
  business_impact = "high"
  sla_breach = true
}
```

### 4.3 智能仪表盘配置

```dsl
dashboard "microservices_overview" {
  title = "微服务概览"
  refresh = "30s"
  time_range = "6h"
  
  panels {
    "service_health" {
      type = "status"
      metrics = ["availability", "response_time", "error_rate"]
      thresholds = {
        green = "availability > 0.99"
        yellow = "availability > 0.95"
        red = "availability <= 0.95"
      }
    }
    
    "traffic_flow" {
      type = "graph"
      metrics = ["request_rate", "throughput"]
      visualization = "line_chart"
      stacked = false
    }
    
    "error_analysis" {
      type = "table"
      metrics = ["error_count", "error_rate"]
      group_by = ["service", "endpoint", "error_type"]
      sort_by = "error_count desc"
    }
  }
}
```

### 4.4 AI自动化与智能监控

```dsl
# 支持AI自动生成监控规则
ai_monitoring "为电商系统自动生成关键业务指标监控" {
  domain = "ecommerce"
  business_metrics = ["order_rate", "payment_success", "user_engagement"]
  technical_metrics = ["response_time", "error_rate", "throughput"]
  auto_optimize = true
}

# 智能异常检测
anomaly_detection "traffic_anomaly" {
  method = "machine_learning"
  algorithm = "isolation_forest"
  training_window = "30d"
  sensitivity = "medium"
  metrics = ["request_rate", "response_time", "error_rate"]
}
```

## 5. 与主流标准的映射

### 5.1 Prometheus映射

```dsl
# DSL定义
metric "http_requests_total" {
  type = "counter"
  description = "HTTP请求总数"
  labels = ["method", "endpoint", "status"]
}

# 映射到Prometheus
# http_requests_total{method="GET",endpoint="/api/users",status="200"}
```

### 5.2 Grafana映射

```dsl
# DSL定义
dashboard "service_monitoring" {
  title = "服务监控"
  panels = ["response_time", "error_rate", "throughput"]
}

# 映射到Grafana JSON
{
  "dashboard": {
    "title": "服务监控",
    "panels": [
      {"title": "响应时间", "targets": [...]},
      {"title": "错误率", "targets": [...]},
      {"title": "吞吐量", "targets": [...]}
    ]
  }
}
```

### 5.3 Datadog映射

```dsl
# DSL定义
alert "high_cpu_usage" {
  condition = "avg:system.cpu.user{*} > 80"
  duration = "5m"
  severity = "warning"
}

# 映射到Datadog
{
  "name": "High CPU Usage",
  "query": "avg:system.cpu.user{*} > 80",
  "message": "CPU使用率过高",
  "type": "metric alert"
}
```

## 6. 递归扩展建议

### 6.1 多层级监控

```dsl
monitoring_hierarchy {
  level_1: "infrastructure" {
    metrics = ["cpu", "memory", "disk", "network"]
  }
  
  level_2: "application" {
    metrics = ["response_time", "error_rate", "throughput"]
  }
  
  level_3: "business" {
    metrics = ["order_rate", "revenue", "user_engagement"]
  }
  
  level_4: "user_experience" {
    metrics = ["page_load_time", "user_satisfaction", "conversion_rate"]
  }
}
```

### 6.2 智能告警优化

```dsl
smart_alerting {
  adaptive_thresholds = true
  machine_learning = true
  context_aware = true
  
  rules {
    "business_hours" {
      time_range = "09:00-18:00"
      sensitivity = "high"
    }
    
    "off_hours" {
      time_range = "18:00-09:00"
      sensitivity = "low"
    }
  }
}
```

## 7. 工程实践示例

### 7.1 微服务监控配置

```dsl
service_monitoring "user_service" {
  metrics {
    "request_count" {
      type = "counter"
      labels = ["method", "endpoint", "status"]
    }
    
    "request_duration" {
      type = "histogram"
      buckets = [0.1, 0.5, 1.0, 2.0, 5.0]
    }
    
    "active_connections" {
      type = "gauge"
    }
  }
  
  alerts {
    "high_latency" {
      condition = "request_duration_p95 > 2.0"
      duration = "5m"
      severity = "warning"
    }
    
    "service_down" {
      condition = "request_count == 0"
      duration = "1m"
      severity = "critical"
    }
  }
  
  dashboard {
    title = "用户服务监控"
    panels = ["request_rate", "response_time", "error_rate", "active_connections"]
  }
}
```

### 7.2 业务指标监控

```dsl
business_monitoring "ecommerce" {
  metrics {
    "order_rate" {
      type = "counter"
      description = "订单创建速率"
      business_impact = "high"
    }
    
    "payment_success_rate" {
      type = "gauge"
      description = "支付成功率"
      expression = "successful_payments / total_payments * 100"
    }
    
    "revenue_per_hour" {
      type = "gauge"
      description = "每小时收入"
      currency = "USD"
    }
  }
  
  alerts {
    "revenue_drop" {
      condition = "revenue_per_hour < threshold"
      duration = "30m"
      severity = "critical"
      business_impact = "high"
    }
  }
}
```

### 7.3 基础设施监控

```dsl
infrastructure_monitoring "production_cluster" {
  metrics {
    "cpu_usage" {
      type = "gauge"
      unit = "percentage"
      aggregation = "avg"
    }
    
    "memory_usage" {
      type = "gauge"
      unit = "percentage"
      aggregation = "avg"
    }
    
    "disk_usage" {
      type = "gauge"
      unit = "percentage"
      aggregation = "max"
    }
    
    "network_throughput" {
      type = "gauge"
      unit = "bytes_per_second"
      aggregation = "sum"
    }
  }
  
  alerts {
    "high_cpu" {
      condition = "cpu_usage > 80"
      duration = "5m"
      severity = "warning"
    }
    
    "disk_full" {
      condition = "disk_usage > 90"
      duration = "1m"
      severity = "critical"
    }
  }
}
```

## 8. 最佳实践

### 8.1 指标命名规范

```dsl
naming_conventions {
  format = "{domain}_{object}_{action}_{unit}"
  examples = [
    "http_requests_total",
    "database_connections_active",
    "cache_hit_ratio_percent",
    "api_response_time_seconds"
  ]
}
```

### 8.2 告警设计原则

```dsl
alerting_principles {
  actionable = true
  specific = true
  contextual = true
  
  rules {
    "avoid_noise" {
      condition = "min_occurrences > 3"
      duration = "5m"
    }
    
    "escalation" {
      auto_escalate = true
      escalation_delay = "10m"
    }
  }
}
```

### 8.3 仪表盘设计

```dsl
dashboard_design {
  principles = [
    "one_purpose_per_dashboard",
    "logical_grouping",
    "consistent_visualization",
    "appropriate_refresh_rate"
  ]
  
  layout {
    grid_size = "12x12"
    responsive = true
    mobile_friendly = true
  }
}
```

---

> 本文档持续递归完善，欢迎补充更多监控指标DSL示例、最佳实践、工具集成等内容。
