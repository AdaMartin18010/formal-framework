# 指标建模DSL设计

## 设计目标

指标建模DSL旨在提供声明式语言定义复杂的监控指标配置，支持多种指标类型、聚合策略、告警规则、可视化配置，并与主流监控平台无缝集成。

## 基本语法

### 核心结构

```dsl
metrics_model "web_service_metrics" {
  description: "Web服务监控指标"
  version: "1.0.0"
  
  namespace: "web_service"
  labels: {
    service: "web-service"
    environment: "production"
    version: "1.0.0"
  }
  
  metrics: [
    {
      name: "http_requests_total"
      type: "counter"
      help: "Total number of HTTP requests"
      labels = ["method", "endpoint", "status_code"]
    }
  ]
  
  collection: {
    interval: "15s"
    timeout: "10s"
    retries: 3
  }
}
```

### 计数器指标

```dsl
counter_metric "http_requests_total" {
  description: "HTTP请求总数"
  
  type: "counter"
  help: "Total number of HTTP requests"
  
  labels: [
    {
      name: "method"
      values: ["GET", "POST", "PUT", "DELETE"]
      description: "HTTP method"
    },
    {
      name: "endpoint"
      description: "API endpoint"
    },
    {
      name: "status_code"
      values: ["200", "400", "401", "403", "404", "500"]
      description: "HTTP status code"
    },
    {
      name: "service"
      value: "web-service"
      description: "Service name"
    }
  ]
  
  collection: {
    source: "application"
    method: "increment"
    interval: "1s"
  }
  
  aggregation: [
    {
      name: "requests_per_second"
      type: "rate"
      window: "5m"
      labels: ["method", "endpoint"]
    },
    {
      name: "error_rate"
      type: "ratio"
      numerator: "status_code:5xx"
      denominator: "*"
      window: "5m"
    }
  ]
  
  alerting: [
    {
      name: "high_error_rate"
      condition: "error_rate > 0.05"
      duration: "2m"
      severity: "warning"
      labels: {
        alert_type: "error_rate"
        service: "web-service"
      }
    }
  ]
}
```

### 仪表盘指标

```dsl
gauge_metric "active_connections" {
  description: "活跃连接数"
  
  type: "gauge"
  help: "Number of active connections"
  
  labels: [
    {
      name: "connection_type"
      values: ["http", "websocket", "database"]
      description: "Type of connection"
    },
    {
      name: "service"
      value: "web-service"
      description: "Service name"
    }
  ]
  
  collection: {
    source: "application"
    method: "set"
    interval: "30s"
  }
  
  aggregation: [
    {
      name: "avg_connections"
      type: "avg"
      window: "5m"
      labels: ["connection_type"]
    },
    {
      name: "max_connections"
      type: "max"
      window: "5m"
      labels: ["connection_type"]
    }
  ]
  
  alerting: [
    {
      name: "too_many_connections"
      condition: "active_connections > 1000"
      duration: "1m"
      severity: "critical"
      labels: {
        alert_type: "connection_limit"
        service: "web-service"
      }
    }
  ]
}
```

### 直方图指标

```dsl
histogram_metric "http_request_duration_seconds" {
  description: "HTTP请求持续时间"
  
  type: "histogram"
  help: "HTTP request duration in seconds"
  
  buckets: [0.1, 0.25, 0.5, 1, 2.5, 5, 10, 30]
  
  labels: [
    {
      name: "method"
      values: ["GET", "POST", "PUT", "DELETE"]
      description: "HTTP method"
    },
    {
      name: "endpoint"
      description: "API endpoint"
    },
    {
      name: "service"
      value: "web-service"
      description: "Service name"
    }
  ]
  
  collection: {
    source: "application"
    method: "observe"
    interval: "1s"
  }
  
  aggregation: [
    {
      name: "p50_duration"
      type: "histogram_quantile"
      quantile: 0.5
      window: "5m"
      labels: ["method", "endpoint"]
    },
    {
      name: "p95_duration"
      type: "histogram_quantile"
      quantile: 0.95
      window: "5m"
      labels: ["method", "endpoint"]
    },
    {
      name: "p99_duration"
      type: "histogram_quantile"
      quantile: 0.99
      window: "5m"
      labels: ["method", "endpoint"]
    },
    {
      name: "avg_duration"
      type: "avg"
      window: "5m"
      labels: ["method", "endpoint"]
    }
  ]
  
  alerting: [
    {
      name: "high_latency"
      condition: "p95_duration > 2"
      duration: "2m"
      severity: "warning"
      labels: {
        alert_type: "latency"
        service: "web-service"
      }
    },
    {
      name: "very_high_latency"
      condition: "p99_duration > 5"
      duration: "1m"
      severity: "critical"
      labels: {
        alert_type: "latency"
        service: "web-service"
      }
    }
  ]
}
```

### 摘要指标

```dsl
summary_metric "database_query_duration_seconds" {
  description: "数据库查询持续时间"
  
  type: "summary"
  help: "Database query duration in seconds"
  
  quantiles: [0.5, 0.9, 0.95, 0.99]
  
  labels: [
    {
      name: "database"
      values: ["mysql", "postgresql", "redis"]
      description: "Database type"
    },
    {
      name: "operation"
      values: ["select", "insert", "update", "delete"]
      description: "Database operation"
    },
    {
      name: "service"
      value: "web-service"
      description: "Service name"
    }
  ]
  
  collection: {
    source: "application"
    method: "observe"
    interval: "1s"
  }
  
  aggregation: [
    {
      name: "avg_query_duration"
      type: "avg"
      window: "5m"
      labels: ["database", "operation"]
    },
    {
      name: "query_count"
      type: "count"
      window: "5m"
      labels: ["database", "operation"]
    }
  ]
  
  alerting: [
    {
      name: "slow_queries"
      condition: "avg_query_duration > 1"
      duration: "2m"
      severity: "warning"
      labels: {
        alert_type: "database_performance"
        service: "web-service"
      }
    }
  ]
}
```

## 高级用法

### 复合指标

```dsl
composite_metric "service_health_score" {
  description: "服务健康度评分"
  
  type: "composite"
  help: "Overall service health score (0-100)"
  
  components: [
    {
      name: "availability_score"
      weight: 0.4
      metric: "service_uptime_percentage"
      calculation: "value * 100"
    },
    {
      name: "performance_score"
      weight: 0.3
      metric: "response_time_score"
      calculation: "max(0, 100 - (p95_duration * 20))"
    },
    {
      name: "error_score"
      weight: 0.3
      metric: "error_rate"
      calculation: "max(0, 100 - (error_rate * 1000))"
    }
  ]
  
  calculation: "sum(component_score * weight)"
  
  labels: [
    {
      name: "service"
      value: "web-service"
      description: "Service name"
    },
    {
      name: "environment"
      values: ["production", "staging", "development"]
      description: "Environment"
    }
  ]
  
  alerting: [
    {
      name: "low_health_score"
      condition: "service_health_score < 80"
      duration: "5m"
      severity: "warning"
      labels: {
        alert_type: "health_score"
        service: "web-service"
      }
    },
    {
      name: "critical_health_score"
      condition: "service_health_score < 60"
      duration: "2m"
      severity: "critical"
      labels: {
        alert_type: "health_score"
        service: "web-service"
      }
    }
  ]
}
```

### 业务指标

```dsl
business_metric "order_processing_metrics" {
  description: "订单处理业务指标"
  
  namespace: "business"
  
  metrics: [
    {
      name: "orders_created_total"
      type: "counter"
      help: "Total number of orders created"
      labels: ["payment_method", "order_type", "customer_tier"]
    },
    {
      name: "orders_completed_total"
      type: "counter"
      help: "Total number of orders completed"
      labels: ["payment_method", "order_type", "customer_tier"]
    },
    {
      name: "order_value"
      type: "histogram"
      help: "Order value distribution"
      buckets: [10, 50, 100, 500, 1000, 5000, 10000]
      labels: ["payment_method", "order_type", "customer_tier"]
    },
    {
      name: "order_processing_duration"
      type: "histogram"
      help: "Order processing duration"
      buckets: [1, 5, 15, 30, 60, 300, 600]
      labels: ["payment_method", "order_type"]
    }
  ]
  
  derived_metrics: [
    {
      name: "order_success_rate"
      type: "ratio"
      numerator: "orders_completed_total"
      denominator: "orders_created_total"
      window: "1h"
      labels: ["payment_method", "order_type", "customer_tier"]
    },
    {
      name: "avg_order_value"
      type: "avg"
      metric: "order_value"
      window: "1h"
      labels: ["payment_method", "order_type", "customer_tier"]
    },
    {
      name: "order_processing_throughput"
      type: "rate"
      metric: "orders_completed_total"
      window: "5m"
      labels: ["payment_method", "order_type"]
    }
  ]
  
  alerting: [
    {
      name: "low_order_success_rate"
      condition: "order_success_rate < 0.95"
      duration: "10m"
      severity: "critical"
      labels: {
        alert_type: "business_impact"
        service: "order-service"
      }
    },
    {
      name: "high_order_processing_time"
      condition: "p95_order_processing_duration > 300"
      duration: "5m"
      severity: "warning"
      labels: {
        alert_type: "business_impact"
        service: "order-service"
      }
    }
  ]
}
```

### 分布式指标

```dsl
distributed_metric "distributed_service_metrics" {
  description: "分布式服务指标"
  
  topology: {
    type: "microservices"
    services: [
      {
        name: "api-gateway"
        instances: 3
        metrics: ["request_rate", "error_rate", "latency"]
      },
      {
        name: "user-service"
        instances: 2
        metrics: ["request_rate", "error_rate", "latency", "database_connections"]
      },
      {
        name: "order-service"
        instances: 2
        metrics: ["request_rate", "error_rate", "latency", "order_processing_time"]
      },
      {
        name: "payment-service"
        instances: 2
        metrics: ["request_rate", "error_rate", "latency", "payment_success_rate"]
      }
    ]
  }
  
  aggregation_strategies: [
    {
      name: "service_level"
      type: "sum"
      group_by: ["service"]
      metrics: ["request_rate", "error_rate"]
    },
    {
      name: "instance_level"
      type: "avg"
      group_by: ["service", "instance"]
      metrics: ["latency", "cpu_usage", "memory_usage"]
    },
    {
      name: "cluster_level"
      type: "sum"
      group_by: ["cluster"]
      metrics: ["total_requests", "total_errors"]
    }
  ]
  
  correlation: {
    enabled: true
    correlation_key: "trace_id"
    services: ["api-gateway", "user-service", "order-service", "payment-service"]
    time_window: "5m"
  }
  
  distributed_tracing: {
    enabled: true
    sampling_rate: 0.1
    metrics: [
      "trace_duration",
      "span_count",
      "error_spans"
    ]
  }
  
  alerting: [
    {
      name: "service_cascade_failure"
      condition: "error_rate > 0.1 AND correlation_impact > 0.5"
      duration: "2m"
      severity: "critical"
      labels: {
        alert_type: "distributed_failure"
        impact: "cascade"
      }
    }
  ]
}
```

## 代码生成模板

### Prometheus配置

```yaml
# 生成的Prometheus配置
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "web_service_alerts.yml"

scrape_configs:
  - job_name: 'web-service'
    static_configs:
      - targets: ['web-service:8080']
    metrics_path: '/metrics'
    scrape_interval: 15s
    scrape_timeout: 10s
    honor_labels: true
    labels:
      service: web-service
      environment: production
    metric_relabel_configs:
      - source_labels: [__name__]
        regex: 'http_requests_total'
        action: keep
      - source_labels: [method, endpoint, status_code]
        target_label: __tmp_labels
        regex: '(.+);(.+);(.+)'
        replacement: '${1},${2},${3}'

  - job_name: 'database'
    static_configs:
      - targets: ['mysql:3306', 'postgresql:5432', 'redis:6379']
    metrics_path: '/metrics'
    scrape_interval: 30s
    scrape_timeout: 15s
    labels:
      service: database
      environment: production

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093
      scheme: http
      timeout: 10s
      api_version: v1

# 告警规则
groups:
  - name: web_service_alerts
    rules:
      - alert: HighErrorRate
        expr: rate(http_requests_total{status_code=~"5.."}[5m]) / rate(http_requests_total[5m]) > 0.05
        for: 2m
        labels:
          severity: warning
          service: web-service
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value | humanizePercentage }}"

      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 2
        for: 2m
        labels:
          severity: warning
          service: web-service
        annotations:
          summary: "High latency detected"
          description: "95th percentile latency is {{ $value }}s"

      - alert: TooManyConnections
        expr: active_connections > 1000
        for: 1m
        labels:
          severity: critical
          service: web-service
        annotations:
          summary: "Too many active connections"
          description: "Active connections: {{ $value }}"
```

### Grafana仪表板

```json
// 生成的Grafana仪表板
{
  "dashboard": {
    "id": null,
    "title": "Web Service Metrics",
    "tags": ["web-service", "production"],
    "timezone": "browser",
    "panels": [
      {
        "id": 1,
        "title": "Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_requests_total[5m])",
            "legendFormat": "{{method}} {{endpoint}}"
          }
        ],
        "yAxes": [
          {
            "label": "Requests per second",
            "min": 0
          }
        ]
      },
      {
        "id": 2,
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_requests_total{status_code=~\"5..\"}[5m]) / rate(http_requests_total[5m])",
            "legendFormat": "Error Rate"
          }
        ],
        "yAxes": [
          {
            "label": "Error Rate",
            "min": 0,
            "max": 1,
            "format": "percent"
          }
        ]
      },
      {
        "id": 3,
        "title": "Response Time",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "P95"
          },
          {
            "expr": "histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "P99"
          }
        ],
        "yAxes": [
          {
            "label": "Response Time (seconds)",
            "min": 0
          }
        ]
      },
      {
        "id": 4,
        "title": "Active Connections",
        "type": "stat",
        "targets": [
          {
            "expr": "active_connections",
            "legendFormat": "Connections"
          }
        ],
        "fieldConfig": {
          "defaults": {
            "color": {
              "mode": "thresholds"
            },
            "thresholds": {
              "steps": [
                { "color": "green", "value": null },
                { "color": "yellow", "value": 500 },
                { "color": "red", "value": 1000 }
              ]
            }
          }
        }
      }
    ],
    "time": {
      "from": "now-1h",
      "to": "now"
    },
    "refresh": "30s"
  }
}
```

### Python实现

```python
import time
import random
from prometheus_client import Counter, Gauge, Histogram, Summary, generate_latest, CONTENT_TYPE_LATEST
from flask import Flask, Response

app = Flask(__name__)

# 定义指标
http_requests_total = Counter(
    'http_requests_total',
    'Total number of HTTP requests',
    ['method', 'endpoint', 'status_code', 'service']
)

active_connections = Gauge(
    'active_connections',
    'Number of active connections',
    ['connection_type', 'service']
)

http_request_duration_seconds = Histogram(
    'http_request_duration_seconds',
    'HTTP request duration in seconds',
    ['method', 'endpoint', 'service'],
    buckets=[0.1, 0.25, 0.5, 1, 2.5, 5, 10, 30]
)

database_query_duration_seconds = Summary(
    'database_query_duration_seconds',
    'Database query duration in seconds',
    ['database', 'operation', 'service']
)

# 模拟数据收集
def collect_metrics():
    """收集指标数据"""
    while True:
        # 模拟HTTP请求
        methods = ['GET', 'POST', 'PUT', 'DELETE']
        endpoints = ['/api/users', '/api/orders', '/api/products']
        status_codes = ['200', '400', '401', '403', '404', '500']
        
        method = random.choice(methods)
        endpoint = random.choice(endpoints)
        status_code = random.choice(status_codes)
        
        # 增加请求计数
        http_requests_total.labels(
            method=method,
            endpoint=endpoint,
            status_code=status_code,
            service='web-service'
        ).inc()
        
        # 模拟连接数
        connection_types = ['http', 'websocket', 'database']
        for conn_type in connection_types:
            connections = random.randint(10, 100)
            active_connections.labels(
                connection_type=conn_type,
                service='web-service'
            ).set(connections)
        
        time.sleep(1)

# 模拟HTTP请求处理
@app.route('/api/<path:endpoint>')
def handle_request(endpoint):
    start_time = time.time()
    
    # 模拟处理时间
    processing_time = random.uniform(0.1, 2.0)
    time.sleep(processing_time)
    
    # 记录请求持续时间
    http_request_duration_seconds.labels(
        method='GET',
        endpoint=f'/api/{endpoint}',
        service='web-service'
    ).observe(processing_time)
    
    # 模拟数据库查询
    databases = ['mysql', 'postgresql', 'redis']
    operations = ['select', 'insert', 'update', 'delete']
    
    db = random.choice(databases)
    operation = random.choice(operations)
    query_time = random.uniform(0.01, 0.5)
    
    database_query_duration_seconds.labels(
        database=db,
        operation=operation,
        service='web-service'
    ).observe(query_time)
    
    return {'status': 'success', 'endpoint': endpoint}

# Prometheus指标端点
@app.route('/metrics')
def metrics():
    return Response(generate_latest(), mimetype=CONTENT_TYPE_LATEST)

# 健康检查端点
@app.route('/health')
def health():
    return {'status': 'healthy'}

if __name__ == '__main__':
    import threading
    
    # 启动指标收集线程
    metrics_thread = threading.Thread(target=collect_metrics, daemon=True)
    metrics_thread.start()
    
    # 启动Flask应用
    app.run(host='0.0.0.0', port=8080, debug=False)
```

## 验证规则

### 语法验证

```dsl
validation_rules "metrics_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "version", "namespace", "metrics"]
      message: "必须包含描述、版本、命名空间和指标"
    },
    {
      rule: "valid_metric_type"
      allowed_types: ["counter", "gauge", "histogram", "summary"]
      message: "指标类型必须是支持的类型"
    },
    {
      rule: "valid_label_names"
      condition: "label names match regex [a-zA-Z_][a-zA-Z0-9_]*"
      message: "标签名称必须符合命名规范"
    }
  ]
  
  semantic: [
    {
      rule: "metric_uniqueness"
      condition: "metric names are unique within namespace"
      message: "指标名称在命名空间内必须唯一"
    },
    {
      rule: "label_consistency"
      condition: "labels are consistent across related metrics"
      message: "相关指标的标签必须一致"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "metrics_performance" {
  constraints: [
    {
      metric: "collection_latency"
      threshold: "100ms"
      action: "warn"
    },
    {
      metric: "storage_usage"
      threshold: "1GB"
      action: "error"
    },
    {
      metric: "cardinality"
      threshold: "10000"
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "label_optimization"
      enabled: true
      max_labels: 10
    },
    {
      strategy: "sampling"
      enabled: true
      rate: 0.1
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "metrics_patterns" {
  patterns: [
    {
      name: "four_golden_signals"
      description: "四个黄金信号模式"
      implementation: {
        metrics: ["latency", "traffic", "errors", "saturation"]
        alerting: "based_on_slos"
        visualization: "dashboard_focused"
      }
    },
    {
      name: "red_yellow_green"
      description: "红黄绿状态模式"
      implementation: {
        thresholds: {
          green: "0-80%",
          yellow: "80-95%",
          red: "95-100%"
        }
        alerting: "progressive"
      }
    },
    {
      name: "metric_hierarchy"
      description: "指标层次结构模式"
      implementation: {
        levels: ["business", "application", "infrastructure"]
        aggregation: "hierarchical"
        drill_down: "enabled"
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "over_metricization"
      description: "过度指标化"
      symptoms: ["high_cardinality", "storage_explosion"]
      solution: "reduce_labels"
    },
    {
      name: "under_metricization"
      description: "指标不足"
      symptoms: ["poor_visibility", "reactive_monitoring"]
      solution: "add_critical_metrics"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "metrics_monitoring" {
  metrics: [
    {
      name: "metric_collection_rate"
      type: "counter"
      labels: ["metric_name", "status"]
      unit: "metrics/sec"
    },
    {
      name: "metric_storage_usage"
      type: "gauge"
      labels: ["namespace"]
      unit: "bytes"
    },
    {
      name: "metric_cardinality"
      type: "gauge"
      labels: ["metric_name"]
    }
  ]
  
  alerts: [
    {
      name: "metric_collection_failure"
      condition: "collection_errors > 0"
      severity: "critical"
      action: "restart_collector"
    },
    {
      name: "high_cardinality"
      condition: "metric_cardinality > 10000"
      severity: "warning"
      action: "optimize_labels"
    }
  ]
}
```

## 主流标准映射

### Prometheus集成

```dsl
prometheus_integration "prometheus_metrics" {
  metrics: [
    {
      name: "metric_collection_duration_seconds"
      type: "histogram"
      help: "Metric collection execution time"
      labels: ["metric_name", "status"]
    },
    {
      name: "metric_storage_bytes"
      type: "gauge"
      help: "Metric storage usage in bytes"
      labels: ["namespace", "metric_name"]
    },
    {
      name: "metric_cardinality_total"
      type: "gauge"
      help: "Total metric cardinality"
      labels: ["metric_name"]
    }
  ]
  
  rules: [
    {
      name: "High Metric Cardinality"
      expr: "metric_cardinality_total > 10000"
      for: "5m"
      labels: { severity: warning }
      annotations: { summary: "High metric cardinality detected" }
    },
    {
      name: "Metric Collection Failure"
      expr: "rate(metric_collection_errors_total[5m]) > 0"
      for: "1m"
      labels: { severity: critical }
      annotations: { summary: "Metric collection is failing" }
    }
  ]
  
  alertmanager: {
    receivers: [
      {
        name: "slack"
        slack_configs: [
          {
            channel: "#alerts"
            title: "Metrics Alert"
            text: "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}"
          }
        ]
      }
    ]
  }
}
```

## 工程实践示例

### 微服务指标

```dsl
microservice_metrics "order_service_metrics" {
  description: "订单服务指标"
  
  namespace: "order_service"
  
  services: [
    {
      name: "order-service"
      instances: 3
      metrics: [
        {
          name: "order_requests_total"
          type: "counter"
          labels: ["method", "endpoint", "status_code"]
        },
        {
          name: "order_processing_duration"
          type: "histogram"
          buckets: [1, 5, 15, 30, 60, 300]
          labels: ["order_type", "payment_method"]
        },
        {
          name: "active_orders"
          type: "gauge"
          labels: ["order_status"]
        }
      ]
    },
    {
      name: "payment-service"
      instances: 2
      metrics: [
        {
          name: "payment_requests_total"
          type: "counter"
          labels: ["payment_method", "status"]
        },
        {
          name: "payment_processing_duration"
          type: "histogram"
          buckets: [0.1, 0.5, 1, 2, 5, 10]
          labels: ["payment_method"]
        },
        {
          name: "payment_success_rate"
          type: "gauge"
          labels: ["payment_method"]
        }
      ]
    },
    {
      name: "inventory-service"
      instances: 2
      metrics: [
        {
          name: "inventory_operations_total"
          type: "counter"
          labels: ["operation", "status"]
        },
        {
          name: "inventory_level"
          type: "gauge"
          labels: ["product_category"]
        }
      ]
    }
  ]
  
  business_metrics: [
    {
      name: "order_success_rate"
      type: "ratio"
      numerator: "order_requests_total{status_code=\"200\"}"
      denominator: "order_requests_total"
      window: "5m"
    },
    {
      name: "avg_order_value"
      type: "avg"
      metric: "order_value"
      window: "1h"
    },
    {
      name: "order_throughput"
      type: "rate"
      metric: "order_requests_total{status_code=\"200\"}"
      window: "5m"
    }
  ]
  
  slos: [
    {
      name: "order_availability"
      target: 0.999
      window: "30d"
      metric: "order_success_rate"
    },
    {
      name: "order_latency"
      target: 0.95
      window: "30d"
      metric: "p95_order_processing_duration"
      threshold: 30
    }
  ]
  
  alerting: [
    {
      name: "order_service_down"
      condition: "up{service=\"order-service\"} == 0"
      duration: "1m"
      severity: "critical"
      notification: "pagerduty"
    },
    {
      name: "high_order_error_rate"
      condition: "order_success_rate < 0.95"
      duration: "5m"
      severity: "warning"
      notification: "slack"
    },
    {
      name: "slow_order_processing"
      condition: "p95_order_processing_duration > 60"
      duration: "2m"
      severity: "warning"
      notification: "slack"
    }
  ]
  
  visualization: {
    dashboards: [
      {
        name: "Order Service Overview"
        panels: [
          {
            title: "Order Success Rate"
            type: "graph"
            metric: "order_success_rate"
            thresholds: [0.95, 0.99]
          },
          {
            title: "Order Processing Time"
            type: "graph"
            metric: "p95_order_processing_duration"
            thresholds: [30, 60]
          },
          {
            title: "Order Throughput"
            type: "graph"
            metric: "order_throughput"
          }
        ]
      }
    ]
  }
}
```

### 实时流指标

```dsl
stream_metrics "real_time_metrics" {
  description: "实时流指标"
  
  streaming: {
    engine: "kafka_streams"
    mode: "real_time"
    parallelism: 8
  }
  
  sources: [
    {
      name: "application_logs"
      type: "kafka"
      topic: "application-logs"
      consumer_group: "metrics-processor"
      auto_offset_reset: "latest"
    },
    {
      name: "system_metrics"
      type: "kafka"
      topic: "system-metrics"
      consumer_group: "metrics-processor"
      auto_offset_reset: "latest"
    }
  ]
  
  processing: [
    {
      name: "log_metrics_extraction"
      type: "stream_processor"
      input: "application_logs"
      output: "extracted_metrics"
      operations: [
        {
          type: "parse_json"
          field: "message"
        },
        {
          type: "extract_metrics"
          patterns: [
            {
              name: "http_request"
              pattern: "HTTP request: {method} {endpoint} {status_code} {duration}"
              metrics: [
                {
                  name: "http_requests_total"
                  type: "counter"
                  labels: ["method", "endpoint", "status_code"]
                },
                {
                  name: "http_request_duration"
                  type: "histogram"
                  field: "duration"
                  labels: ["method", "endpoint"]
                }
              ]
            }
          ]
        }
      ]
    },
    {
      name: "system_metrics_aggregation"
      type: "stream_processor"
      input: "system_metrics"
      output: "aggregated_metrics"
      operations: [
        {
          type: "window"
          size: "1m"
          slide: "10s"
        },
        {
          type: "aggregate"
          metrics: [
            {
              name: "cpu_usage_avg"
              type: "avg"
              field: "cpu_usage"
            },
            {
              name: "memory_usage_avg"
              type: "avg"
              field: "memory_usage"
            },
            {
              name: "disk_usage_avg"
              type: "avg"
              field: "disk_usage"
            }
          ]
        }
      ]
    },
    {
      name: "anomaly_detection"
      type: "stream_processor"
      input: ["extracted_metrics", "aggregated_metrics"]
      output: "anomaly_alerts"
      operations: [
        {
          type: "anomaly_detection"
          algorithm: "z_score"
          fields: ["error_rate", "cpu_usage_avg", "memory_usage_avg"]
          threshold: 3.0
        },
        {
          type: "alert_generation"
          severity_mapping: {
            low: { threshold: 2.0, actions: ["notify"] },
            medium: { threshold: 3.0, actions: ["notify", "escalate"] },
            high: { threshold: 5.0, actions: ["notify", "escalate", "page"] }
          }
        }
      ]
    }
  ]
  
  outputs: [
    {
      name: "prometheus_sink"
      type: "prometheus"
      topic: "processed_metrics"
      endpoint: "http://prometheus:9090"
      batch_size: 100
      flush_interval: "10s"
    },
    {
      name: "alert_sink"
      type: "multiple"
      outputs: [
        {
          type: "kafka"
          topic: "alert-stream"
          endpoint: "kafka:9092"
          acks: "all"
          compression: "snappy"
        },
        {
          type: "slack"
          webhook_url: "https://hooks.slack.com/services/xxx"
          channel: "#alerts"
        },
        {
          type: "pagerduty"
          api_key: "xxx"
          service_id: "xxx"
        }
      ]
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
      "processing_latency",
      "throughput",
      "error_rate",
      "alert_count",
      "anomaly_detection_accuracy",
      "memory_usage",
      "cpu_usage"
    ]
    health_checks: [
      "kafka_connectivity",
      "prometheus_connectivity",
      "processing_pipeline_health"
    ]
    alerting: {
      on_high_latency: {
        threshold: "100ms"
        severity: "warning"
      }
      on_high_error_rate: {
        threshold: 0.01
        severity: "critical"
      }
      on_high_memory_usage: {
        threshold: 0.9
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

这个DSL设计提供了完整的指标建模能力，支持多种指标类型、聚合策略、告警规则、可视化配置，并能够与主流监控平台无缝集成。
