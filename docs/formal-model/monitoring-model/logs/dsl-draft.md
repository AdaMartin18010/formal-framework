# 日志建模DSL草案

## 1. 设计目标

- 用声明式语法描述日志采集、解析、存储、查询、分析等流程
- 支持多源异构日志统一建模
- 便于自动生成采集/分析配置
- 支持日志聚合、过滤、转换、告警等高级特性

## 2. 基本语法结构

```dsl
log "web_application_logs" {
  description: "Web应用日志"
  version: "1.0.0"
  author: "system"
  
  source: {
    type: "file"
    path: "/var/log/webapp/app.log"
    format: "json"
    encoding: "utf-8"
    level: ["INFO", "WARN", "ERROR", "FATAL"]
    rotation: {
      enabled: true
      max_size: "100MB"
      max_files: 10
      compress: true
    }
  }
  
  parsing: {
    enabled: true
    format: "json"
    fields: [
      {
        name: "timestamp"
        type: "datetime"
        format: "ISO8601"
        required: true
      },
      {
        name: "level"
        type: "string"
        enum: ["DEBUG", "INFO", "WARN", "ERROR", "FATAL"]
        required: true
      },
      {
        name: "message"
        type: "string"
        required: true
      },
      {
        name: "trace_id"
        type: "string"
        required: false
      },
      {
        name: "user_id"
        type: "string"
        required: false
      },
      {
        name: "request_id"
        type: "string"
        required: false
      },
      {
        name: "service"
        type: "string"
        default: "web-service"
      },
      {
        name: "environment"
        type: "string"
        default: "production"
      }
    ]
  }
  
  filtering: {
    enabled: true
    rules: [
      {
        name: "exclude_debug"
        condition: "level != 'DEBUG'"
        action: "include"
      },
      {
        name: "include_errors"
        condition: "level in ['ERROR', 'FATAL']"
        action: "include"
      }
    ]
  }
  
  transformation: {
    enabled: true
    rules: [
      {
        name: "add_timestamp"
        action: "set_field"
        field: "timestamp"
        value: "{{ current_timestamp }}"
        condition: "timestamp == null"
      },
      {
        name: "add_service_info"
        action: "set_field"
        field: "service"
        value: "web-service"
      },
      {
        name: "add_environment"
        action: "set_field"
        field: "environment"
        value: "production"
      }
    ]
  }
  
  storage: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    index: "webapp-logs"
    index_pattern: "webapp-logs-{YYYY.MM.DD}"
    shards: 3
    replicas: 1
    retention: "30d"
    compression: true
  }
  
  alerting: {
    enabled: true
    rules: [
      {
        name: "high_error_rate"
        condition: "count(level='ERROR') > 10 in 5m"
        action: "notify"
        notification: "slack"
        channel: "#alerts"
      },
      {
        name: "critical_errors"
        condition: "level='FATAL'"
        action: "notify"
        notification: "pagerduty"
        urgency: "high"
      }
    ]
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "log_volume",
      "error_rate",
      "response_time",
      "throughput"
    ]
    dashboards: [
      "https://grafana.example.com/d/webapp-logs"
    ]
  }
}
```

## 3. 关键元素

- log：日志声明
- description：描述信息
- version：版本号
- author：作者
- source：日志源配置
- parsing：解析配置
- filtering：过滤规则
- transformation：转换规则
- storage：存储配置
- alerting：告警配置
- monitoring：监控配置

## 4. 高级用法

### 4.1 多源日志聚合

```dsl
log "distributed_system_logs" {
  description: "分布式系统日志"
  version: "1.0.0"
  author: "system"
  
  sources: [
    {
      name: "web_service"
      type: "file"
      path: "/var/log/web-service/app.log"
      format: "json"
      level: ["INFO", "WARN", "ERROR", "FATAL"]
    },
    {
      name: "api_service"
      type: "file"
      path: "/var/log/api-service/app.log"
      format: "json"
      level: ["INFO", "WARN", "ERROR", "FATAL"]
    },
    {
      name: "database_service"
      type: "file"
      path: "/var/log/db-service/app.log"
      format: "json"
      level: ["INFO", "WARN", "ERROR", "FATAL"]
    },
    {
      name: "cache_service"
      type: "file"
      path: "/var/log/cache-service/app.log"
      format: "json"
      level: ["INFO", "WARN", "ERROR", "FATAL"]
    }
  ]
  
  parsing: {
    enabled: true
    format: "json"
    fields: [
      {
        name: "timestamp"
        type: "datetime"
        format: "ISO8601"
        required: true
      },
      {
        name: "level"
        type: "string"
        enum: ["DEBUG", "INFO", "WARN", "ERROR", "FATAL"]
        required: true
      },
      {
        name: "message"
        type: "string"
        required: true
      },
      {
        name: "service"
        type: "string"
        required: true
      },
      {
        name: "trace_id"
        type: "string"
        required: false
      },
      {
        name: "request_id"
        type: "string"
        required: false
      },
      {
        name: "user_id"
        type: "string"
        required: false
      },
      {
        name: "environment"
        type: "string"
        default: "production"
      },
      {
        name: "datacenter"
        type: "string"
        default: "us-east-1"
      }
    ]
  }
  
  correlation: {
    enabled: true
    correlation_fields: [
      "trace_id",
      "request_id",
      "user_id"
    ]
    time_window: "5m"
  }
  
  aggregation: {
    enabled: true
    rules: [
      {
        name: "error_summary"
        condition: "level in ['ERROR', 'FATAL']"
        group_by: ["service", "level", "hour"]
        aggregation: "count"
        time_window: "1h"
      },
      {
        name: "performance_summary"
        condition: "message contains 'response_time'"
        group_by: ["service", "endpoint"]
        aggregation: "avg"
        field: "response_time"
        time_window: "5m"
      }
    ]
  }
  
  storage: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    index: "distributed-logs"
    index_pattern: "distributed-logs-{YYYY.MM.DD}"
    shards: 5
    replicas: 2
    retention: "90d"
    compression: true
    lifecycle_policy: {
      enabled: true
      hot_retention: "7d"
      warm_retention: "30d"
      cold_retention: "90d"
      delete_after: "365d"
    }
  }
  
  alerting: {
    enabled: true
    rules: [
      {
        name: "service_down"
        condition: "count(service='{service}') == 0 in 5m"
        action: "notify"
        notification: "pagerduty"
        urgency: "high"
      },
      {
        name: "high_error_rate"
        condition: "count(level='ERROR') > 50 in 10m"
        action: "notify"
        notification: "slack"
        channel: "#alerts"
      },
      {
        name: "performance_degradation"
        condition: "avg(response_time) > 2s in 5m"
        action: "notify"
        notification: "slack"
        channel: "#performance"
      }
    ]
  }
}
```

### 4.2 结构化日志分析

```dsl
log "business_events" {
  description: "业务事件日志"
  version: "1.0.0"
  author: "system"
  
  source: {
    type: "kafka"
    topic: "business-events"
    format: "json"
    consumer_group: "log-processor"
    auto_offset_reset: "latest"
  }
  
  parsing: {
    enabled: true
    format: "json"
    fields: [
      {
        name: "timestamp"
        type: "datetime"
        format: "ISO8601"
        required: true
      },
      {
        name: "event_type"
        type: "string"
        enum: ["user_registered", "order_created", "payment_processed", "order_shipped"]
        required: true
      },
      {
        name: "user_id"
        type: "string"
        required: true
      },
      {
        name: "session_id"
        type: "string"
        required: false
      },
      {
        name: "order_id"
        type: "string"
        required: false
      },
      {
        name: "amount"
        type: "number"
        required: false
      },
      {
        name: "currency"
        type: "string"
        default: "USD"
      },
      {
        name: "metadata"
        type: "object"
        required: false
      }
    ]
  }
  
  enrichment: {
    enabled: true
    rules: [
      {
        name: "add_user_info"
        action: "lookup"
        source: "user_service"
        key: "user_id"
        fields: ["user_type", "registration_date", "country"]
      },
      {
        name: "add_order_info"
        action: "lookup"
        source: "order_service"
        key: "order_id"
        fields: ["order_status", "items_count", "shipping_address"]
        condition: "event_type in ['order_created', 'order_shipped']"
      }
    ]
  }
  
  analytics: {
    enabled: true
    metrics: [
      {
        name: "user_registration_rate"
        condition: "event_type='user_registered'"
        aggregation: "count"
        group_by: ["hour", "country"]
        time_window: "1h"
      },
      {
        name: "order_conversion_rate"
        condition: "event_type='order_created'"
        aggregation: "count"
        group_by: ["day", "user_type"]
        time_window: "1d"
      },
      {
        name: "average_order_value"
        condition: "event_type='order_created'"
        aggregation: "avg"
        field: "amount"
        group_by: ["day", "currency"]
        time_window: "1d"
      }
    ]
  }
  
  storage: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    index: "business-events"
    index_pattern: "business-events-{YYYY.MM.DD}"
    shards: 3
    replicas: 1
    retention: "365d"
  }
  
  alerting: {
    enabled: true
    rules: [
      {
        name: "low_registration_rate"
        condition: "user_registration_rate < 10 in 1h"
        action: "notify"
        notification: "slack"
        channel: "#business"
      },
      {
        name: "high_order_value"
        condition: "average_order_value > 1000 in 1d"
        action: "notify"
        notification: "email"
        recipients: ["business@example.com"]
      }
    ]
  }
}
```

## 5. 代码生成模板

### 5.1 Fluentd配置生成

```ruby
# fluentd.conf
<source>
  @type tail
  path /var/log/webapp/app.log
  pos_file /var/log/fluentd/webapp.log.pos
  tag webapp.logs
  format json
  read_from_head true
</source>

<filter webapp.logs>
  @type record_transformer
  enable_ruby true
  <record>
    service "web-service"
    environment "production"
    timestamp ${Time.now.utc.iso8601}
  </record>
</filter>

<filter webapp.logs>
  @type grep
  <exclude>
    key level
    pattern DEBUG
  </exclude>
</filter>

<match webapp.logs>
  @type elasticsearch
  host elasticsearch
  port 9200
  logstash_format true
  logstash_prefix webapp-logs
  time_key timestamp
  time_key_format %Y-%m-%dT%H:%M:%S.%L%z
  include_tag_key true
  tag_key @log_name
  flush_interval 1s
  retry_max_interval 30
  retry_forever false
</match>
```

### 5.2 Logstash配置生成

```ruby
# logstash.conf
input {
  file {
    path => "/var/log/webapp/app.log"
    start_position => "beginning"
    codec => json
    tags => ["webapp"]
  }
}

filter {
  if "webapp" in [tags] {
    mutate {
      add_field => {
        "service" => "web-service"
        "environment" => "production"
      }
    }
    
    if [level] == "DEBUG" {
      drop {}
    }
    
    if [level] in ["ERROR", "FATAL"] {
      mutate {
        add_tag => ["error"]
      }
    }
  }
}

output {
  if "webapp" in [tags] {
    elasticsearch {
      hosts => ["elasticsearch:9200"]
      index => "webapp-logs-%{+YYYY.MM.dd}"
      template_name => "webapp-logs"
      template => {
        "index_patterns" => ["webapp-logs-*"]
        "settings" => {
          "number_of_shards" => 3
          "number_of_replicas" => 1
        }
        "mappings" => {
          "properties" => {
            "timestamp" => { "type" => "date" }
            "level" => { "type" => "keyword" }
            "message" => { "type" => "text" }
            "service" => { "type" => "keyword" }
            "environment" => { "type" => "keyword" }
          }
        }
      }
    }
  }
}
```

### 5.3 Prometheus告警规则生成

```yaml
# prometheus-rules.yml
groups:
  - name: log-alerts
    rules:
      - alert: HighErrorRate
        expr: rate(log_entries_total{level="ERROR"}[5m]) > 0.1
        for: 5m
        labels:
          severity: warning
          service: web-service
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value }} errors per second"
          
      - alert: ServiceDown
        expr: rate(log_entries_total{service="web-service"}[5m]) == 0
        for: 5m
        labels:
          severity: critical
          service: web-service
        annotations:
          summary: "Service appears to be down"
          description: "No logs received from web-service in the last 5 minutes"
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - log.name
    - log.description
    - log.version
    - log.source
  
  type_constraints:
    - field: "log.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "log.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "log.source.type"
      type: "string"
      enum: ["file", "kafka", "syslog", "http"]
```

### 6.2 日志验证规则

```yaml
log_validation:
  source_consistency:
    - rule: "source path must be valid"
    - rule: "source format must be supported"
    - rule: "source level must be valid"
  
  parsing_validation:
    - rule: "all required fields must be defined"
    - rule: "field types must be valid"
    - rule: "enum values must be consistent"
  
  storage_validation:
    - rule: "storage endpoint must be accessible"
    - rule: "index pattern must be valid"
    - rule: "retention period must be positive"
```

## 7. 最佳实践

### 7.1 日志设计模式

```dsl
# 应用日志模式
log "application_logs" {
  description: "应用日志"
  version: "1.0.0"
  
  source: {
    type: "file"
    path: "/var/log/app/app.log"
    format: "json"
    level: ["INFO", "WARN", "ERROR", "FATAL"]
  }
  
  parsing: {
    enabled: true
    format: "json"
    fields: [
      {
        name: "timestamp"
        type: "datetime"
        required: true
      },
      {
        name: "level"
        type: "string"
        required: true
      },
      {
        name: "message"
        type: "string"
        required: true
      }
    ]
  }
  
  storage: {
    type: "elasticsearch"
    index: "app-logs"
    retention: "30d"
  }
}

# 业务事件日志模式
log "business_events" {
  description: "业务事件日志"
  version: "1.0.0"
  
  source: {
    type: "kafka"
    topic: "business-events"
    format: "json"
  }
  
  parsing: {
    enabled: true
    format: "json"
    fields: [
      {
        name: "timestamp"
        type: "datetime"
        required: true
      },
      {
        name: "event_type"
        type: "string"
        required: true
      },
      {
        name: "user_id"
        type: "string"
        required: true
      }
    ]
  }
  
  analytics: {
    enabled: true
    metrics: [
      {
        name: "event_count"
        aggregation: "count"
        group_by: ["event_type", "hour"]
      }
    ]
  }
}
```

### 7.2 日志命名规范

```dsl
# 推荐命名模式
log "service_component_logs" {
  # 服务_组件_日志
}

log "environment_type_logs" {
  # 环境_类型_日志
}

log "domain_event_logs" {
  # 领域_事件_日志
}
```

## 8. 与主流标准的映射

| DSL元素 | Fluentd | Logstash | OpenTelemetry | ELK Stack |
|---------|---------|----------|---------------|-----------|
| log | source | input | resource | input |
| parsing | filter | filter | processor | filter |
| storage | output | output | exporter | output |
| alerting | n/a | n/a | n/a | alerting |
| analytics | n/a | n/a | n/a | analytics |

## 9. 工程实践示例

```dsl
# 生产环境日志配置示例
log "production_web_service_logs" {
  description: "生产环境Web服务日志"
  version: "1.0.0"
  author: "system"
  
  source: {
    type: "file"
    path: "/var/log/web-service/app.log"
    format: "json"
    encoding: "utf-8"
    level: ["INFO", "WARN", "ERROR", "FATAL"]
    rotation: {
      enabled: true
      max_size: "500MB"
      max_files: 20
      compress: true
      compress_after: "1d"
    }
    multiline: {
      enabled: true
      pattern: "^\\{"
      negate: true
      match: "after"
    }
  }
  
  parsing: {
    enabled: true
    format: "json"
    fields: [
      {
        name: "timestamp"
        type: "datetime"
        format: "ISO8601"
        required: true
      },
      {
        name: "level"
        type: "string"
        enum: ["DEBUG", "INFO", "WARN", "ERROR", "FATAL"]
        required: true
      },
      {
        name: "message"
        type: "string"
        required: true
      },
      {
        name: "trace_id"
        type: "string"
        required: false
        pattern: "^[a-f0-9]{32}$"
      },
      {
        name: "span_id"
        type: "string"
        required: false
        pattern: "^[a-f0-9]{16}$"
      },
      {
        name: "request_id"
        type: "string"
        required: false
      },
      {
        name: "user_id"
        type: "string"
        required: false
      },
      {
        name: "session_id"
        type: "string"
        required: false
      },
      {
        name: "service"
        type: "string"
        default: "web-service"
      },
      {
        name: "environment"
        type: "string"
        default: "production"
      },
      {
        name: "version"
        type: "string"
        default: "1.0.0"
      },
      {
        name: "host"
        type: "string"
        default: "{{ hostname }}"
      },
      {
        name: "pod_name"
        type: "string"
        default: "{{ pod_name }}"
      },
      {
        name: "namespace"
        type: "string"
        default: "{{ namespace }}"
      },
      {
        name: "http_method"
        type: "string"
        required: false
      },
      {
        name: "http_path"
        type: "string"
        required: false
      },
      {
        name: "http_status_code"
        type: "integer"
        required: false
      },
      {
        name: "response_time"
        type: "number"
        required: false
      },
      {
        name: "user_agent"
        type: "string"
        required: false
      },
      {
        name: "client_ip"
        type: "string"
        required: false
      },
      {
        name: "error_code"
        type: "string"
        required: false
      },
      {
        name: "error_message"
        type: "string"
        required: false
      },
      {
        name: "stack_trace"
        type: "string"
        required: false
      },
      {
        name: "metadata"
        type: "object"
        required: false
      }
    ]
  }
  
  filtering: {
    enabled: true
    rules: [
      {
        name: "exclude_debug"
        condition: "level != 'DEBUG'"
        action: "include"
      },
      {
        name: "include_errors"
        condition: "level in ['ERROR', 'FATAL']"
        action: "include"
      },
      {
        name: "exclude_health_checks"
        condition: "http_path != '/health'"
        action: "include"
      }
    ]
  }
  
  transformation: {
    enabled: true
    rules: [
      {
        name: "add_timestamp"
        action: "set_field"
        field: "timestamp"
        value: "{{ current_timestamp }}"
        condition: "timestamp == null"
      },
      {
        name: "add_service_info"
        action: "set_field"
        field: "service"
        value: "web-service"
      },
      {
        name: "add_environment"
        action: "set_field"
        field: "environment"
        value: "production"
      },
      {
        name: "add_host_info"
        action: "set_field"
        field: "host"
        value: "{{ hostname }}"
      },
      {
        name: "add_pod_info"
        action: "set_field"
        field: "pod_name"
        value: "{{ pod_name }}"
      },
      {
        name: "add_namespace"
        action: "set_field"
        field: "namespace"
        value: "{{ namespace }}"
      },
      {
        name: "parse_http_info"
        action: "extract"
        source: "message"
        pattern: "HTTP (\\w+) (\\S+) - (\\d+) - (\\d+)ms"
        fields: ["http_method", "http_path", "http_status_code", "response_time"]
        condition: "message contains 'HTTP'"
      }
    ]
  }
  
  correlation: {
    enabled: true
    correlation_fields: [
      "trace_id",
      "request_id",
      "user_id",
      "session_id"
    ]
    time_window: "5m"
  }
  
  aggregation: {
    enabled: true
    rules: [
      {
        name: "error_summary"
        condition: "level in ['ERROR', 'FATAL']"
        group_by: ["service", "level", "hour", "error_code"]
        aggregation: "count"
        time_window: "1h"
      },
      {
        name: "performance_summary"
        condition: "response_time != null"
        group_by: ["service", "http_path", "http_method"]
        aggregation: "avg"
        field: "response_time"
        time_window: "5m"
      },
      {
        name: "throughput_summary"
        condition: "http_method != null"
        group_by: ["service", "http_path", "minute"]
        aggregation: "count"
        time_window: "1m"
      }
    ]
  }
  
  storage: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    index: "web-service-logs"
    index_pattern: "web-service-logs-{YYYY.MM.DD}"
    shards: 5
    replicas: 2
    retention: "90d"
    compression: true
    lifecycle_policy: {
      enabled: true
      hot_retention: "7d"
      warm_retention: "30d"
      cold_retention: "90d"
      delete_after: "365d"
    }
    mapping: {
      timestamp: { type: "date" }
      level: { type: "keyword" }
      message: { type: "text" }
      trace_id: { type: "keyword" }
      request_id: { type: "keyword" }
      user_id: { type: "keyword" }
      service: { type: "keyword" }
      environment: { type: "keyword" }
      http_method: { type: "keyword" }
      http_path: { type: "keyword" }
      http_status_code: { type: "integer" }
      response_time: { type: "float" }
      error_code: { type: "keyword" }
    }
  }
  
  alerting: {
    enabled: true
    rules: [
      {
        name: "high_error_rate"
        condition: "count(level='ERROR') > 100 in 10m"
        action: "notify"
        notification: "slack"
        channel: "#alerts"
        severity: "warning"
      },
      {
        name: "critical_errors"
        condition: "level='FATAL'"
        action: "notify"
        notification: "pagerduty"
        urgency: "high"
        severity: "critical"
      },
      {
        name: "service_down"
        condition: "count(service='web-service') == 0 in 5m"
        action: "notify"
        notification: "pagerduty"
        urgency: "high"
        severity: "critical"
      },
      {
        name: "high_latency"
        condition: "avg(response_time) > 2s in 5m"
        action: "notify"
        notification: "slack"
        channel: "#performance"
        severity: "warning"
      },
      {
        name: "high_4xx_rate"
        condition: "count(http_status_code >= 400 AND http_status_code < 500) > 50 in 5m"
        action: "notify"
        notification: "slack"
        channel: "#alerts"
        severity: "warning"
      },
      {
        name: "high_5xx_rate"
        condition: "count(http_status_code >= 500) > 10 in 5m"
        action: "notify"
        notification: "pagerduty"
        urgency: "high"
        severity: "critical"
      }
    ]
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "log_volume",
      "error_rate",
      "response_time_p50",
      "response_time_p95",
      "response_time_p99",
      "throughput",
      "unique_users",
      "unique_sessions"
    ]
    dashboards: [
      "https://grafana.example.com/d/web-service-logs"
    ]
    thresholds: {
      error_rate_warning: 0.05
      error_rate_critical: 0.1
      response_time_warning: "1s"
      response_time_critical: "2s"
      throughput_warning: 1000
      throughput_critical: 500
    }
  }
  
  security: {
    enabled: true
    sensitive_fields: [
      "password",
      "token",
      "credit_card",
      "ssn",
      "api_key"
    ]
    redaction_rules: [
      {
        pattern: "password=.*"
        replacement: "password=***"
      },
      {
        pattern: "token=.*"
        replacement: "token=***"
      },
      {
        pattern: "api_key=.*"
        replacement: "api_key=***"
      }
    ]
    pii_detection: {
      enabled: true
      patterns: [
        "\\b\\d{3}-\\d{2}-\\d{4}\\b",  # SSN
        "\\b\\d{4}-\\d{4}-\\d{4}-\\d{4}\\b"  # Credit card
      ]
    }
    access_control: {
      enabled: true
      roles: [
        {
          name: "admin"
          permissions: ["read", "write", "delete"]
        },
        {
          name: "analyst"
          permissions: ["read"]
        }
      ]
    }
  }
  
  compliance: {
    enabled: true
    retention_policy: {
      enabled: true
      retention_period: "365d"
      legal_hold: false
    }
    audit_logging: {
      enabled: true
      log_access: true
      log_modifications: true
      retention_period: "7y"
    }
    data_classification: {
      enabled: true
      classifications: [
        "public",
        "internal",
        "confidential",
        "restricted"
      ]
      default_classification: "internal"
    }
  }
}
```

这个DSL设计为日志建模提供了完整的配置语言，支持基础日志、多源聚合、结构化分析等多种模式，同时保持了良好的可扩展性和可维护性。
