# 日志解析建模DSL草案

## 1. 设计目标

- 用声明式语法描述日志解析规则、格式、字段映射、输出等流程
- 支持多格式、多模式日志统一解析建模
- 便于自动生成解析与映射配置
- 支持复杂解析逻辑、条件解析、多级解析等高级特性

## 2. 基本语法结构

```dsl
log_parse "web_service_logs" {
  description: "Web服务日志解析"
  version: "1.0.0"
  author: "system"
  
  input: {
    format: "json"
    encoding: "utf-8"
    timestamp_field: "timestamp"
    timestamp_format: "ISO8601"
  }
  
  parsing: {
    type: "structured"
    rules: [
      {
        name: "extract_fields"
        condition: "true"
        actions: [
          {
            type: "extract"
            source: "message"
            target: "parsed_message"
            pattern: "\\[(.*?)\\] (.*)"
            groups: ["level", "content"]
          }
        ]
      }
    ]
  }
  
  field_mapping: [
    {
      source: "timestamp"
      target: "event_time"
      type: "timestamp"
      format: "ISO8601"
    },
    {
      source: "level"
      target: "severity"
      type: "string"
      mapping: {
        "DEBUG": "debug"
        "INFO": "info"
        "WARN": "warning"
        "ERROR": "error"
        "FATAL": "critical"
      }
    },
    {
      source: "message"
      target: "log_message"
      type: "string"
      max_length: 1000
    },
    {
      source: "trace_id"
      target: "correlation_id"
      type: "string"
      required: false
    }
  ]
  
  validation: {
    enabled: true
    rules: [
      {
        name: "required_fields"
        condition: "timestamp != null AND level != null"
        error_message: "Missing required fields: timestamp or level"
      },
      {
        name: "timestamp_format"
        condition: "timestamp matches ISO8601 pattern"
        error_message: "Invalid timestamp format"
      }
    ]
  }
  
  transformation: {
    enabled: true
    rules: [
      {
        name: "add_metadata"
        condition: "true"
        actions: [
          {
            type: "add_field"
            name: "service"
            value: "web-service"
          },
          {
            type: "add_field"
            name: "environment"
            value: "production"
          },
          {
            type: "add_field"
            name: "parsed_at"
            value: "now()"
            type: "timestamp"
          }
        ]
      }
    ]
  }
  
  output: {
    format: "json"
    schema: {
      type: "object"
      properties: {
        event_time: { type: "string", format: "date-time" }
        severity: { type: "string", enum: ["debug", "info", "warning", "error", "critical"] }
        log_message: { type: "string" }
        correlation_id: { type: "string" }
        service: { type: "string" }
        environment: { type: "string" }
        parsed_at: { type: "string", format: "date-time" }
      }
      required: ["event_time", "severity", "log_message"]
    }
  }
  
  error_handling: {
    enabled: true
    strategy: "continue"
    error_field: "parse_error"
    max_errors: 100
  }
  
  performance: {
    batch_size: 1000
    timeout: "30s"
    max_memory: "512MB"
  }
}
```

## 3. 关键元素

- log_parse：日志解析声明
- description：描述信息
- version：版本号
- author：作者
- input：输入配置
- parsing：解析规则
- field_mapping：字段映射
- validation：验证规则
- transformation：数据转换
- output：输出配置
- error_handling：错误处理
- performance：性能配置

## 4. 高级用法

### 4.1 多格式日志解析

```dsl
log_parse "multi_format_logs" {
  description: "多格式日志解析"
  version: "1.0.0"
  author: "system"
  
  input: {
    format: "auto"
    encoding: "utf-8"
    detect_format: true
  }
  
  parsing: {
    type: "conditional"
    rules: [
      {
        name: "json_logs"
        condition: "message startsWith '{'"
        actions: [
          {
            type: "parse_json"
            source: "message"
            target: "parsed_data"
          }
        ]
      },
      {
        name: "syslog_logs"
        condition: "message matches syslog pattern"
        actions: [
          {
            type: "parse_syslog"
            source: "message"
            target: "parsed_data"
            format: "rfc5424"
          }
        ]
      },
      {
        name: "nginx_logs"
        condition: "message contains 'nginx'"
        actions: [
          {
            type: "parse_nginx"
            source: "message"
            target: "parsed_data"
            format: "combined"
          }
        ]
      },
      {
        name: "custom_logs"
        condition: "true"
        actions: [
          {
            type: "parse_regex"
            source: "message"
            target: "parsed_data"
            pattern: "\\[(.*?)\\] (.*?) - (.*)"
            groups: ["timestamp", "level", "message"]
          }
        ]
      }
    ]
  }
  
  field_mapping: [
    {
      source: "parsed_data.timestamp"
      target: "event_time"
      type: "timestamp"
      format: "auto"
    },
    {
      source: "parsed_data.level"
      target: "severity"
      type: "string"
      mapping: {
        "DEBUG": "debug"
        "INFO": "info"
        "WARN": "warning"
        "ERROR": "error"
        "FATAL": "critical"
      }
    },
    {
      source: "parsed_data.message"
      target: "log_message"
      type: "string"
    }
  ]
  
  validation: {
    enabled: true
    rules: [
      {
        name: "valid_severity"
        condition: "severity in ['debug', 'info', 'warning', 'error', 'critical']"
        error_message: "Invalid severity level"
      }
    ]
  }
  
  output: {
    format: "json"
    schema: {
      type: "object"
      properties: {
        event_time: { type: "string", format: "date-time" }
        severity: { type: "string" }
        log_message: { type: "string" }
        original_format: { type: "string" }
      }
    }
  }
}
```

### 4.2 复杂解析逻辑

```dsl
log_parse "complex_parsing" {
  description: "复杂日志解析"
  version: "1.0.0"
  author: "system"
  
  input: {
    format: "text"
    encoding: "utf-8"
  }
  
  parsing: {
    type: "pipeline"
    stages: [
      {
        name: "stage1_extract_basic"
        condition: "true"
        actions: [
          {
            type: "extract_regex"
            source: "message"
            target: "basic_info"
            pattern: "\\[(.*?)\\] (.*?) - (.*)"
            groups: ["timestamp", "level", "content"]
          }
        ]
      },
      {
        name: "stage2_extract_metadata"
        condition: "basic_info.content contains 'metadata'"
        actions: [
          {
            type: "extract_json"
            source: "basic_info.content"
            target: "metadata"
            path: "$.metadata"
          }
        ]
      },
      {
        name: "stage3_extract_metrics"
        condition: "basic_info.content contains 'metrics'"
        actions: [
          {
            type: "extract_json"
            source: "basic_info.content"
            target: "metrics"
            path: "$.metrics"
          }
        ]
      },
      {
        name: "stage4_extract_errors"
        condition: "basic_info.level == 'ERROR'"
        actions: [
          {
            type: "extract_regex"
            source: "basic_info.content"
            target: "error_details"
            pattern: "Error: (.*?) at (.*?) \\((.*?):(.*?)\\)"
            groups: ["error_message", "function", "file", "line"]
          }
        ]
      }
    ]
  }
  
  field_mapping: [
    {
      source: "basic_info.timestamp"
      target: "event_time"
      type: "timestamp"
      format: "ISO8601"
    },
    {
      source: "basic_info.level"
      target: "severity"
      type: "string"
      mapping: {
        "DEBUG": "debug"
        "INFO": "info"
        "WARN": "warning"
        "ERROR": "error"
        "FATAL": "critical"
      }
    },
    {
      source: "basic_info.content"
      target: "log_message"
      type: "string"
    },
    {
      source: "metadata"
      target: "metadata"
      type: "object"
      required: false
    },
    {
      source: "metrics"
      target: "metrics"
      type: "object"
      required: false
    },
    {
      source: "error_details"
      target: "error_info"
      type: "object"
      required: false
    }
  ]
  
  transformation: {
    enabled: true
    rules: [
      {
        name: "calculate_metrics"
        condition: "metrics != null"
        actions: [
          {
            type: "calculate"
            target: "metrics_summary"
            expression: "metrics.response_time + metrics.processing_time"
          }
        ]
      },
      {
        name: "enrich_error_info"
        condition: "error_info != null"
        actions: [
          {
            type: "add_field"
            name: "error_category"
            value: "application_error"
          },
          {
            type: "add_field"
            name: "error_priority"
            value: "high"
          }
        ]
      }
    ]
  }
  
  output: {
    format: "json"
    schema: {
      type: "object"
      properties: {
        event_time: { type: "string", format: "date-time" }
        severity: { type: "string" }
        log_message: { type: "string" }
        metadata: { type: "object" }
        metrics: { type: "object" }
        error_info: { type: "object" }
        metrics_summary: { type: "number" }
        error_category: { type: "string" }
        error_priority: { type: "string" }
      }
    }
  }
}
```

## 5. 代码生成模板

### 5.1 Logstash配置生成

```ruby
# logstash.conf
input {
  file {
    path => "/var/log/webapp/app.log"
    start_position => "beginning"
    codec => json
  }
}

filter {
  if [message] =~ /\[.*?\] .*? - .*/ {
    grok {
      match => { "message" => "\[%{TIMESTAMP_ISO8601:timestamp}\] %{LOGLEVEL:level} - %{GREEDYDATA:content}" }
    }
  }
  
  date {
    match => [ "timestamp", "ISO8601" ]
    target => "@timestamp"
  }
  
  mutate {
    add_field => { "service" => "web-service" }
    add_field => { "environment" => "production" }
  }
  
  if [level] == "ERROR" {
    grok {
      match => { "content" => "Error: %{GREEDYDATA:error_message} at %{DATA:function} \(%{DATA:file}:%{NUMBER:line}\)" }
    }
  }
}

output {
  elasticsearch {
    hosts => ["elasticsearch:9200"]
    index => "web-service-logs"
  }
}
```

### 5.2 Fluentd配置生成

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
  @type parser
  key_name message
  <parse>
    @type regexp
    expression /\[(?<timestamp>.*?)\] (?<level>.*?) - (?<content>.*)/
  </parse>
</filter>

<filter webapp.logs>
  @type record_transformer
  enable_ruby true
  <record>
    service "web-service"
    environment "production"
    parsed_at ${Time.now.utc.iso8601}
  </record>
</filter>

<filter webapp.logs>
  @type record_transformer
  <record>
    severity ${record['level'] == 'DEBUG' ? 'debug' : record['level'] == 'INFO' ? 'info' : record['level'] == 'WARN' ? 'warning' : record['level'] == 'ERROR' ? 'error' : 'critical'}
  </record>
</filter>

<match webapp.logs>
  @type elasticsearch
  host elasticsearch
  port 9200
  logstash_format true
  logstash_prefix web-service-logs
  flush_interval 5s
</match>
```

### 5.3 OpenTelemetry Collector配置生成

```yaml
# otel-collector-config.yaml
receivers:
  filelog:
    include: [ /var/log/webapp/*.log ]
    start_at: end
    operators:
      - type: regex_parser
        regex: '\[(?P<timestamp>.*?)\] (?P<level>.*?) - (?P<content>.*)'
        timestamp:
          parse_from: attributes.timestamp
          layout: RFC3339
      - type: add_fields
        fields:
          service: web-service
          environment: production
      - type: move
        from: attributes.level
        to: attributes.severity

processors:
  batch:
    timeout: 1s
    send_batch_size: 100
  transform:
    log_statements:
      - context: log
        statements:
          - set(attributes["severity"], attributes["level"] == "DEBUG" ? "debug" : attributes["level"] == "INFO" ? "info" : attributes["level"] == "WARN" ? "warning" : attributes["level"] == "ERROR" ? "error" : "critical")

exporters:
  otlp/elasticsearch:
    endpoint: elasticsearch:9200
    tls:
      insecure: true

service:
  pipelines:
    logs:
      receivers: [filelog]
      processors: [batch, transform]
      exporters: [otlp/elasticsearch]
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - log_parse.name
    - log_parse.description
    - log_parse.version
    - log_parse.input
  
  type_constraints:
    - field: "log_parse.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "log_parse.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "log_parse.input.format"
      type: "string"
      enum: ["json", "text", "csv", "syslog", "nginx", "auto"]
```

### 6.2 解析验证规则

```yaml
parsing_validation:
  input_consistency:
    - rule: "input format must be supported"
    - rule: "input encoding must be valid"
    - rule: "timestamp format must be valid"
  
  parsing_validation:
    - rule: "parsing rules must be valid"
    - rule: "regex patterns must be valid"
    - rule: "field mappings must be consistent"
  
  output_validation:
    - rule: "output format must be supported"
    - rule: "output schema must be valid"
    - rule: "required fields must be mapped"
```

## 7. 最佳实践

### 7.1 解析设计模式

```dsl
# 基础解析模式
log_parse "basic_parse" {
  description: "基础日志解析"
  version: "1.0.0"
  
  input: {
    format: "json"
    encoding: "utf-8"
  }
  
  field_mapping: [
    {
      source: "timestamp"
      target: "event_time"
      type: "timestamp"
    },
    {
      source: "level"
      target: "severity"
      type: "string"
    }
  ]
  
  output: {
    format: "json"
  }
}

# 条件解析模式
log_parse "conditional_parse" {
  description: "条件日志解析"
  version: "1.0.0"
  
  input: {
    format: "auto"
    encoding: "utf-8"
  }
  
  parsing: {
    type: "conditional"
    rules: [
      {
        name: "json_logs"
        condition: "message startsWith '{'"
        actions: [
          {
            type: "parse_json"
            source: "message"
            target: "parsed_data"
          }
        ]
      },
      {
        name: "text_logs"
        condition: "true"
        actions: [
          {
            type: "parse_regex"
            source: "message"
            target: "parsed_data"
            pattern: "\\[(.*?)\\] (.*)"
            groups: ["timestamp", "content"]
          }
        ]
      }
    ]
  }
  
  output: {
    format: "json"
  }
}
```

### 7.2 解析命名规范

```dsl
# 推荐命名模式
log_parse "service_format_parse" {
  # 服务_格式_解析
}

log_parse "environment_type_parse" {
  # 环境_类型_解析
}

log_parse "domain_complexity_parse" {
  # 领域_复杂度_解析
}
```

## 8. 与主流标准的映射

| DSL元素 | Logstash | Fluentd | OpenTelemetry | ELK Stack |
|---------|----------|---------|---------------|-----------|
| log_parse | filter | parser | processor | filter |
| field_mapping | mutate | record_transformer | processor | transform |
| validation | validate | validate | processor | validate |
| transformation | mutate | record_transformer | processor | transform |
| output | output | output | exporter | output |

## 9. 工程实践示例

```dsl
# 生产环境日志解析配置示例
log_parse "production_log_parse" {
  description: "生产环境日志解析"
  version: "1.0.0"
  author: "system"
  
  input: {
    format: "auto"
    encoding: "utf-8"
    detect_format: true
    fallback_format: "text"
  }
  
  parsing: {
    type: "pipeline"
    stages: [
      {
        name: "detect_format"
        condition: "true"
        actions: [
          {
            type: "detect_format"
            source: "message"
            target: "detected_format"
            formats: ["json", "syslog", "nginx", "custom"]
          }
        ]
      },
      {
        name: "parse_json"
        condition: "detected_format == 'json'"
        actions: [
          {
            type: "parse_json"
            source: "message"
            target: "parsed_data"
            strict: false
          }
        ]
      },
      {
        name: "parse_syslog"
        condition: "detected_format == 'syslog'"
        actions: [
          {
            type: "parse_syslog"
            source: "message"
            target: "parsed_data"
            format: "rfc5424"
          }
        ]
      },
      {
        name: "parse_nginx"
        condition: "detected_format == 'nginx'"
        actions: [
          {
            type: "parse_nginx"
            source: "message"
            target: "parsed_data"
            format: "combined"
          }
        ]
      },
      {
        name: "parse_custom"
        condition: "detected_format == 'custom'"
        actions: [
          {
            type: "parse_regex"
            source: "message"
            target: "parsed_data"
            pattern: "\\[(?P<timestamp>.*?)\\] (?P<level>.*?) - (?P<content>.*)"
            groups: ["timestamp", "level", "content"]
          }
        ]
      }
    ]
  }
  
  field_mapping: [
    {
      source: "parsed_data.timestamp"
      target: "event_time"
      type: "timestamp"
      format: "auto"
      timezone: "UTC"
    },
    {
      source: "parsed_data.level"
      target: "severity"
      type: "string"
      mapping: {
        "DEBUG": "debug"
        "INFO": "info"
        "WARN": "warning"
        "ERROR": "error"
        "FATAL": "critical"
        "TRACE": "trace"
      }
      default: "info"
    },
    {
      source: "parsed_data.content"
      target: "log_message"
      type: "string"
      max_length: 2000
      truncate: true
    },
    {
      source: "parsed_data.trace_id"
      target: "correlation_id"
      type: "string"
      required: false
      pattern: "^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$"
    },
    {
      source: "parsed_data.user_id"
      target: "user_id"
      type: "string"
      required: false
      mask: true
    },
    {
      source: "parsed_data.ip_address"
      target: "client_ip"
      type: "string"
      required: false
      validate: "ipv4"
    }
  ]
  
  validation: {
    enabled: true
    rules: [
      {
        name: "required_fields"
        condition: "event_time != null AND severity != null"
        error_message: "Missing required fields: event_time or severity"
        severity: "error"
      },
      {
        name: "valid_severity"
        condition: "severity in ['debug', 'info', 'warning', 'error', 'critical', 'trace']"
        error_message: "Invalid severity level: {severity}"
        severity: "warning"
      },
      {
        name: "valid_timestamp"
        condition: "event_time != null AND event_time > '2020-01-01T00:00:00Z'"
        error_message: "Invalid timestamp: {event_time}"
        severity: "warning"
      },
      {
        name: "message_length"
        condition: "log_message != null AND log_message.length <= 2000"
        error_message: "Log message too long: {log_message.length} characters"
        severity: "warning"
      }
    ]
    error_handling: {
      strategy: "continue"
      error_field: "validation_errors"
      max_errors: 100
    }
  }
  
  transformation: {
    enabled: true
    rules: [
      {
        name: "add_metadata"
        condition: "true"
        actions: [
          {
            type: "add_field"
            name: "service"
            value: "web-service"
          },
          {
            type: "add_field"
            name: "environment"
            value: "production"
          },
          {
            type: "add_field"
            name: "parsed_at"
            value: "now()"
            type: "timestamp"
          },
          {
            type: "add_field"
            name: "parse_version"
            value: "1.0.0"
          }
        ]
      },
      {
        name: "enrich_error_logs"
        condition: "severity in ['error', 'critical']"
        actions: [
          {
            type: "add_field"
            name: "error_category"
            value: "application_error"
          },
          {
            type: "add_field"
            name: "alert_priority"
            value: "high"
          }
        ]
      },
      {
        name: "mask_sensitive_data"
        condition: "log_message contains 'password' OR log_message contains 'token'"
        actions: [
          {
            type: "mask_field"
            field: "log_message"
            pattern: "(password|token)=[^\\s]+"
            replacement: "$1=***"
          }
        ]
      },
      {
        name: "calculate_metrics"
        condition: "log_message contains 'response_time'"
        actions: [
          {
            type: "extract_regex"
            source: "log_message"
            target: "response_time"
            pattern: "response_time=(\\d+)"
            groups: ["time_ms"]
          },
          {
            type: "calculate"
            target: "response_time_seconds"
            expression: "response_time.time_ms / 1000"
            type: "float"
          }
        ]
      }
    ]
  }
  
  output: {
    format: "json"
    schema: {
      type: "object"
      properties: {
        event_time: { type: "string", format: "date-time" }
        severity: { type: "string", enum: ["debug", "info", "warning", "error", "critical", "trace"] }
        log_message: { type: "string", maxLength: 2000 }
        correlation_id: { type: "string", format: "uuid" }
        user_id: { type: "string" }
        client_ip: { type: "string", format: "ipv4" }
        service: { type: "string" }
        environment: { type: "string" }
        parsed_at: { type: "string", format: "date-time" }
        parse_version: { type: "string" }
        error_category: { type: "string" }
        alert_priority: { type: "string" }
        response_time_seconds: { type: "number" }
        validation_errors: { type: "array", items: { type: "string" } }
      }
      required: ["event_time", "severity", "log_message", "service", "environment"]
    }
    compression: {
      enabled: true
      algorithm: "gzip"
      level: 6
    }
  }
  
  error_handling: {
    enabled: true
    strategy: "continue"
    error_field: "parse_error"
    max_errors: 1000
    error_logging: {
      enabled: true
      level: "warn"
      destination: "parse_errors.log"
    }
    fallback: {
      enabled: true
      action: "passthrough"
      add_error_info: true
    }
  }
  
  performance: {
    batch_size: 1000
    timeout: "30s"
    max_memory: "1GB"
    parallel_processing: {
      enabled: true
      workers: 4
      queue_size: 10000
    }
    caching: {
      enabled: true
      max_size: "100MB"
      ttl: "1h"
    }
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "parse_rate",
      "parse_latency",
      "error_rate",
      "format_detection_accuracy",
      "validation_errors",
      "transformation_errors"
    ]
    alerts: [
      {
        name: "high_parse_error_rate"
        condition: "error_rate > 0.05"
        duration: "5m"
        severity: "warning"
      },
      {
        name: "high_parse_latency"
        condition: "parse_latency > 5s"
        duration: "2m"
        severity: "warning"
      }
    ]
    dashboards: [
      "https://grafana.example.com/d/log-parsing"
    ]
  }
  
  security: {
    enabled: true
    data_masking: {
      enabled: true
      fields: ["password", "token", "api_key", "credit_card"]
      method: "hash"
      salt: "random_salt"
    }
    encryption: {
      enabled: true
      algorithm: "AES-256"
      key_rotation: "30d"
    }
    access_control: {
      enabled: true
      audit_logging: true
      retention_period: "7y"
    }
  }
}
```

这个DSL设计为日志解析建模提供了完整的配置语言，支持基础解析、多格式解析、复杂解析逻辑等多种模式，同时保持了良好的可扩展性和可维护性。
