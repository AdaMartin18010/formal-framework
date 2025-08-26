# 日志解析建模DSL设计

## 设计目标

日志解析建模DSL旨在提供声明式语言定义复杂的日志解析规则，支持多种日志格式、解析策略、字段映射、数据转换，并与主流日志解析平台无缝集成。

## 基本语法

### 核心结构

```dsl
log_parsing "web_service_parsing" {
  description: "Web服务日志解析"
  version: "1.0.0"
  
  input: {
    format: "json"
    encoding: "utf-8"
    source: "filebeat"
  }
  
  parsers: [
    {
      name: "json_parser"
      type: "json"
      target: "parsed"
      overwrite_keys: true
    }
  ]
  
  output: {
    format: "structured"
    destination: "elasticsearch"
    index: "parsed-logs"
  }
}
```

### JSON解析器

```dsl
json_parser "application_logs" {
  description: "应用程序JSON日志解析"
  
  type: "json"
  target: "parsed"
  overwrite_keys: true
  
  field_mapping: {
    timestamp: "@timestamp"
    level: "log.level"
    message: "message"
    service: "service.name"
    trace_id: "trace.id"
    span_id: "span.id"
  }
  
  validation: {
    required_fields: ["timestamp", "level", "message"]
    field_types: {
      timestamp: "datetime"
      level: "string"
      message: "string"
      service: "string"
      trace_id: "string"
      span_id: "string"
    }
  }
  
  transformation: [
    {
      name: "normalize_timestamp"
      type: "timestamp"
      field: "timestamp"
      format: "ISO8601"
      timezone: "UTC"
    },
    {
      name: "normalize_level"
      type: "enum"
      field: "level"
      mapping: {
        "ERROR": "error"
        "WARN": "warn"
        "INFO": "info"
        "DEBUG": "debug"
      }
    }
  ]
  
  error_handling: {
    on_error: "drop"
    error_log: true
    error_metrics: true
  }
}
```

### Grok解析器

```dsl
grok_parser "nginx_access_logs" {
  description: "Nginx访问日志解析"
  
  type: "grok"
  pattern: "%{IPORHOST:clientip} - %{DATA:ident} - %{DATA:auth} \\[%{HTTPDATE:timestamp}\\] \"%{WORD:verb} %{DATA:request} HTTP/%{NUMBER:httpversion}\" %{NUMBER:response} %{NUMBER:bytes}"
  
  field_mapping: {
    clientip: "client_ip"
    timestamp: "@timestamp"
    verb: "http_method"
    request: "http_request"
    httpversion: "http_version"
    response: "http_status_code"
    bytes: "response_size"
  }
  
  custom_patterns: [
    {
      name: "IPORHOST"
      pattern: "(?<![0-9])(?:(?:25[0-5]|2[0-4][0-9]|[0-1]?[0-9]{1,2})[.](?:25[0-5]|2[0-4][0-9]|[0-1]?[0-9]{1,2})[.](?:25[0-5]|2[0-4][0-9]|[0-1]?[0-9]{1,2})[.](?:25[0-5]|2[0-4][0-9]|[0-1]?[0-9]{1,2}))(?![0-9])"
    }
  ]
  
  validation: {
    required_fields: ["client_ip", "@timestamp", "http_method", "http_status_code"]
    field_types: {
      client_ip: "ip"
      "@timestamp": "datetime"
      http_method: "string"
      http_status_code: "integer"
      response_size: "integer"
    }
  }
  
  transformation: [
    {
      name: "parse_request"
      type: "regex"
      field: "http_request"
      pattern: "(?<method>\\w+) (?<path>[^\\s]+) (?<query>[^\\s]*)"
      target: "parsed_request"
    },
    {
      name: "categorize_status"
      type: "conditional"
      field: "http_status_code"
      rules: [
        { condition: "value >= 200 AND value < 300", result: "success" },
        { condition: "value >= 300 AND value < 400", result: "redirect" },
        { condition: "value >= 400 AND value < 500", result: "client_error" },
        { condition: "value >= 500", result: "server_error" }
      ]
      target: "status_category"
    }
  ]
}
```

### 正则表达式解析器

```dsl
regex_parser "custom_log_format" {
  description: "自定义日志格式解析"
  
  type: "regex"
  pattern: "\\[(?<timestamp>\\d{4}-\\d{2}-\\d{2} \\d{2}:\\d{2}:\\d{2}\\.\\d{3})\\] \\[(?<level>\\w+)\\] \\[(?<service>\\w+)\\] (?<message>.*)"
  
  field_mapping: {
    timestamp: "@timestamp"
    level: "log.level"
    service: "service.name"
    message: "message"
  }
  
  validation: {
    required_fields: ["@timestamp", "log.level", "service.name", "message"]
    field_types: {
      "@timestamp": "datetime"
      "log.level": "string"
      "service.name": "string"
      "message": "string"
    }
  }
  
  transformation: [
    {
      name: "parse_timestamp"
      type: "timestamp"
      field: "@timestamp"
      format: "yyyy-MM-dd HH:mm:ss.SSS"
      timezone: "UTC"
    },
    {
      name: "extract_metadata"
      type: "regex"
      field: "message"
      pattern: "\\[(?<component>\\w+)\\] \\[(?<operation>\\w+)\\]"
      target: "metadata"
    }
  ]
}
```

### 多行解析器

```dsl
multiline_parser "stack_trace_parser" {
  description: "堆栈跟踪多行解析"
  
  type: "multiline"
  pattern: "^\\["
  negate: true
  match: "after"
  
  field_mapping: {
    first_line: "stack_trace_start"
    continuation_lines: "stack_trace_body"
  }
  
  validation: {
    required_fields: ["stack_trace_start"]
    max_lines: 100
    max_length: 10000
  }
  
  transformation: [
    {
      name: "extract_exception"
      type: "regex"
      field: "stack_trace_start"
      pattern: "(?<exception_type>\\w+): (?<exception_message>.*)"
      target: "exception_info"
    },
    {
      name: "parse_stack_frames"
      type: "regex"
      field: "stack_trace_body"
      pattern: "\\s+at (?<class>\\S+)\\.(?<method>\\S+)\\((?<file>\\S+):(?<line>\\d+)\\)"
      target: "stack_frames"
      multiple: true
    }
  ]
}
```

## 高级用法

### 复合解析器

```dsl
composite_parser "comprehensive_parsing" {
  description: "综合日志解析"
  
  parsers: [
    {
      name: "format_detector"
      type: "format_detection"
      patterns: [
        { pattern: "^\\{.*\\}$", format: "json" },
        { pattern: "^\\[.*\\]", format: "bracket" },
        { pattern: "^\\d{4}-\\d{2}-\\d{2}", format: "timestamp" }
      ]
    },
    {
      name: "json_parser"
      type: "json"
      condition: "format == 'json'"
      target: "parsed"
    },
    {
      name: "bracket_parser"
      type: "regex"
      condition: "format == 'bracket'"
      pattern: "\\[(?<timestamp>.*?)\\] \\[(?<level>\\w+)\\] (?<message>.*)"
    },
    {
      name: "timestamp_parser"
      type: "regex"
      condition: "format == 'timestamp'"
      pattern: "(?<timestamp>\\d{4}-\\d{2}-\\d{2} \\d{2}:\\d{2}:\\d{2}) (?<level>\\w+) (?<message>.*)"
    }
  ]
  
  aggregation: {
    strategy: "merge"
    priority: ["json_parser", "bracket_parser", "timestamp_parser"]
  }
  
  post_processing: [
    {
      name: "normalize_fields"
      type: "field_normalization"
      fields: ["timestamp", "level", "message"]
    },
    {
      name: "add_metadata"
      type: "field_addition"
      fields: {
        parser_used: "format_detector.result",
        parsed_at: "now()"
      }
    }
  ]
}
```

### 条件解析器

```dsl
conditional_parser "service_specific_parsing" {
  description: "服务特定解析"
  
  conditions: [
    {
      name: "web_service_logs"
      condition: "service == 'web-service'"
      parser: {
        type: "json"
        target: "web_parsed"
        field_mapping: {
          timestamp: "@timestamp"
          level: "log.level"
          message: "message"
          endpoint: "http.endpoint"
          method: "http.method"
          status: "http.status"
          duration: "http.duration"
        }
      }
    },
    {
      name: "database_service_logs"
      condition: "service == 'database-service'"
      parser: {
        type: "regex"
        pattern: "\\[(?<timestamp>.*?)\\] \\[(?<level>\\w+)\\] \\[(?<operation>\\w+)\\] (?<query>.*?) \\((?<duration>\\d+)ms\\)"
        field_mapping: {
          timestamp: "@timestamp"
          level: "log.level"
          operation: "db.operation"
          query: "db.query"
          duration: "db.duration"
        }
      }
    },
    {
      name: "cache_service_logs"
      condition: "service == 'cache-service'"
      parser: {
        type: "json"
        target: "cache_parsed"
        field_mapping: {
          timestamp: "@timestamp"
          level: "log.level"
          message: "message"
          cache_key: "cache.key"
          cache_operation: "cache.operation"
          cache_hit: "cache.hit"
        }
      }
    }
  ]
  
  default_parser: {
    type: "regex"
    pattern: "\\[(?<timestamp>.*?)\\] \\[(?<level>\\w+)\\] \\[(?<service>\\w+)\\] (?<message>.*)"
  }
}
```

### 流式解析器

```dsl
stream_parser "real_time_parsing" {
  description: "实时流解析"
  
  streaming: {
    engine: "kafka_streams"
    mode: "real_time"
    parallelism: 4
  }
  
  input: {
    topic: "raw-logs"
    consumer_group: "log-parsers"
    auto_offset_reset: "latest"
  }
  
  parsing_pipeline: [
    {
      name: "format_detection"
      type: "stream_processor"
      operation: "detect_format"
      output: "detected_format"
    },
    {
      name: "json_parsing"
      type: "stream_processor"
      input: "detected_format"
      condition: "format == 'json'"
      operation: "parse_json"
      output: "parsed_json"
    },
    {
      name: "regex_parsing"
      type: "stream_processor"
      input: "detected_format"
      condition: "format == 'regex'"
      operation: "parse_regex"
      output: "parsed_regex"
    },
    {
      name: "field_normalization"
      type: "stream_processor"
      input: ["parsed_json", "parsed_regex"]
      operation: "normalize_fields"
      output: "normalized_logs"
    }
  ]
  
  output: {
    topic: "parsed-logs"
    producer_config: {
      acks: "all"
      compression: "snappy"
      batch_size: 1000
    }
  }
  
  monitoring: {
    metrics: [
      "records_processed",
      "parsing_success_rate",
      "parsing_latency",
      "error_rate"
    ]
    alerting: {
      on_error_rate: {
        threshold: 0.01
        severity: "critical"
      }
      on_latency: {
        threshold: "1s"
        severity: "warning"
      }
    }
  }
}
```

## 代码生成模板

### Fluentd配置

```ruby
# 生成的Fluentd配置
<source>
  @type tail
  path /var/log/webapp/app.log
  pos_file /var/log/fluentd/webapp.log.pos
  tag web-service.logs
  read_from_head true
  <parse>
    @type json
    time_key timestamp
    time_format %Y-%m-%dT%H:%M:%S.%LZ
  </parse>
</source>

<filter web-service.logs>
  @type parser
  key_name message
  <parse>
    @type regexp
    expression /\[(?<timestamp>.*?)\] \[(?<level>\w+)\] \[(?<service>\w+)\] (?<message>.*)/
  </parse>
</filter>

<filter web-service.logs>
  @type record_transformer
  <record>
    @timestamp ${time}
    log_level ${level}
    service_name ${service}
    log_message ${message}
    parsed_at "#{Time.now.utc.iso8601}"
  </record>
</filter>

<filter web-service.logs>
  @type grep
  <regexp>
    key log_level
    pattern /ERROR|WARN|INFO/
  </regexp>
</filter>

<match web-service.logs>
  @type elasticsearch
  host elasticsearch
  port 9200
  logstash_format true
  logstash_prefix parsed-logs
  include_tag_key true
  tag_key @log_name
  flush_interval 5s
  <buffer>
    @type memory
    flush_interval 5s
    chunk_limit_size 2M
    queue_limit_length 8
    retry_max_interval 30
    retry_forever false
  </buffer>
</match>
```

### Logstash配置

```ruby
# 生成的Logstash配置
input {
  beats {
    port => 5044
    ssl => true
    ssl_certificate => "/etc/ssl/certs/logstash.crt"
    ssl_key => "/etc/ssl/private/logstash.key"
  }
}

filter {
  if [fields][service] == "web-service" {
    json {
      source => "message"
      target => "parsed"
    }
    
    date {
      match => ["parsed.timestamp", "ISO8601"]
      target => "@timestamp"
    }
    
    mutate {
      add_field => {
        "log_level" => "%{[parsed][level]}"
        "service_name" => "%{[parsed][service]}"
        "log_message" => "%{[parsed][message]}"
      }
      remove_field => ["parsed"]
    }
  } else if [fields][service] == "nginx" {
    grok {
      match => { "message" => "%{IPORHOST:clientip} - %{DATA:ident} - %{DATA:auth} \[%{HTTPDATE:timestamp}\] \"%{WORD:verb} %{DATA:request} HTTP/%{NUMBER:httpversion}\" %{NUMBER:response} %{NUMBER:bytes}" }
    }
    
    date {
      match => ["timestamp", "dd/MMM/yyyy:HH:mm:ss Z"]
      target => "@timestamp"
    }
    
    mutate {
      add_field => {
        "http_method" => "%{verb}"
        "http_status_code" => "%{response}"
        "response_size" => "%{bytes}"
      }
      remove_field => ["verb", "response", "bytes", "ident", "auth", "httpversion"]
    }
  } else {
    grok {
      match => { "message" => "\[%{TIMESTAMP_ISO8601:timestamp}\] \[%{LOGLEVEL:level}\] \[%{DATA:service}\] %{GREEDYDATA:message}" }
    }
    
    date {
      match => ["timestamp", "ISO8601"]
      target => "@timestamp"
    }
  }
  
  mutate {
    add_field => {
      "parsed_at" => "%{@timestamp}"
      "parser_version" => "1.0.0"
    }
  }
}

output {
  elasticsearch {
    hosts => ["elasticsearch:9200"]
    index => "parsed-logs-%{+YYYY.MM.dd}"
    template_name => "parsed-logs"
    template_pattern => "parsed-logs-*"
    template_overwrite => true
  }
}
```

### Python实现

```python
import re
import json
import logging
from datetime import datetime
from typing import Dict, Any, Optional

class LogParser:
    def __init__(self, config):
        self.config = config
        self.parsers = self._initialize_parsers()
        self.logger = logging.getLogger(__name__)
    
    def _initialize_parsers(self):
        parsers = {}
        for parser_config in self.config['parsers']:
            if parser_config['type'] == 'json':
                parsers[parser_config['name']] = JSONParser(parser_config)
            elif parser_config['type'] == 'grok':
                parsers[parser_config['name']] = GrokParser(parser_config)
            elif parser_config['type'] == 'regex':
                parsers[parser_config['name']] = RegexParser(parser_config)
        return parsers
    
    def parse(self, log_line: str) -> Optional[Dict[str, Any]]:
        try:
            # 检测日志格式
            format_type = self._detect_format(log_line)
            
            # 选择相应的解析器
            if format_type == 'json':
                parser = self.parsers.get('json_parser')
            elif format_type == 'nginx':
                parser = self.parsers.get('grok_parser')
            else:
                parser = self.parsers.get('regex_parser')
            
            if parser:
                result = parser.parse(log_line)
                if result:
                    result['parsed_at'] = datetime.utcnow().isoformat()
                    result['parser_used'] = parser.name
                return result
            else:
                self.logger.warning(f"No parser found for format: {format_type}")
                return None
                
        except Exception as e:
            self.logger.error(f"Error parsing log line: {e}")
            return None
    
    def _detect_format(self, log_line: str) -> str:
        if log_line.strip().startswith('{') and log_line.strip().endswith('}'):
            return 'json'
        elif 'HTTP/' in log_line and 'GET' in log_line or 'POST' in log_line:
            return 'nginx'
        else:
            return 'custom'

class JSONParser:
    def __init__(self, config):
        self.name = config['name']
        self.target = config.get('target', 'parsed')
        self.overwrite_keys = config.get('overwrite_keys', True)
        self.field_mapping = config.get('field_mapping', {})
    
    def parse(self, log_line: str) -> Optional[Dict[str, Any]]:
        try:
            data = json.loads(log_line)
            
            # 应用字段映射
            result = {}
            for source_field, target_field in self.field_mapping.items():
                if source_field in data:
                    result[target_field] = data[source_field]
            
            # 添加原始数据
            if self.target:
                result[self.target] = data
            
            return result
        except json.JSONDecodeError:
            return None

class GrokParser:
    def __init__(self, config):
        self.name = config['name']
        self.pattern = config['pattern']
        self.field_mapping = config.get('field_mapping', {})
        self.compiled_pattern = re.compile(self.pattern)
    
    def parse(self, log_line: str) -> Optional[Dict[str, Any]]:
        match = self.compiled_pattern.match(log_line)
        if match:
            result = {}
            for source_field, target_field in self.field_mapping.items():
                if source_field in match.groupdict():
                    result[target_field] = match.group(source_field)
            return result
        return None

class RegexParser:
    def __init__(self, config):
        self.name = config['name']
        self.pattern = config['pattern']
        self.field_mapping = config.get('field_mapping', {})
        self.compiled_pattern = re.compile(self.pattern)
    
    def parse(self, log_line: str) -> Optional[Dict[str, Any]]:
        match = self.compiled_pattern.match(log_line)
        if match:
            result = {}
            for source_field, target_field in self.field_mapping.items():
                if source_field in match.groupdict():
                    result[target_field] = match.group(source_field)
            return result
        return None

# 使用示例
config = {
    "parsers": [
        {
            "name": "json_parser",
            "type": "json",
            "target": "parsed",
            "overwrite_keys": True,
            "field_mapping": {
                "timestamp": "@timestamp",
                "level": "log.level",
                "message": "message"
            }
        },
        {
            "name": "grok_parser",
            "type": "grok",
            "pattern": r"\[(?P<timestamp>.*?)\] \[(?P<level>\w+)\] \[(?P<service>\w+)\] (?P<message>.*)",
            "field_mapping": {
                "timestamp": "@timestamp",
                "level": "log.level",
                "service": "service.name",
                "message": "message"
            }
        },
        {
            "name": "regex_parser",
            "type": "regex",
            "pattern": r"\[(?P<timestamp>.*?)\] \[(?P<level>\w+)\] \[(?P<service>\w+)\] (?P<message>.*)",
            "field_mapping": {
                "timestamp": "@timestamp",
                "level": "log.level",
                "service": "service.name",
                "message": "message"
            }
        }
    ]
}

parser = LogParser(config)

# 测试解析
json_log = '{"timestamp": "2024-01-01T12:00:00Z", "level": "INFO", "message": "Application started"}'
custom_log = '[2024-01-01 12:00:00] [INFO] [web-service] Application started'

print(parser.parse(json_log))
print(parser.parse(custom_log))
```

## 验证规则

### 语法验证

```dsl
validation_rules "log_parsing_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "version", "input", "parsers"]
      message: "必须包含描述、版本、输入和解析器"
    },
    {
      rule: "valid_parser_type"
      allowed_types: ["json", "grok", "regex", "multiline"]
      message: "解析器类型必须是支持的类型"
    },
    {
      rule: "valid_pattern"
      condition: "pattern is valid regex"
      message: "正则表达式模式必须有效"
    }
  ]
  
  semantic: [
    {
      rule: "field_mapping_validity"
      condition: "all mapped fields exist in pattern"
      message: "字段映射中的所有字段必须在模式中存在"
    },
    {
      rule: "target_field_uniqueness"
      condition: "target fields are unique"
      message: "目标字段必须是唯一的"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "parsing_performance" {
  constraints: [
    {
      metric: "parsing_latency"
      threshold: "100ms"
      action: "warn"
    },
    {
      metric: "throughput"
      threshold: "10000 logs/sec"
      action: "error"
    },
    {
      metric: "memory_usage"
      threshold: "1GB"
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "pattern_optimization"
      enabled: true
      target_efficiency: 0.95
    },
    {
      strategy: "caching"
      enabled: true
      cache_size: "100MB"
      ttl: "1h"
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "log_parsing_patterns" {
  patterns: [
    {
      name: "format_detection"
      description: "格式检测模式"
      implementation: {
        strategy: "pattern_matching"
        fallback: "default_parser"
        confidence_threshold: 0.8
      }
    },
    {
      name: "incremental_parsing"
      description: "增量解析模式"
      implementation: {
        strategy: "pipeline_processing"
        stages: ["detect", "parse", "validate", "transform"]
        error_recovery: true
      }
    },
    {
      name: "adaptive_parsing"
      description: "自适应解析模式"
      implementation: {
        strategy: "learning_based"
        feedback_loop: true
        pattern_evolution: true
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "over_parsing"
      description: "过度解析"
      symptoms: ["high_cpu_usage", "slow_processing"]
      solution: "optimize_patterns"
    },
    {
      name: "under_parsing"
      description: "解析不足"
      symptoms: ["missing_fields", "incomplete_data"]
      solution: "expand_patterns"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "parsing_monitoring" {
  metrics: [
    {
      name: "log_parsing_rate"
      type: "counter"
      labels: ["parser", "format", "status"]
      unit: "logs/sec"
    },
    {
      name: "parsing_latency"
      type: "histogram"
      labels: ["parser", "format"]
      buckets: [0.1, 0.5, 1, 5, 10, 50]
    },
    {
      name: "parsing_errors"
      type: "counter"
      labels: ["parser", "error_type"]
    },
    {
      name: "parsing_accuracy"
      type: "gauge"
      labels: ["parser", "format"]
      range: [0, 1]
    }
  ]
  
  alerts: [
    {
      name: "parsing_failure"
      condition: "parsing_errors > 0"
      severity: "critical"
      action: "restart_parser"
    },
    {
      name: "high_latency"
      condition: "parsing_latency > 100ms"
      severity: "warning"
      action: "optimize_patterns"
    },
    {
      name: "low_accuracy"
      condition: "parsing_accuracy < 0.9"
      severity: "warning"
      action: "review_patterns"
    }
  ]
}
```

## 主流标准映射

### ELK Stack集成

```dsl
elk_integration "elk_parsing" {
  elasticsearch: {
    index_pattern: "parsed-logs-*"
    template: {
      name: "parsed-logs"
      pattern: "parsed-logs-*"
      settings: {
        number_of_shards: 3
        number_of_replicas: 1
        refresh_interval: "5s"
      }
    }
  }
  
  logstash: {
    input: {
      type: "beats"
      port: 5044
      ssl: true
    }
    filter: [
      {
        type: "grok"
        pattern: "%{TIMESTAMP_ISO8601:timestamp} %{LOGLEVEL:level} %{GREEDYDATA:message}"
      },
      {
        type: "date"
        match: ["timestamp", "ISO8601"]
        target: "@timestamp"
      }
    ]
    output: {
      type: "elasticsearch"
      hosts: ["elasticsearch:9200"]
      index: "parsed-logs-%{+YYYY.MM.dd}"
    }
  }
  
  kibana: {
    index_pattern: "parsed-logs-*"
    time_field: "@timestamp"
    visualizations: [
      {
        name: "Parsing Success Rate"
        type: "line"
        x_axis: "@timestamp"
        y_axis: "parsing_success_rate"
      },
      {
        name: "Parsing Errors by Type"
        type: "pie"
        field: "error_type"
      }
    ]
  }
}
```

### Prometheus集成

```dsl
prometheus_integration "prometheus_parsing" {
  metrics: [
    {
      name: "log_parsing_duration_seconds"
      type: "histogram"
      help: "Log parsing execution time"
      labels: ["parser", "format", "status"]
    },
    {
      name: "log_parsing_events_total"
      type: "counter"
      help: "Total number of parsed log events"
      labels: ["parser", "format", "status"]
    },
    {
      name: "log_parsing_errors_total"
      type: "counter"
      help: "Total number of parsing errors"
      labels: ["parser", "error_type"]
    },
    {
      name: "log_parsing_accuracy"
      type: "gauge"
      help: "Parsing accuracy percentage"
      labels: ["parser", "format"]
    }
  ]
  
  rules: [
    {
      name: "High Parsing Error Rate"
      expr: "rate(log_parsing_errors_total[5m]) > 0.1"
      for: "2m"
      labels: { severity: warning }
      annotations: { summary: "High log parsing error rate" }
    },
    {
      name: "Parsing Accuracy Degraded"
      expr: "log_parsing_accuracy < 0.9"
      for: "5m"
      labels: { severity: critical }
      annotations: { summary: "Log parsing accuracy is degraded" }
    }
  ]
  
  alertmanager: {
    receivers: [
      {
        name: "slack"
        slack_configs: [
          {
            channel: "#alerts"
            title: "Log Parsing Alert"
            text: "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}"
          }
        ]
      }
    ]
  }
}
```

## 工程实践示例

### 微服务日志解析

```dsl
microservice_parsing "order_service_parsing" {
  description: "订单服务日志解析"
  
  services: [
    {
      name: "order-service"
      format: "json"
      parsers: [
        {
          name: "application_logs"
          type: "json"
          field_mapping: {
            timestamp: "@timestamp"
            level: "log.level"
            message: "message"
            trace_id: "trace.id"
            span_id: "span.id"
            user_id: "user.id"
            order_id: "order.id"
          }
        }
      ]
    },
    {
      name: "payment-service"
      format: "json"
      parsers: [
        {
          name: "payment_logs"
          type: "json"
          field_mapping: {
            timestamp: "@timestamp"
            level: "log.level"
            message: "message"
            payment_id: "payment.id"
            amount: "payment.amount"
            status: "payment.status"
          }
        }
      ]
    },
    {
      name: "inventory-service"
      format: "custom"
      parsers: [
        {
          name: "inventory_logs"
          type: "regex"
          pattern: "\\[(?<timestamp>.*?)\\] \\[(?<level>\\w+)\\] \\[(?<operation>\\w+)\\] (?<message>.*?) \\((?<duration>\\d+)ms\\)"
          field_mapping: {
            timestamp: "@timestamp"
            level: "log.level"
            operation: "inventory.operation"
            message: "message"
            duration: "inventory.duration"
          }
        }
      ]
    }
  ]
  
  correlation: {
    enabled: true
    correlation_key: "trace_id"
    services: ["order-service", "payment-service", "inventory-service"]
    time_window: "5m"
  }
  
  validation: {
    required_fields: ["@timestamp", "log.level", "message"]
    field_types: {
      "@timestamp": "datetime"
      "log.level": "string"
      "message": "string"
    }
  }
  
  transformation: [
    {
      name: "normalize_timestamp"
      type: "timestamp"
      field: "@timestamp"
      format: "ISO8601"
      timezone: "UTC"
    },
    {
      name: "normalize_level"
      type: "enum"
      field: "log.level"
      mapping: {
        "ERROR": "error"
        "WARN": "warn"
        "INFO": "info"
        "DEBUG": "debug"
      }
    },
    {
      name: "add_service_metadata"
      type: "field_addition"
      fields: {
        service_name: "service.name"
        environment: "production"
        data_center: "us-east-1"
      }
    }
  ]
  
  output: {
    format: "structured"
    destination: "elasticsearch"
    index: "microservice-logs"
    template: {
      name: "microservice-logs"
      pattern: "microservice-logs-*"
      settings: {
        number_of_shards: 3
        number_of_replicas: 1
        refresh_interval: "5s"
      }
    }
  }
  
  monitoring: {
    metrics: [
      "parsing_success_rate",
      "parsing_latency",
      "field_extraction_rate",
      "correlation_success_rate"
    ]
    alerting: {
      on_parsing_failure: {
        threshold: 0.01
        severity: "critical"
        notification: "pagerduty"
      }
      on_high_latency: {
        threshold: "100ms"
        severity: "warning"
        notification: "slack"
      }
    }
  }
}
```

这个DSL设计提供了完整的日志解析建模能力，支持多种日志格式、解析策略、字段映射、数据转换，并能够与主流日志解析平台无缝集成。
