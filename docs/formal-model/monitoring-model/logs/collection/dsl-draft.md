# 日志收集建模DSL草案

## 1. 设计目标

- 用声明式语法描述日志采集源、协议、策略、调度等流程
- 支持多源异构日志统一采集建模
- 便于自动生成采集与调度配置
- 支持采集优化、负载均衡、故障恢复等高级特性

## 2. 基本语法结构

```dsl
log_collection "web_service_collection" {
  description: "Web服务日志收集"
  version: "1.0.0"
  author: "system"
  
  sources: [
    {
      name: "application_logs"
      type: "file"
      path: "/var/log/webapp/app.log"
      format: "json"
      encoding: "utf-8"
      rotation: {
        enabled: true
        max_size: "100MB"
        max_files: 10
      }
    },
    {
      name: "access_logs"
      type: "file"
      path: "/var/log/nginx/access.log"
      format: "nginx"
      encoding: "utf-8"
    }
  ]
  
  agent: {
    type: "fluentd"
    version: "1.14"
    resources: {
      cpu: "100m"
      memory: "128Mi"
    }
    replicas: 2
  }
  
  policy: {
    sampling: {
      enabled: true
      rate: 0.1
      max_events_per_second: 1000
    }
    filtering: {
      enabled: true
      rules: [
        {
          name: "exclude_debug"
          condition: "level != 'DEBUG'"
          action: "include"
        }
      ]
    }
    buffering: {
      enabled: true
      buffer_size: "100MB"
      flush_interval: "5s"
      retry_max_times: 3
    }
  }
  
  schedule: {
    type: "continuous"
    interval: "1s"
    batch_size: 1000
    batch_timeout: "5s"
  }
  
  routing: {
    enabled: true
    rules: [
      {
        name: "error_logs"
        condition: "level in ['ERROR', 'FATAL']"
        destination: "error_processing"
        priority: "high"
      }
    ]
  }
  
  destinations: [
    {
      name: "elasticsearch"
      type: "elasticsearch"
      endpoint: "http://elasticsearch:9200"
      index: "web-service-logs"
      bulk_size: 1000
      retry_on_failure: true
    }
  ]
  
  monitoring: {
    enabled: true
    metrics: [
      "collection_rate",
      "processing_latency",
      "error_rate",
      "buffer_usage"
    ]
    alerts: [
      {
        name: "high_error_rate"
        condition: "error_rate > 0.05"
        duration: "5m"
      }
    ]
  }
}
```

## 3. 关键元素

- log_collection：日志收集声明
- description：描述信息
- version：版本号
- author：作者
- sources：日志源配置
- agent：采集代理配置
- policy：采集策略
- schedule：采集调度
- routing：路由规则
- destinations：目标配置
- monitoring：监控配置

## 4. 高级用法

### 4.1 分布式日志收集

```dsl
log_collection "distributed_system_collection" {
  description: "分布式系统日志收集"
  version: "1.0.0"
  author: "system"
  
  sources: [
    {
      name: "web_service_logs"
      type: "file"
      path: "/var/log/web-service/app.log"
      format: "json"
      service: "web-service"
      environment: "production"
    },
    {
      name: "api_service_logs"
      type: "file"
      path: "/var/log/api-service/app.log"
      format: "json"
      service: "api-service"
      environment: "production"
    }
  ]
  
  agent: {
    type: "fluentd"
    version: "1.14"
    deployment: {
      strategy: "DaemonSet"
      resources: {
        cpu: "200m"
        memory: "256Mi"
      }
    }
  }
  
  policy: {
    sampling: {
      enabled: true
      strategy: "adaptive"
      base_rate: 0.1
      max_rate: 0.5
    }
    filtering: {
      enabled: true
      rules: [
        {
          name: "exclude_debug"
          condition: "level != 'DEBUG'"
          action: "include"
        }
      ]
    }
  }
  
  destinations: [
    {
      name: "elasticsearch"
      type: "elasticsearch"
      endpoint: "http://elasticsearch:9200"
      index: "distributed-logs"
      bulk_size: 2000
    }
  ]
}
```

### 4.2 实时日志流收集

```dsl
log_collection "real_time_stream_collection" {
  description: "实时日志流收集"
  version: "1.0.0"
  author: "system"
  
  sources: [
    {
      name: "kafka_logs"
      type: "kafka"
      brokers: ["kafka:9092"]
      topic: "application-logs"
      consumer_group: "log-collector"
    },
    {
      name: "syslog"
      type: "syslog"
      port: 514
      protocol: "udp"
    }
  ]
  
  agent: {
    type: "otel_collector"
    version: "0.80"
    deployment: {
      strategy: "Deployment"
      replicas: 3
    }
  }
  
  schedule: {
    type: "real_time"
    batch_size: 100
    batch_timeout: "1s"
  }
  
  destinations: [
    {
      name: "elasticsearch"
      type: "elasticsearch"
      endpoint: "http://elasticsearch:9200"
      index: "realtime-logs"
      bulk_size: 100
    }
  ]
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

<filter **>
  @type record_transformer
  <record>
    service "web-service"
    environment "production"
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

### 5.2 Kubernetes部署配置生成

```yaml
# fluentd-daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: fluentd
  namespace: logging
spec:
  selector:
    matchLabels:
      app: fluentd
  template:
    metadata:
      labels:
        app: fluentd
    spec:
      containers:
      - name: fluentd
        image: fluent/fluentd-kubernetes-daemonset:v1.14-debian-elasticsearch7-1
        env:
          - name: FLUENT_ELASTICSEARCH_HOST
            value: "elasticsearch"
          - name: FLUENT_ELASTICSEARCH_PORT
            value: "9200"
        resources:
          limits:
            memory: 256Mi
          requests:
            cpu: 100m
            memory: 128Mi
        volumeMounts:
        - name: varlog
          mountPath: /var/log
      volumes:
      - name: varlog
        hostPath:
          path: /var/log
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - log_collection.name
    - log_collection.description
    - log_collection.version
    - log_collection.sources
  
  type_constraints:
    - field: "log_collection.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "log_collection.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "log_collection.sources[].type"
      type: "string"
      enum: ["file", "kafka", "syslog", "http", "tcp", "udp"]
```

### 6.2 收集验证规则

```yaml
collection_validation:
  source_consistency:
    - rule: "all source paths must be valid"
    - rule: "source formats must be supported"
    - rule: "source types must be valid"
  
  agent_validation:
    - rule: "agent type must be supported"
    - rule: "agent version must be valid"
    - rule: "agent resources must be sufficient"
  
  policy_validation:
    - rule: "sampling rate must be between 0 and 1"
    - rule: "filter conditions must be valid"
    - rule: "buffer size must be positive"
```

## 7. 最佳实践

### 7.1 收集设计模式

```dsl
# 基础收集模式
log_collection "basic_collection" {
  description: "基础日志收集"
  version: "1.0.0"
  
  sources: [
    {
      name: "app_logs"
      type: "file"
      path: "/var/log/app/app.log"
      format: "json"
    }
  ]
  
  agent: {
    type: "fluentd"
    version: "1.14"
  }
  
  destinations: [
    {
      name: "elasticsearch"
      type: "elasticsearch"
      endpoint: "http://elasticsearch:9200"
      index: "app-logs"
    }
  ]
}

# 分布式收集模式
log_collection "distributed_collection" {
  description: "分布式日志收集"
  version: "1.0.0"
  
  sources: [
    {
      name: "service_logs"
      type: "file"
      path: "/var/log/service/app.log"
      format: "json"
    }
  ]
  
  agent: {
    type: "fluentd"
    version: "1.14"
    deployment: {
      strategy: "DaemonSet"
    }
  }
  
  routing: {
    enabled: true
    rules: [
      {
        name: "error_logs"
        condition: "level == 'ERROR'"
        destination: "error_processing"
      }
    ]
  }
  
  destinations: [
    {
      name: "elasticsearch"
      type: "elasticsearch"
      endpoint: "http://elasticsearch:9200"
      index: "service-logs"
    }
  ]
}
```

### 7.2 收集命名规范

```dsl
# 推荐命名模式
log_collection "service_component_collection" {
  # 服务_组件_收集
}

log_collection "environment_type_collection" {
  # 环境_类型_收集
}

log_collection "domain_workflow_collection" {
  # 领域_工作流_收集
}
```

## 8. 与主流标准的映射

| DSL元素 | Fluentd | Logstash | OpenTelemetry | ELK Stack |
|---------|---------|----------|---------------|-----------|
| log_collection | source | input | receiver | input |
| sources | source | input | receiver | input |
| agent | agent | agent | service | agent |
| policy | filter | filter | processor | filter |
| destinations | output | output | exporter | output |

## 9. 工程实践示例

```dsl
# 生产环境日志收集配置示例
log_collection "production_log_collection" {
  description: "生产环境日志收集"
  version: "1.0.0"
  author: "system"
  
  sources: [
    {
      name: "web_service_logs"
      type: "file"
      path: "/var/log/web-service/app.log"
      format: "json"
      encoding: "utf-8"
      service: "web-service"
      environment: "production"
      rotation: {
        enabled: true
        max_size: "500MB"
        max_files: 20
        compress: true
      }
    },
    {
      name: "api_service_logs"
      type: "file"
      path: "/var/log/api-service/app.log"
      format: "json"
      encoding: "utf-8"
      service: "api-service"
      environment: "production"
      rotation: {
        enabled: true
        max_size: "500MB"
        max_files: 20
        compress: true
      }
    }
  ]
  
  agent: {
    type: "fluentd"
    version: "1.14"
    deployment: {
      strategy: "DaemonSet"
      resources: {
        cpu: "500m"
        memory: "1Gi"
      }
    }
    configuration: {
      workers: 8
      buffer_size: "1GB"
      flush_interval: "10s"
      retry_max_times: 10
    }
  }
  
  policy: {
    sampling: {
      enabled: true
      strategy: "adaptive"
      base_rate: 0.1
      max_rate: 0.5
      min_rate: 0.01
      target_events_per_second: 50000
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
          sampling_rate: 1.0
        }
      ]
    }
    buffering: {
      enabled: true
      buffer_size: "2GB"
      flush_interval: "10s"
      retry_max_times: 10
      retry_exponential_backoff: true
    }
    compression: {
      enabled: true
      algorithm: "gzip"
      level: 6
    }
  }
  
  schedule: {
    type: "continuous"
    interval: "1s"
    batch_size: 5000
    batch_timeout: "10s"
    max_retries: 5
  }
  
  routing: {
    enabled: true
    rules: [
      {
        name: "critical_errors"
        condition: "level == 'FATAL'"
        destination: "critical_processing"
        priority: "critical"
        immediate: true
      },
      {
        name: "error_logs"
        condition: "level == 'ERROR'"
        destination: "error_processing"
        priority: "high"
      },
      {
        name: "performance_logs"
        condition: "message contains 'response_time'"
        destination: "performance_processing"
        priority: "normal"
      },
      {
        name: "default_logs"
        condition: "true"
        destination: "default_processing"
        priority: "low"
      }
    ]
    load_balancing: {
      enabled: true
      strategy: "round_robin"
      health_check: {
        enabled: true
        interval: "30s"
        timeout: "5s"
      }
    }
  }
  
  destinations: [
    {
      name: "elasticsearch"
      type: "elasticsearch"
      endpoint: "http://elasticsearch:9200"
      index: "production-logs"
      bulk_size: 5000
      retry_on_failure: true
      compression: true
      timeout: "30s"
      max_retries: 5
    },
    {
      name: "kafka"
      type: "kafka"
      brokers: ["kafka-1:9092", "kafka-2:9092", "kafka-3:9092"]
      topic: "production-logs"
      partition: 0
      acks: "all"
      compression: "snappy"
      batch_size: 10000
    },
    {
      name: "s3_backup"
      type: "s3"
      bucket: "logs-backup"
      region: "us-east-1"
      path: "logs/{YYYY}/{MM}/{DD}"
      compression: "gzip"
      retention: "365d"
    }
  ]
  
  failover: {
    enabled: true
    primary: "elasticsearch"
    secondary: "kafka"
    tertiary: "s3_backup"
    health_check_interval: "30s"
    failover_timeout: "5s"
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "collection_rate",
      "processing_latency",
      "error_rate",
      "buffer_usage",
      "destination_health",
      "throughput"
    ]
    alerts: [
      {
        name: "high_error_rate"
        condition: "error_rate > 0.05"
        duration: "5m"
        severity: "warning"
      },
      {
        name: "buffer_full"
        condition: "buffer_usage > 0.9"
        duration: "2m"
        severity: "critical"
      },
      {
        name: "destination_unhealthy"
        condition: "destination_health == 'unhealthy'"
        duration: "1m"
        severity: "critical"
      }
    ]
    dashboards: [
      "https://grafana.example.com/d/log-collection"
    ]
  }
  
  security: {
    enabled: true
    authentication: {
      type: "service_account"
      service_account: "log-collector"
      namespace: "logging"
    }
    encryption: {
      enabled: true
      algorithm: "AES-256"
      key_rotation: "30d"
    }
    access_control: {
      enabled: true
      rbac: {
        enabled: true
        service_account: "log-collector"
        namespace: "logging"
      }
    }
  }
}
```

这个DSL设计为日志收集建模提供了完整的配置语言，支持基础收集、分布式收集、实时流收集等多种模式，同时保持了良好的可扩展性和可维护性。
