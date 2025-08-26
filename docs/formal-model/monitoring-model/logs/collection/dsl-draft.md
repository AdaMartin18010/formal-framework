# 日志收集建模DSL设计

## 设计目标

日志收集建模DSL旨在提供声明式语言定义复杂的日志收集配置，支持多种日志源、收集策略、数据转换、传输协议，并与主流日志收集平台无缝集成。

## 基本语法

### 核心结构

```dsl
log_collection "web_service_collection" {
  description: "Web服务日志收集"
  version: "1.0.0"
  
  sources: [
    {
      name: "application_logs"
      type: "file"
      path: "/var/log/webapp/app.log"
      format: "json"
      encoding: "utf-8"
    }
  ]
  
  agents: [
    {
      name: "filebeat_agent"
      type: "filebeat"
      version: "7.17.0"
      resources: {
        cpu: "100m"
        memory: "128Mi"
      }
    }
  ]
  
  policies: [
    {
      name: "real_time_collection"
      type: "continuous"
      interval: "1s"
      batch_size: 1000
    }
  ]
  
  output: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    index: "web-service-logs"
  }
}
```

### 日志源定义

```dsl
log_source "application_logs" {
  description: "应用程序日志源"
  
  type: "file"
  path: "/var/log/webapp/app.log"
  format: "json"
  encoding: "utf-8"
  
  discovery: {
    enabled: true
    pattern: "*.log"
    recursive: true
    max_depth: 3
  }
  
  monitoring: {
    file_size: true
    file_age: true
    rotation_detection: true
  }
  
  labels: {
    service: "web-service"
    environment: "production"
    component: "application"
  }
  
  metadata: {
    hostname: "${HOSTNAME}"
    pod_name: "${POD_NAME}"
    namespace: "${NAMESPACE}"
  }
}
```

### 收集代理

```dsl
collection_agent "filebeat_agent" {
  description: "Filebeat收集代理"
  
  type: "filebeat"
  version: "7.17.0"
  
  deployment: {
    mode: "daemonset"
    replicas: 1
    node_selector: {
      app: "web-service"
    }
  }
  
  resources: {
    requests: {
      cpu: "100m"
      memory: "128Mi"
    }
    limits: {
      cpu: "500m"
      memory: "512Mi"
    }
  }
  
  configuration: {
    logging: {
      level: "info"
      to_files: true
      to_syslog: false
    }
    
    monitoring: {
      enabled: true
      metrics: ["beat", "libbeat", "filebeat"]
    }
    
    queue: {
      mem: {
        events: 4096
        flush: {
          min_events: 512
          timeout: "1s"
        }
      }
    }
  }
  
  security: {
    ssl: {
      enabled: true
      certificate_authorities: ["/etc/ssl/certs/ca.crt"]
      certificate: "/etc/ssl/certs/filebeat.crt"
      key: "/etc/ssl/private/filebeat.key"
    }
  }
}
```

### 收集策略

```dsl
collection_policy "real_time_collection" {
  description: "实时收集策略"
  
  type: "continuous"
  interval: "1s"
  batch_size: 1000
  max_batch_size: 5000
  
  scheduling: {
    mode: "real_time"
    backoff: {
      initial: "1s"
      max: "30s"
      multiplier: 2
    }
  }
  
  filtering: {
    include: [
      "level:ERROR",
      "level:WARN",
      "service:web-service"
    ]
    exclude: [
      "message:health_check",
      "message:heartbeat"
    ]
  }
  
  sampling: {
    enabled: false
    rate: 1.0
    seed: 42
  }
  
  buffering: {
    enabled: true
    max_size: "100MB"
    flush_interval: "5s"
    max_age: "30s"
  }
}
```

### 数据转换

```dsl
data_transformation "log_enrichment" {
  description: "日志数据增强"
  
  processors: [
    {
      name: "add_host_metadata"
      type: "add_host_metadata"
      fields: ["hostname", "os", "architecture"]
    },
    {
      name: "add_kubernetes_metadata"
      type: "add_kubernetes_metadata"
      fields: ["pod_name", "namespace", "service_name"]
    },
    {
      name: "add_timestamp"
      type: "timestamp"
      field: "@timestamp"
      layouts: ["2006-01-02T15:04:05.000Z"]
    },
    {
      name: "parse_json"
      type: "json"
      target: "parsed"
      overwrite_keys: true
    },
    {
      name: "add_fields"
      type: "add_fields"
      fields: {
        environment: "production"
        data_center: "us-east-1"
        collection_agent: "filebeat"
      }
    }
  ]
  
  validation: {
    required_fields: ["timestamp", "level", "message"]
    field_types: {
      timestamp: "datetime"
      level: "string"
      message: "string"
    }
  }
  
  error_handling: {
    on_error: "drop"
    error_log: true
    error_metrics: true
  }
}
```

## 高级用法

### 多源收集

```dsl
multi_source_collection "comprehensive_logging" {
  description: "综合日志收集"
  
  sources: [
    {
      name: "application_logs"
      type: "file"
      path: "/var/log/webapp/app.log"
      format: "json"
      priority: "high"
    },
    {
      name: "access_logs"
      type: "file"
      path: "/var/log/nginx/access.log"
      format: "nginx"
      priority: "medium"
    },
    {
      name: "system_logs"
      type: "file"
      path: "/var/log/syslog"
      format: "syslog"
      priority: "low"
    },
    {
      name: "docker_logs"
      type: "docker"
      containers: ["web-service", "database-service"]
      format: "json"
      priority: "high"
    },
    {
      name: "kubernetes_logs"
      type: "kubernetes"
      namespace: "web-service"
      format: "json"
      priority: "high"
    }
  ]
  
  routing: {
    strategy: "priority_based"
    rules: [
      {
        condition: "priority == 'high'"
        output: "elasticsearch_primary"
        backup: "elasticsearch_backup"
      },
      {
        condition: "priority == 'medium'"
        output: "elasticsearch_secondary"
      },
      {
        condition: "priority == 'low'"
        output: "elasticsearch_archive"
      }
    ]
  }
  
  load_balancing: {
    enabled: true
    strategy: "round_robin"
    health_checks: true
    failover: true
  }
}
```

### 分布式收集

```dsl
distributed_collection "cluster_logging" {
  description: "集群日志收集"
  
  topology: {
    type: "hierarchical"
    levels: [
      {
        name: "edge"
        role: "collector"
        agents: ["filebeat", "fluent-bit"]
      },
      {
        name: "aggregator"
        role: "aggregator"
        agents: ["fluentd", "logstash"]
      },
      {
        name: "storage"
        role: "storage"
        systems: ["elasticsearch", "opensearch"]
      }
    ]
  }
  
  edge_collectors: [
    {
      name: "node_collector"
      type: "daemonset"
      selector: {
        app: "log-collector"
      }
      resources: {
        cpu: "200m"
        memory: "256Mi"
      }
      configuration: {
        sources: ["application_logs", "system_logs"]
        output: "aggregator_service"
        compression: true
        encryption: true
      }
    }
  ]
  
  aggregators: [
    {
      name: "log_aggregator"
      type: "deployment"
      replicas: 3
      resources: {
        cpu: "500m"
        memory: "1Gi"
      }
      configuration: {
        input: {
          type: "forward"
          port: 24224
          ssl: true
        }
        processing: {
          parsing: true
          filtering: true
          enrichment: true
        }
        output: {
          type: "elasticsearch"
          endpoints: ["elasticsearch-1:9200", "elasticsearch-2:9200"]
          load_balance: true
        }
      }
    }
  ]
  
  coordination: {
    service_discovery: {
      type: "kubernetes"
      namespace: "logging"
    }
    health_monitoring: {
      enabled: true
      interval: "30s"
      timeout: "10s"
    }
    failover: {
      enabled: true
      strategy: "active_passive"
      automatic: true
    }
  }
}
```

### 实时流收集

```dsl
stream_collection "real_time_streaming" {
  description: "实时流收集"
  
  streaming: {
    engine: "kafka_connect"
    mode: "real_time"
    parallelism: 4
  }
  
  sources: [
    {
      name: "log_stream"
      type: "kafka"
      topic: "raw-logs"
      consumer_group: "log-collectors"
      auto_offset_reset: "latest"
    },
    {
      name: "event_stream"
      type: "kafka"
      topic: "application-events"
      consumer_group: "event-collectors"
      auto_offset_reset: "latest"
    }
  ]
  
  processing: [
    {
      name: "log_parser"
      type: "stream_processor"
      input: "log_stream"
      output: "parsed_logs"
      operations: [
        {
          type: "parse_json"
          field: "message"
        },
        {
          type: "add_timestamp"
          field: "@timestamp"
        },
        {
          type: "filter"
          condition: "level in ['ERROR', 'WARN', 'INFO']"
        }
      ]
    },
    {
      name: "event_enricher"
      type: "stream_processor"
      input: "event_stream"
      output: "enriched_events"
      operations: [
        {
          type: "join"
          with: "user_context"
          on: "user_id"
        },
        {
          type: "aggregate"
          window: "5m"
          group_by: ["event_type", "user_id"]
          metrics: ["count", "sum"]
        }
      ]
    }
  ]
  
  outputs: [
    {
      name: "elasticsearch_sink"
      type: "elasticsearch"
      topic: "parsed_logs"
      endpoint: "http://elasticsearch:9200"
      index: "stream-logs"
      batch_size: 1000
      flush_interval: "5s"
    },
    {
      name: "kafka_sink"
      type: "kafka"
      topic: "enriched_events"
      endpoint: "kafka:9092"
      acks: "all"
      compression: "snappy"
    }
  ]
  
  monitoring: {
    metrics: [
      "records_consumed",
      "records_produced",
      "processing_latency",
      "error_rate"
    ]
    alerting: {
      on_lag: true
      on_error_rate: true
      on_latency: true
    }
  }
}
```

## 代码生成模板

### Filebeat配置

```yaml
# 生成的Filebeat配置
filebeat.inputs:
  - type: log
    enabled: true
    paths:
      - /var/log/webapp/app.log
    json.keys_under_root: true
    json.add_error_key: true
    json.message_key: message
    fields:
      service: web-service
      environment: production
      component: application
    fields_under_root: true
    multiline.pattern: '^\['
    multiline.negate: true
    multiline.match: after
    processors:
      - add_host_metadata:
          when.not.contains.tags: forwarded
      - add_kubernetes_metadata:
          host: ${NODE_NAME}
          matchers:
          - logs_path:
              logs_path: "/var/log/containers/"
      - timestamp:
          field: timestamp
          layouts:
            - "2006-01-02T15:04:05.000Z"
          test:
            - "2024-01-01T12:00:00.000Z"
      - add_fields:
          fields:
            environment: production
            data_center: us-east-1
            collection_agent: filebeat

filebeat.config:
  modules:
    path: ${path.config}/modules.d/*.yml
    reload.enabled: false

setup.kibana:
  host: "kibana:5601"

setup.dashboards.enabled: true
setup.template.enabled: true

output.elasticsearch:
  hosts: ["elasticsearch:9200"]
  protocol: "https"
  ssl.certificate_authorities: ["/etc/ssl/certs/ca.crt"]
  ssl.certificate: "/etc/ssl/certs/filebeat.crt"
  ssl.key: "/etc/ssl/private/filebeat.key"
  index: "web-service-logs-%{+yyyy.MM.dd}"
  template.name: "web-service-logs"
  template.pattern: "web-service-logs-*"
  template.enabled: true
  template.overwrite: true

logging.level: info
logging.to_files: true
logging.files:
  path: /var/log/filebeat
  name: filebeat
  keepfiles: 7
  permissions: 0644

monitoring.enabled: true
monitoring.metrics.enabled: true
monitoring.logging.enabled: true

queue.mem:
  events: 4096
  flush.min_events: 512
  flush.timeout: 1s
```

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

<source>
  @type tail
  path /var/log/nginx/access.log
  pos_file /var/log/fluentd/nginx.log.pos
  tag nginx.access
  read_from_head true
  <parse>
    @type nginx
  </parse>
</source>

<filter web-service.logs>
  @type record_transformer
  <record>
    service web-service
    environment production
    component application
    hostname "#{Socket.gethostname}"
    timestamp ${time}
  </record>
</filter>

<filter **>
  @type grep
  <regexp>
    key level
    pattern /ERROR|WARN|INFO/
  </regexp>
</filter>

<match web-service.logs>
  @type elasticsearch
  host elasticsearch
  port 9200
  logstash_format true
  logstash_prefix web-service-logs
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

<match nginx.access>
  @type elasticsearch
  host elasticsearch
  port 9200
  logstash_format true
  logstash_prefix nginx-access
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

### Kubernetes DaemonSet

```yaml
# 生成的Kubernetes DaemonSet
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: log-collector
  namespace: logging
  labels:
    app: log-collector
spec:
  selector:
    matchLabels:
      app: log-collector
  template:
    metadata:
      labels:
        app: log-collector
    spec:
      serviceAccountName: log-collector
      containers:
      - name: filebeat
        image: docker.elastic.co/beats/filebeat:7.17.0
        args:
          - "-c"
          - "/etc/filebeat/filebeat.yml"
          - "-e"
        env:
        - name: NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: POD_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        resources:
          requests:
            cpu: 100m
            memory: 128Mi
          limits:
            cpu: 500m
            memory: 512Mi
        volumeMounts:
        - name: filebeat-config
          mountPath: /etc/filebeat
        - name: filebeat-data
          mountPath: /usr/share/filebeat/data
        - name: var-logs
          mountPath: /var/log
          readOnly: true
        - name: var-lib-docker-containers
          mountPath: /var/lib/docker/containers
          readOnly: true
        - name: ssl-certs
          mountPath: /etc/ssl/certs
          readOnly: true
        - name: ssl-private
          mountPath: /etc/ssl/private
          readOnly: true
        securityContext:
          runAsUser: 0
          privileged: false
          readOnlyRootFilesystem: false
      volumes:
      - name: filebeat-config
        configMap:
          name: filebeat-config
      - name: filebeat-data
        emptyDir: {}
      - name: var-logs
        hostPath:
          path: /var/log
      - name: var-lib-docker-containers
        hostPath:
          path: /var/lib/docker/containers
      - name: ssl-certs
        secret:
          secretName: ssl-certs
      - name: ssl-private
        secret:
          secretName: ssl-private
      tolerations:
      - key: node-role.kubernetes.io/master
        effect: NoSchedule
      - key: node-role.kubernetes.io/control-plane
        effect: NoSchedule
---
apiVersion: v1
kind: ConfigMap
metadata:
  name: filebeat-config
  namespace: logging
data:
  filebeat.yml: |
    filebeat.inputs:
    - type: log
      enabled: true
      paths:
        - /var/log/containers/*.log
      json.keys_under_root: true
      json.add_error_key: true
      json.message_key: message
      fields:
        service: web-service
        environment: production
      fields_under_root: true
      processors:
        - add_kubernetes_metadata:
            host: ${NODE_NAME}
            matchers:
            - logs_path:
                logs_path: "/var/log/containers/"
        - timestamp:
            field: timestamp
            layouts:
              - "2006-01-02T15:04:05.000Z"
        - add_fields:
            fields:
              environment: production
              collection_agent: filebeat

    output.elasticsearch:
      hosts: ["elasticsearch:9200"]
      protocol: "https"
      ssl.certificate_authorities: ["/etc/ssl/certs/ca.crt"]
      ssl.certificate: "/etc/ssl/certs/filebeat.crt"
      ssl.key: "/etc/ssl/private/filebeat.key"
      index: "web-service-logs-%{+yyyy.MM.dd}"

    logging.level: info
    monitoring.enabled: true
```

### Docker Compose

```yaml
# 生成的Docker Compose配置
version: '3.8'

services:
  filebeat:
    image: docker.elastic.co/beats/filebeat:7.17.0
    container_name: filebeat
    user: root
    volumes:
      - ./filebeat.yml:/usr/share/filebeat/filebeat.yml:ro
      - /var/log:/var/log:ro
      - /var/lib/docker/containers:/var/lib/docker/containers:ro
      - filebeat-data:/usr/share/filebeat/data
      - ./ssl:/etc/ssl:ro
    environment:
      - NODE_NAME=${HOSTNAME}
    networks:
      - logging
    depends_on:
      - elasticsearch
    restart: unless-stopped

  fluentd:
    image: fluent/fluentd:v1.14-1
    container_name: fluentd
    volumes:
      - ./fluentd.conf:/fluentd/etc/fluent.conf:ro
      - ./fluentd:/fluentd/log
      - /var/log:/var/log:ro
      - ./ssl:/etc/ssl:ro
    environment:
      - FLUENTD_CONF=fluent.conf
    networks:
      - logging
    depends_on:
      - elasticsearch
    restart: unless-stopped

  elasticsearch:
    image: docker.elastic.co/elasticsearch/elasticsearch:7.17.0
    container_name: elasticsearch
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
      - "ES_JAVA_OPTS=-Xms512m -Xmx512m"
    volumes:
      - elasticsearch-data:/usr/share/elasticsearch/data
    networks:
      - logging
    ports:
      - "9200:9200"
    restart: unless-stopped

  kibana:
    image: docker.elastic.co/kibana/kibana:7.17.0
    container_name: kibana
    environment:
      - ELASTICSEARCH_HOSTS=http://elasticsearch:9200
    networks:
      - logging
    ports:
      - "5601:5601"
    depends_on:
      - elasticsearch
    restart: unless-stopped

volumes:
  filebeat-data:
  elasticsearch-data:

networks:
  logging:
    driver: bridge
```

## 验证规则

### 语法验证

```dsl
validation_rules "log_collection_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "version", "sources", "agents"]
      message: "必须包含描述、版本、日志源和收集代理"
    },
    {
      rule: "valid_source_type"
      allowed_types: ["file", "docker", "kubernetes", "syslog", "tcp", "udp"]
      message: "日志源类型必须是支持的类型"
    },
    {
      rule: "valid_agent_type"
      allowed_types: ["filebeat", "fluentd", "fluent-bit", "logstash"]
      message: "收集代理类型必须是支持的类型"
    }
  ]
  
  semantic: [
    {
      rule: "path_validity"
      condition: "source.path exists and readable"
      message: "日志文件路径必须存在且可读"
    },
    {
      rule: "agent_compatibility"
      condition: "agent supports source type"
      message: "收集代理必须支持指定的日志源类型"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "collection_performance" {
  constraints: [
    {
      metric: "collection_latency"
      threshold: "5s"
      action: "warn"
    },
    {
      metric: "throughput"
      threshold: "10000 events/sec"
      action: "error"
    },
    {
      metric: "resource_usage"
      threshold: "80%"
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "batch_optimization"
      enabled: true
      optimal_batch_size: 1000
      optimal_interval: "5s"
    },
    {
      strategy: "compression"
      enabled: true
      algorithm: "gzip"
      level: 6
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "log_collection_patterns" {
  patterns: [
    {
      name: "sidecar_collection"
      description: "Sidecar收集模式"
      implementation: {
        strategy: "container_sidecar"
        shared_volumes: true
        resource_sharing: true
      }
    },
    {
      name: "daemon_collection"
      description: "Daemon收集模式"
      implementation: {
        strategy: "node_daemon"
        host_path_mounting: true
        privileged_access: false
      }
    },
    {
      name: "gateway_collection"
      description: "网关收集模式"
      implementation: {
        strategy: "centralized_gateway"
        load_balancing: true
        failover: true
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "over_collection"
      description: "过度收集"
      symptoms: ["high_resource_usage", "network_congestion"]
      solution: "implement_filtering"
    },
    {
      name: "under_collection"
      description: "收集不足"
      symptoms: ["missing_logs", "incomplete_data"]
      solution: "expand_coverage"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "collection_monitoring" {
  metrics: [
    {
      name: "log_collection_rate"
      type: "counter"
      labels: ["source", "agent", "status"]
      unit: "events/sec"
    },
    {
      name: "collection_latency"
      type: "histogram"
      labels: ["source", "agent"]
      buckets: [0.1, 0.5, 1, 5, 10, 30]
    },
    {
      name: "collection_errors"
      type: "counter"
      labels: ["source", "agent", "error_type"]
    },
    {
      name: "buffer_usage"
      type: "gauge"
      labels: ["agent"]
      range: [0, 1]
    }
  ]
  
  alerts: [
    {
      name: "collection_failure"
      condition: "collection_errors > 0"
      severity: "critical"
      action: "restart_agent"
    },
    {
      name: "high_latency"
      condition: "collection_latency > 10s"
      severity: "warning"
      action: "optimize_configuration"
    },
    {
      name: "buffer_full"
      condition: "buffer_usage > 0.9"
      severity: "warning"
      action: "increase_buffer_size"
    }
  ]
}
```

## 主流标准映射

### ELK Stack集成

```dsl
elk_integration "elk_collection" {
  elasticsearch: {
    endpoint: "http://elasticsearch:9200"
    index_pattern: "web-service-logs-*"
    template: {
      name: "web-service-logs"
      pattern: "web-service-logs-*"
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
      index: "web-service-logs-%{+YYYY.MM.dd}"
    }
  }
  
  kibana: {
    index_pattern: "web-service-logs-*"
    time_field: "@timestamp"
    visualizations: [
      {
        name: "Log Volume Over Time"
        type: "line"
        x_axis: "@timestamp"
        y_axis: "count"
      },
      {
        name: "Error Rate by Service"
        type: "pie"
        field: "service"
        filter: "level:ERROR"
      }
    ]
  }
}
```

### Prometheus集成

```dsl
prometheus_integration "prometheus_collection" {
  metrics: [
    {
      name: "log_collection_duration_seconds"
      type: "histogram"
      help: "Log collection execution time"
      labels: ["source", "agent", "status"]
    },
    {
      name: "log_collection_events_total"
      type: "counter"
      help: "Total number of collected log events"
      labels: ["source", "agent", "level"]
    },
    {
      name: "log_collection_errors_total"
      type: "counter"
      help: "Total number of collection errors"
      labels: ["source", "agent", "error_type"]
    },
    {
      name: "log_collection_buffer_usage"
      type: "gauge"
      help: "Buffer usage percentage"
      labels: ["agent"]
    }
  ]
  
  rules: [
    {
      name: "High Collection Error Rate"
      expr: "rate(log_collection_errors_total[5m]) > 0.1"
      for: "2m"
      labels: { severity: warning }
      annotations: { summary: "High log collection error rate" }
    },
    {
      name: "Collection Buffer Full"
      expr: "log_collection_buffer_usage > 0.9"
      for: "1m"
      labels: { severity: critical }
      annotations: { summary: "Log collection buffer is full" }
    }
  ]
  
  alertmanager: {
    receivers: [
      {
        name: "slack"
        slack_configs: [
          {
            channel: "#alerts"
            title: "Log Collection Alert"
            text: "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}"
          }
        ]
      }
    ]
  }
}
```

### Kubernetes集成

```dsl
kubernetes_integration "k8s_collection" {
  cluster_logging: {
    enabled: true
    namespace: "logging"
    service_account: "log-collector"
  }
  
  daemonset: {
    name: "log-collector"
    image: "docker.elastic.co/beats/filebeat:7.17.0"
    resources: {
      requests: { cpu: "100m", memory: "128Mi" }
      limits: { cpu: "500m", memory: "512Mi" }
    }
    volume_mounts: [
      {
        name: "var-logs"
        mount_path: "/var/log"
        read_only: true
      },
      {
        name: "var-lib-docker-containers"
        mount_path: "/var/lib/docker/containers"
        read_only: true
      }
    ]
  }
  
  configmap: {
    name: "log-collector-config"
    data: {
      "filebeat.yml": "filebeat configuration content"
    }
  }
  
  service: {
    name: "log-collector"
    type: "ClusterIP"
    ports: [
      { port: 5044, target_port: 5044, protocol: "TCP" }
    ]
  }
  
  ingress: {
    enabled: false
    annotations: {}
  }
  
  monitoring: {
    service_monitor: {
      enabled: true
      interval: "30s"
      path: "/metrics"
    }
    prometheus_rule: {
      enabled: true
      rules: [
        {
          name: "LogCollectionDown"
          expr: "up{job=\"log-collector\"} == 0"
          for: "1m"
          labels: { severity: critical }
        }
      ]
    }
  }
}
```

## 工程实践示例

### 微服务日志收集

```dsl
microservice_collection "order_service_collection" {
  description: "订单服务日志收集"
  
  services: [
    {
      name: "order-service"
      namespace: "order-system"
      replicas: 3
      logs: {
        sources: [
          {
            name: "application_logs"
            type: "file"
            path: "/var/log/order-service/app.log"
            format: "json"
          },
          {
            name: "access_logs"
            type: "file"
            path: "/var/log/order-service/access.log"
            format: "nginx"
          }
        ]
        labels: {
          service: "order-service"
          component: "order-management"
          environment: "production"
        }
      }
    },
    {
      name: "payment-service"
      namespace: "payment-system"
      replicas: 2
      logs: {
        sources: [
          {
            name: "application_logs"
            type: "file"
            path: "/var/log/payment-service/app.log"
            format: "json"
          }
        ]
        labels: {
          service: "payment-service"
          component: "payment-processing"
          environment: "production"
        }
      }
    },
    {
      name: "inventory-service"
      namespace: "inventory-system"
      replicas: 2
      logs: {
        sources: [
          {
            name: "application_logs"
            type: "file"
            path: "/var/log/inventory-service/app.log"
            format: "json"
          }
        ]
        labels: {
          service: "inventory-service"
          component: "inventory-management"
          environment: "production"
        }
      }
    }
  ]
  
  collection_strategy: {
    mode: "sidecar"
    agent: "filebeat"
    version: "7.17.0"
    resources: {
      requests: { cpu: "50m", memory: "64Mi" }
      limits: { cpu: "200m", memory: "256Mi" }
    }
  }
  
  routing: {
    strategy: "service_based"
    rules: [
      {
        service: "order-service"
        output: "elasticsearch_primary"
        index: "order-service-logs"
      },
      {
        service: "payment-service"
        output: "elasticsearch_primary"
        index: "payment-service-logs"
      },
      {
        service: "inventory-service"
        output: "elasticsearch_primary"
        index: "inventory-service-logs"
      }
    ]
  }
  
  correlation: {
    enabled: true
    correlation_key: "request_id"
    services: ["order-service", "payment-service", "inventory-service"]
    time_window: "5m"
  }
  
  alerting: {
    rules: [
      {
        name: "Service Log Collection Failure"
        condition: "collection_errors > 0"
        severity: "critical"
        notification: "pagerduty"
        escalation: {
          levels: ["immediate", "5m", "15m"]
          actions: ["page_oncall", "notify_manager", "create_incident"]
        }
      }
    ]
  }
}
```

### 1实时流收集

```dsl
stream_collection "real_time_log_streaming" {
  description: "实时日志流收集"
  
  streaming: {
    engine: "kafka_connect"
    mode: "real_time"
    parallelism: 8
  }
  
  sources: [
    {
      name: "application_logs"
      type: "kafka"
      topic: "application-logs"
      consumer_group: "log-collectors"
      auto_offset_reset: "latest"
      max_poll_records: 1000
    },
    {
      name: "system_logs"
      type: "kafka"
      topic: "system-logs"
      consumer_group: "system-collectors"
      auto_offset_reset: "latest"
      max_poll_records: 1000
    },
    {
      name: "audit_logs"
      type: "kafka"
      topic: "audit-logs"
      consumer_group: "audit-collectors"
      auto_offset_reset: "latest"
      max_poll_records: 500
    }
  ]
  
  processing: [
    {
      name: "log_parser"
      type: "stream_processor"
      input: "application_logs"
      output: "parsed_logs"
      operations: [
        {
          type: "parse_json"
          field: "message"
          target: "parsed"
        },
        {
          type: "add_timestamp"
          field: "@timestamp"
          format: "ISO8601"
        },
        {
          type: "filter"
          condition: "level in ['ERROR', 'WARN', 'INFO']"
        },
        {
          type: "enrich"
          with: "service_metadata"
          on: "service_name"
        }
      ]
    },
    {
      name: "log_aggregator"
      type: "stream_processor"
      input: "parsed_logs"
      output: "aggregated_logs"
      operations: [
        {
          type: "window"
          size: "5m"
          slide: "1m"
        },
        {
          type: "group_by"
          fields: ["service", "level", "endpoint"]
        },
        {
          type: "aggregate"
          metrics: [
            { name: "count", function: "count" },
            { name: "error_rate", function: "ratio", numerator: "error_count", denominator: "total_count" },
            { name: "avg_response_time", function: "avg", field: "response_time" }
          ]
        }
      ]
    },
    {
      name: "anomaly_detector"
      type: "stream_processor"
      input: "aggregated_logs"
      output: "anomaly_alerts"
      operations: [
        {
          type: "anomaly_detection"
          algorithm: "z_score"
          field: "error_rate"
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
      name: "elasticsearch_sink"
      type: "elasticsearch"
      topic: "parsed_logs"
      endpoint: "http://elasticsearch:9200"
      index: "stream-logs"
      batch_size: 1000
      flush_interval: "5s"
      retry_policy: {
        max_retries: 3
        backoff: "exponential"
        initial_delay: "1s"
        max_delay: "30s"
      }
    },
    {
      name: "kafka_sink"
      type: "kafka"
      topic: "aggregated_logs"
      endpoint: "kafka:9092"
      acks: "all"
      compression: "snappy"
      batch_size: 1000
      linger_ms: 100
    },
    {
      name: "alert_sink"
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
      "records_consumed",
      "records_produced",
      "processing_latency",
      "error_rate",
      "consumer_lag",
      "memory_usage",
      "cpu_usage"
    ]
    health_checks: [
      "kafka_connectivity",
      "elasticsearch_connectivity",
      "processing_pipeline_health"
    ]
    alerting: {
      on_lag: {
        enabled: true
        threshold: "5m"
        severity: "warning"
      }
      on_error_rate: {
        enabled: true
        threshold: 0.01
        severity: "critical"
      }
      on_latency: {
        enabled: true
        threshold: "1s"
        severity: "warning"
      }
      on_memory_usage: {
        enabled: true
        threshold: 0.9
        severity: "critical"
      }
    }
  }
}
```

这个DSL设计提供了完整的日志收集建模能力，支持多种日志源、收集策略、数据转换、传输协议，并能够与主流日志收集平台无缝集成。
