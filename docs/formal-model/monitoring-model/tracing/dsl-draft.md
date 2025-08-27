# 追踪建模DSL设计

## 设计目标

追踪建模DSL旨在提供声明式语言定义复杂的分布式追踪配置，支持多种追踪策略、采样规则、上下文传播、性能分析，并与主流追踪平台无缝集成。

## 基本语法

### 核心结构

```dsl
tracing_model "web_service_tracing" {
  description: "Web服务分布式追踪"
  version: "1.0.0"
  
  namespace: "web_service"
  labels: {
    service: "web-service"
    environment: "production"
    version: "1.0.0"
  }
  
  sampling: {
    rate: 0.1
    strategy: "probabilistic"
  }
  
  propagation: {
    type: "w3c_tracecontext"
    headers: ["traceparent", "tracestate"]
  }
}
```

### 追踪源配置

```dsl
trace_source "web_service_source" {
  description: "Web服务追踪源"
  
  service: {
    name: "web-service"
    version: "1.0.0"
    environment: "production"
  }
  
  instrumentation: {
    framework: "opentelemetry"
    language: "python"
    version: "1.20.0"
  }
  
  endpoints: [
    {
      name: "user_api"
      path: "/api/users/*"
      method: ["GET", "POST", "PUT", "DELETE"]
      tracing: {
        enabled: true
        span_name: "user_api_request"
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "user.id"
        ]
      }
    },
    {
      name: "order_api"
      path: "/api/orders/*"
      method: ["GET", "POST", "PUT", "DELETE"]
      tracing: {
        enabled: true
        span_name: "order_api_request"
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "order.id"
        ]
      }
    }
  ]
  
  database: {
    enabled: true
    spans: [
      {
        name: "database_query"
        attributes: [
          "db.system",
          "db.name",
          "db.statement",
          "db.operation"
        ]
      }
    ]
  }
  
  messaging: {
    enabled: true
    spans: [
      {
        name: "message_publish"
        attributes: [
          "messaging.system",
          "messaging.destination",
          "messaging.operation"
        ]
      },
      {
        name: "message_consume"
        attributes: [
          "messaging.system",
          "messaging.destination",
          "messaging.operation"
        ]
      }
    ]
  }
}
```

### 采样策略

```dsl
sampling_strategy "adaptive_sampling" {
  description: "自适应采样策略"
  
  type: "adaptive"
  
  rules: [
    {
      name: "error_sampling"
      condition: "http.status_code >= 400"
      rate: 1.0
      priority: 1
    },
    {
      name: "slow_request_sampling"
      condition: "duration > 1s"
      rate: 1.0
      priority: 2
    },
    {
      name: "critical_path_sampling"
      condition: "service.name in ['payment-service', 'order-service']"
      rate: 0.5
      priority: 3
    },
    {
      name: "default_sampling"
      condition: "*"
      rate: 0.1
      priority: 4
    }
  ]
  
  adaptive: {
    enabled: true
    target_rate: 0.1
    adjustment_interval: "5m"
    min_rate: 0.01
    max_rate: 1.0
  }
  
  head_sampling: {
    enabled: true
    rate: 0.1
    max_qps: 1000
  }
  
  tail_sampling: {
    enabled: true
    policies: [
      {
        name: "error_traces"
        condition: "status == ERROR"
        rate: 1.0
      },
      {
        name: "slow_traces"
        condition: "duration > 5s"
        rate: 1.0
      },
      {
        name: "rare_traces"
        condition: "service.name not in common_services"
        rate: 0.5
      }
    ]
  }
}
```

### 上下文传播

```dsl
context_propagation "w3c_propagation" {
  description: "W3C TraceContext传播"
  
  type: "w3c_tracecontext"
  
  headers: [
    {
      name: "traceparent"
      format: "00-{trace_id}-{span_id}-{trace_flags}"
      required: true
    },
    {
      name: "tracestate"
      format: "key=value"
      required: false
    }
  ]
  
  baggage: {
    enabled: true
    max_entries: 20
    max_value_length: 4096
    allowed_keys: [
      "user.id",
      "session.id",
      "request.id",
      "correlation.id"
    ]
  }
  
  correlation: {
    enabled: true
    correlation_id_header: "X-Correlation-ID"
    request_id_header: "X-Request-ID"
    session_id_header: "X-Session-ID"
  }
  
  injection: {
    http_headers: true
    grpc_metadata: true
    messaging_headers: true
    database_queries: false
  }
  
  extraction: {
    http_headers: true
    grpc_metadata: true
    messaging_headers: true
    database_queries: false
  }
}
```

### 追踪存储

```dsl
trace_store "jaeger_store" {
  description: "Jaeger追踪存储"
  
  type: "jaeger"
  version: "1.42.0"
  
  storage: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    index_prefix: "jaeger"
    username: "${ES_USERNAME}"
    password: "${ES_PASSWORD}"
  }
  
  retention: {
    hot_data: "7d"
    warm_data: "30d"
    cold_data: "90d"
    archive_data: "1y"
  }
  
  indexing: {
    enabled: true
    index_span: true
    index_service: true
    index_operation: true
  }
  
  search: {
    max_search_depth: 20
    max_span_count: 10000
    max_trace_duration: "24h"
  }
  
  sampling: {
    default_strategy: {
      type: "probabilistic"
      param: 0.001
    }
    per_operation_strategies: [
      {
        operation: "user_api_request"
        strategy: {
          type: "probabilistic"
          param: 0.1
        }
      },
      {
        operation: "order_api_request"
        strategy: {
          type: "probabilistic"
          param: 0.5
        }
      }
    ]
  }
}
```

## 高级用法

### 分布式追踪

```dsl
distributed_tracing "microservice_tracing" {
  description: "微服务分布式追踪"
  
  services: [
    {
      name: "api-gateway"
      version: "1.0.0"
      tracing: {
        enabled: true
        sampling_rate: 0.1
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "user.id",
          "request.id"
        ]
      }
    },
    {
      name: "user-service"
      version: "1.0.0"
      tracing: {
        enabled: true
        sampling_rate: 0.2
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "user.id",
          "db.operation"
        ]
      }
    },
    {
      name: "order-service"
      version: "1.0.0"
      tracing: {
        enabled: true
        sampling_rate: 0.5
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "order.id",
          "db.operation",
          "payment.status"
        ]
      }
    },
    {
      name: "payment-service"
      version: "1.0.0"
      tracing: {
        enabled: true
        sampling_rate: 1.0
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "payment.id",
          "payment.method",
          "payment.amount"
        ]
      }
    }
  ]
  
  propagation: {
    type: "w3c_tracecontext"
    headers: ["traceparent", "tracestate"]
    baggage: {
      enabled: true
      keys: ["user.id", "request.id", "correlation.id"]
    }
  }
  
  correlation: {
    enabled: true
    correlation_key: "request_id"
    services: ["api-gateway", "user-service", "order-service", "payment-service"]
    time_window: "5m"
  }
  
  analysis: [
    {
      name: "service_dependency_analysis"
      type: "dependency_graph"
      services: ["api-gateway", "user-service", "order-service", "payment-service"]
      metrics: ["latency", "error_rate", "throughput"]
    },
    {
      name: "bottleneck_detection"
      type: "performance_analysis"
      threshold: "p95_latency > 2s"
      services: ["*"]
    },
    {
      name: "error_propagation_analysis"
      type: "error_analysis"
      services: ["*"]
      correlation: true
    }
  ]
}
```

### 性能分析

```dsl
performance_analysis "trace_performance" {
  description: "追踪性能分析"
  
  analysis_types: [
    {
      name: "latency_analysis"
      type: "latency"
      metrics: [
        {
          name: "p50_latency"
          percentile: 0.5
          threshold: "500ms"
        },
        {
          name: "p95_latency"
          percentile: 0.95
          threshold: "2s"
        },
        {
          name: "p99_latency"
          percentile: 0.99
          threshold: "5s"
        }
      ]
    },
    {
      name: "throughput_analysis"
      type: "throughput"
      metrics: [
        {
          name: "requests_per_second"
          threshold: 1000
        },
        {
          name: "concurrent_requests"
          threshold: 100
        }
      ]
    },
    {
      name: "error_analysis"
      type: "error"
      metrics: [
        {
          name: "error_rate"
          threshold: 0.05
        },
        {
          name: "error_count"
          threshold: 10
        }
      ]
    }
  ]
  
  bottleneck_detection: {
    enabled: true
    algorithms: [
      {
        name: "critical_path_analysis"
        type: "critical_path"
        threshold: "path_latency > 80%_of_total"
      },
      {
        name: "hotspot_detection"
        type: "hotspot"
        threshold: "span_latency > 2s"
      },
      {
        name: "resource_contention"
        type: "contention"
        resources: ["cpu", "memory", "database", "network"]
      }
    ]
  }
  
  optimization_suggestions: {
    enabled: true
    suggestions: [
      {
        type: "database_optimization"
        condition: "db_query_latency > 1s"
        suggestions: [
          "Add database indexes",
          "Optimize query statements",
          "Use connection pooling"
        ]
      },
      {
        type: "caching_optimization"
        condition: "cache_miss_rate > 0.5"
        suggestions: [
          "Implement caching strategy",
          "Increase cache size",
          "Optimize cache keys"
        ]
      },
      {
        type: "service_optimization"
        condition: "service_latency > 2s"
        suggestions: [
          "Optimize service logic",
          "Use async processing",
          "Implement circuit breaker"
        ]
      }
    ]
  }
}
```

### 实时追踪

```dsl
real_time_tracing "stream_tracing" {
  description: "实时流追踪"
  
  streaming: {
    engine: "kafka_streams"
    mode: "real_time"
    parallelism: 8
  }
  
  sources: [
    {
      name: "trace_stream"
      type: "kafka"
      topic: "trace-stream"
      consumer_group: "trace-processor"
      auto_offset_reset: "latest"
    }
  ]
  
  processing: [
    {
      name: "trace_enrichment"
      type: "stream_processor"
      input: "trace_stream"
      output: "enriched_traces"
      operations: [
        {
          type: "enrichment"
          fields: [
            "service_metadata",
            "user_context",
            "business_context"
          ]
        },
        {
          type: "normalization"
          fields: [
            "timestamp",
            "duration",
            "status"
          ]
        }
      ]
    },
    {
      name: "anomaly_detection"
      type: "stream_processor"
      input: "enriched_traces"
      output: "anomaly_alerts"
      operations: [
        {
          type: "anomaly_detection"
          algorithm: "z_score"
          fields: ["duration", "error_rate"]
          threshold: 3.0
        },
        {
          type: "pattern_detection"
          patterns: [
            {
              name: "error_cascade"
              pattern: "error_propagation"
              threshold: 5
              window: "5m"
            },
            {
              name: "performance_degradation"
              pattern: "latency_increase"
              threshold: 2
              window: "10m"
            }
          ]
        }
      ]
    },
    {
      name: "service_graph_generation"
      type: "stream_processor"
      input: "enriched_traces"
      output: "service_graph"
      operations: [
        {
          type: "graph_building"
          nodes: ["service", "operation"]
          edges: ["calls", "depends_on"]
          window: "1h"
        },
        {
          type: "metrics_aggregation"
          metrics: [
            "latency",
            "throughput",
            "error_rate"
          ]
        }
      ]
    }
  ]
  
  outputs: [
    {
      name: "trace_store"
      type: "elasticsearch"
      topic: "enriched_traces"
      endpoint: "http://elasticsearch:9200"
      index: "traces"
      batch_size: 1000
      flush_interval: "10s"
    },
    {
      name: "alert_sink"
      type: "kafka"
      topic: "trace-alerts"
      endpoint: "kafka:9092"
      acks: "all"
      compression: "snappy"
    },
    {
      name: "graph_sink"
      type: "graph_db"
      topic: "service_graph"
      endpoint: "http://neo4j:7474"
      batch_size: 100
      flush_interval: "30s"
    }
  ]
  
  performance: {
    latency: {
      p95: "100ms"
      p99: "500ms"
    }
    throughput: {
      traces_per_second: 10000
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
      "trace_processing_latency",
      "trace_throughput",
      "anomaly_detection_accuracy",
      "service_graph_freshness",
      "storage_usage",
      "processing_lag"
    ]
    health_checks: [
      "kafka_connectivity",
      "elasticsearch_connectivity",
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
      on_storage_full: {
        threshold: 0.9
        severity: "critical"
      }
    }
  }
}
```

## 代码生成模板

### OpenTelemetry配置

```yaml
# 生成的OpenTelemetry配置
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024
    send_batch_max_size: 2048
  
  attributes:
    actions:
      - key: db.statement
        action: delete
      - key: credit_card.number
        action: delete
      - key: password
        action: delete
  
  probabilistic_sampler:
    hash_seed: 22
    sampling_percentage: 10
  
  tail_sampling:
    decision_wait: 10s
    num_traces: 50000
    expected_new_traces_per_sec: 10
    policies:
      - name: error-policy
        type: status_code
        status_code:
          status_codes: [ERROR]
        sampling_percentage: 100
      - name: slow-policy
        type: latency
        latency:
          threshold_ms: 5000
        sampling_percentage: 100
      - name: default-policy
        type: probabilistic
        probabilistic:
          sampling_percentage: 10

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  
  otlp/elasticsearch:
    endpoint: elasticsearch:9200
    tls:
      insecure: true
    headers:
      authorization: "Bearer ${ES_TOKEN}"

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, attributes, probabilistic_sampler, tail_sampling]
      exporters: [jaeger, otlp/elasticsearch]
```

### Jaeger配置

```yaml
# 生成的Jaeger配置
apiVersion: apps/v1
kind: Deployment
metadata:
  name: jaeger
  namespace: tracing
spec:
  replicas: 1
  selector:
    matchLabels:
      app: jaeger
  template:
    metadata:
      labels:
        app: jaeger
    spec:
      containers:
      - name: jaeger
        image: jaegertracing/all-in-one:1.42
        ports:
        - containerPort: 16686
          name: ui
        - containerPort: 14268
          name: http
        - containerPort: 14250
          name: grpc
        env:
        - name: COLLECTOR_OTLP_ENABLED
          value: "true"
        - name: STORAGE_TYPE
          value: "elasticsearch"
        - name: ES_SERVER_URLS
          value: "http://elasticsearch:9200"
        - name: ES_USERNAME
          valueFrom:
            secretKeyRef:
              name: elasticsearch-secret
              key: username
        - name: ES_PASSWORD
          valueFrom:
            secretKeyRef:
              name: elasticsearch-secret
              key: password
        - name: ES_INDEX_PREFIX
          value: "jaeger"
        - name: ES_TAGS_AS_FIELDS_ALL
          value: "true"
        resources:
          requests:
            memory: "512Mi"
            cpu: "500m"
          limits:
            memory: "1Gi"
            cpu: "1000m"
---
apiVersion: v1
kind: Service
metadata:
  name: jaeger
  namespace: tracing
spec:
  selector:
    app: jaeger
  ports:
  - port: 16686
    targetPort: 16686
    name: ui
  - port: 14268
    targetPort: 14268
    name: http
  - port: 14250
    targetPort: 14250
    name: grpc
  type: ClusterIP
```

### Python实现

```python
import time
import random
from opentelemetry import trace
from opentelemetry.exporter.jaeger.thrift import JaegerExporter
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.sdk.resources import Resource
from opentelemetry.instrumentation.flask import FlaskInstrumentor
from opentelemetry.instrumentation.requests import RequestsInstrumentor
from flask import Flask, request, jsonify

# 配置OpenTelemetry
def setup_tracing():
    """设置分布式追踪"""
    # 创建TracerProvider
    resource = Resource.create({
        "service.name": "web-service",
        "service.version": "1.0.0",
        "deployment.environment": "production"
    })
    
    provider = TracerProvider(resource=resource)
    
    # 配置Jaeger导出器
    jaeger_exporter = JaegerExporter(
        agent_host_name="jaeger",
        agent_port=6831,
    )
    
    # 添加BatchSpanProcessor
    processor = BatchSpanProcessor(jaeger_exporter)
    provider.add_span_processor(processor)
    
    # 设置全局TracerProvider
    trace.set_tracer_provider(provider)
    
    return trace.get_tracer(__name__)

# 创建Flask应用
app = Flask(__name__)
tracer = setup_tracing()

# 自动检测Flask和Requests
FlaskInstrumentor().instrument_app(app)
RequestsInstrumentor().instrument()

@app.route('/api/users/<user_id>')
def get_user(user_id):
    """获取用户信息"""
    with tracer.start_as_current_span("get_user") as span:
        # 添加属性
        span.set_attribute("user.id", user_id)
        span.set_attribute("http.method", request.method)
        span.set_attribute("http.url", request.url)
        
        try:
            # 模拟数据库查询
            with tracer.start_as_current_span("database_query") as db_span:
                db_span.set_attribute("db.system", "mysql")
                db_span.set_attribute("db.operation", "SELECT")
                db_span.set_attribute("db.statement", "SELECT * FROM users WHERE id = ?")
                
                # 模拟查询延迟
                time.sleep(random.uniform(0.1, 0.5))
                
                # 模拟偶尔的数据库错误
                if random.random() < 0.1:
                    raise Exception("Database connection failed")
                
                user_data = {
                    "id": user_id,
                    "name": f"User {user_id}",
                    "email": f"user{user_id}@example.com"
                }
            
            # 模拟外部API调用
            with tracer.start_as_current_span("external_api_call") as api_span:
                api_span.set_attribute("http.method", "GET")
                api_span.set_attribute("http.url", "https://api.external.com/user-profile")
                
                # 模拟API调用延迟
                time.sleep(random.uniform(0.2, 1.0))
                
                # 模拟偶尔的API错误
                if random.random() < 0.05:
                    raise Exception("External API timeout")
                
                profile_data = {
                    "profile": "Premium",
                    "preferences": {"theme": "dark"}
                }
            
            # 合并数据
            result = {**user_data, **profile_data}
            
            # 设置响应状态
            span.set_attribute("http.status_code", 200)
            
            return jsonify(result)
            
        except Exception as e:
            # 记录错误
            span.record_exception(e)
            span.set_attribute("http.status_code", 500)
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            
            return jsonify({"error": str(e)}), 500

@app.route('/api/orders/<order_id>')
def get_order(order_id):
    """获取订单信息"""
    with tracer.start_as_current_span("get_order") as span:
        span.set_attribute("order.id", order_id)
        span.set_attribute("http.method", request.method)
        span.set_attribute("http.url", request.url)
        
        try:
            # 模拟订单处理
            with tracer.start_as_current_span("order_processing") as order_span:
                order_span.set_attribute("order.status", "processing")
                
                # 模拟处理延迟
                time.sleep(random.uniform(0.5, 2.0))
                
                order_data = {
                    "id": order_id,
                    "status": "completed",
                    "total": random.uniform(10.0, 1000.0)
                }
            
            span.set_attribute("http.status_code", 200)
            return jsonify(order_data)
            
        except Exception as e:
            span.record_exception(e)
            span.set_attribute("http.status_code", 500)
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            
            return jsonify({"error": str(e)}), 500

@app.route('/health')
def health():
    """健康检查"""
    return jsonify({"status": "healthy"})

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=8080, debug=False)
```

## 验证规则

### 语法验证

```dsl
validation_rules "tracing_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "version", "namespace"]
      message: "必须包含描述、版本和命名空间"
    },
    {
      rule: "valid_sampling_rate"
      condition: "sampling_rate >= 0 AND sampling_rate <= 1"
      message: "采样率必须在0到1之间"
    },
    {
      rule: "valid_propagation_type"
      allowed_types: ["w3c_tracecontext", "b3", "jaeger"]
      message: "传播类型必须是支持的类型"
    }
  ]
  
  semantic: [
    {
      rule: "service_uniqueness"
      condition: "service names are unique within namespace"
      message: "服务名称在命名空间内必须唯一"
    },
    {
      rule: "sampling_consistency"
      condition: "sampling rates are consistent across services"
      message: "采样率在服务间必须一致"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "tracing_performance" {
  constraints: [
    {
      metric: "trace_generation_overhead"
      threshold: "1ms"
      action: "warn"
    },
    {
      metric: "storage_usage"
      threshold: "10GB"
      action: "error"
    },
    {
      metric: "query_latency"
      threshold: "5s"
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "sampling_optimization"
      enabled: true
      target_rate: 0.1
    },
    {
      strategy: "storage_optimization"
      enabled: true
      compression: "gzip"
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "tracing_patterns" {
  patterns: [
    {
      name: "distributed_context_propagation"
      description: "分布式上下文传播模式"
      implementation: {
        strategy: "w3c_tracecontext"
        headers: ["traceparent", "tracestate"]
        baggage: "enabled"
      }
    },
    {
      name: "adaptive_sampling"
      description: "自适应采样模式"
      implementation: {
        strategy: "performance_based"
        metrics: ["latency", "error_rate"]
        adjustment: "automatic"
      }
    },
    {
      name: "correlation_tracking"
      description: "关联追踪模式"
      implementation: {
        strategy: "business_correlation"
        keys: ["user_id", "order_id", "request_id"]
        time_window: "5m"
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "over_tracing"
      description: "过度追踪"
      symptoms: ["high_overhead", "storage_explosion"]
      solution: "optimize_sampling"
    },
    {
      name: "under_tracing"
      description: "追踪不足"
      symptoms: ["poor_visibility", "difficult_debugging"]
      solution: "increase_coverage"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "tracing_monitoring" {
  metrics: [
    {
      name: "trace_generation_rate"
      type: "counter"
      labels: ["service", "operation"]
      unit: "traces/sec"
    },
    {
      name: "trace_storage_usage"
      type: "gauge"
      labels: ["service"]
      unit: "bytes"
    },
    {
      name: "trace_query_latency"
      type: "histogram"
      labels: ["query_type"]
      buckets: [0.1, 0.5, 1, 5, 10, 30]
    }
  ]
  
  alerts: [
    {
      name: "trace_generation_failure"
      condition: "trace_generation_errors > 0"
      severity: "critical"
      action: "restart_tracer"
    },
    {
      name: "high_storage_usage"
      condition: "trace_storage_usage > 10GB"
      severity: "warning"
      action: "cleanup_old_traces"
    }
  ]
}
```

## 主流标准映射

### OpenTelemetry集成

```dsl
opentelemetry_integration "otel_tracing" {
  metrics: [
    {
      name: "trace_generation_duration_seconds"
      type: "histogram"
      help: "Trace generation execution time"
      labels: ["service", "operation"]
    },
    {
      name: "trace_export_duration_seconds"
      type: "histogram"
      help: "Trace export execution time"
      labels: ["exporter", "status"]
    },
    {
      name: "trace_sampling_rate"
      type: "gauge"
      help: "Current trace sampling rate"
      labels: ["service"]
    }
  ]
  
  rules: [
    {
      name: "High Trace Generation Overhead"
      expr: "histogram_quantile(0.95, rate(trace_generation_duration_seconds_bucket[5m])) > 0.001"
      for: "2m"
      labels: { severity: warning }
      annotations: { summary: "High trace generation overhead" }
    },
    {
      name: "Trace Export Failure"
      expr: "rate(trace_export_failures_total[5m]) > 0"
      for: "1m"
      labels: { severity: critical }
      annotations: { summary: "Trace export is failing" }
    }
  ]
  
  alertmanager: {
    receivers: [
      {
        name: "slack"
        slack_configs: [
          {
            channel: "#alerts"
            title: "Tracing Alert"
            text: "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}"
          }
        ]
      }
    ]
  }
}
```

## 工程实践示例

### 微服务追踪

```dsl
microservice_tracing "order_service_tracing" {
  description: "订单服务追踪"
  
  namespace: "order_service"
  
  services: [
    {
      name: "api-gateway"
      version: "1.0.0"
      tracing: {
        enabled: true
        sampling_rate: 0.1
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "user.id",
          "request.id"
        ]
      }
    },
    {
      name: "user-service"
      version: "1.0.0"
      tracing: {
        enabled: true
        sampling_rate: 0.2
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "user.id",
          "db.operation"
        ]
      }
    },
    {
      name: "order-service"
      version: "1.0.0"
      tracing: {
        enabled: true
        sampling_rate: 0.5
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "order.id",
          "db.operation",
          "payment.status"
        ]
      }
    },
    {
      name: "payment-service"
      version: "1.0.0"
      tracing: {
        enabled: true
        sampling_rate: 1.0
        attributes: [
          "http.method",
          "http.url",
          "http.status_code",
          "payment.id",
          "payment.method",
          "payment.amount"
        ]
      }
    }
  ]
  
  propagation: {
    type: "w3c_tracecontext"
    headers: ["traceparent", "tracestate"]
    baggage: {
      enabled: true
      keys: ["user.id", "request.id", "correlation.id"]
    }
  }
  
  correlation: {
    enabled: true
    correlation_key: "request_id"
    services: ["api-gateway", "user-service", "order-service", "payment-service"]
    time_window: "5m"
  }
  
  analysis: [
    {
      name: "service_dependency_analysis"
      type: "dependency_graph"
      services: ["api-gateway", "user-service", "order-service", "payment-service"]
      metrics: ["latency", "error_rate", "throughput"]
    },
    {
      name: "bottleneck_detection"
      type: "performance_analysis"
      threshold: "p95_latency > 2s"
      services: ["*"]
    },
    {
      name: "error_propagation_analysis"
      type: "error_analysis"
      services: ["*"]
      correlation: true
    }
  ]
  
  storage: {
    type: "jaeger"
    endpoint: "http://jaeger:16686"
    retention: {
      hot_data: "7d"
      warm_data: "30d"
      cold_data: "90d"
    }
  }
  
  monitoring: {
    metrics: [
      "trace_generation_rate",
      "trace_storage_usage",
      "service_dependency_freshness",
      "correlation_success_rate"
    ]
    alerting: {
      on_trace_generation_failure: {
        threshold: 0.01
        severity: "critical"
        notification: "pagerduty"
      }
      on_high_storage_usage: {
        threshold: 0.9
        severity: "warning"
        notification: "slack"
      }
    }
  }
}
```

### 实时流追踪

```dsl
stream_tracing "real_time_trace_analysis" {
  description: "实时流追踪分析"
  
  streaming: {
    engine: "kafka_streams"
    mode: "real_time"
    parallelism: 8
  }
  
  sources: [
    {
      name: "trace_stream"
      type: "kafka"
      topic: "trace-stream"
      consumer_group: "trace-analyzer"
      auto_offset_reset: "latest"
    }
  ]
  
  processing: [
    {
      name: "trace_enrichment"
      type: "stream_processor"
      input: "trace_stream"
      output: "enriched_traces"
      operations: [
        {
          type: "enrichment"
          fields: [
            "service_metadata",
            "user_context",
            "business_context"
          ]
        },
        {
          type: "normalization"
          fields: [
            "timestamp",
            "duration",
            "status"
          ]
        }
      ]
    },
    {
      name: "anomaly_detection"
      type: "stream_processor"
      input: "enriched_traces"
      output: "anomaly_alerts"
      operations: [
        {
          type: "anomaly_detection"
          algorithm: "z_score"
          fields: ["duration", "error_rate"]
          threshold: 3.0
        },
        {
          type: "pattern_detection"
          patterns: [
            {
              name: "error_cascade"
              pattern: "error_propagation"
              threshold: 5
              window: "5m"
            },
            {
              name: "performance_degradation"
              pattern: "latency_increase"
              threshold: 2
              window: "10m"
            }
          ]
        }
      ]
    },
    {
      name: "service_graph_generation"
      type: "stream_processor"
      input: "enriched_traces"
      output: "service_graph"
      operations: [
        {
          type: "graph_building"
          nodes: ["service", "operation"]
          edges: ["calls", "depends_on"]
          window: "1h"
        },
        {
          type: "metrics_aggregation"
          metrics: [
            "latency",
            "throughput",
            "error_rate"
          ]
        }
      ]
    }
  ]
  
  outputs: [
    {
      name: "trace_store"
      type: "elasticsearch"
      topic: "enriched_traces"
      endpoint: "http://elasticsearch:9200"
      index: "traces"
      batch_size: 1000
      flush_interval: "10s"
    },
    {
      name: "alert_sink"
      type: "kafka"
      topic: "trace-alerts"
      endpoint: "kafka:9092"
      acks: "all"
      compression: "snappy"
    },
    {
      name: "graph_sink"
      type: "graph_db"
      topic: "service_graph"
      endpoint: "http://neo4j:7474"
      batch_size: 100
      flush_interval: "30s"
    }
  ]
  
  performance: {
    latency: {
      p95: "100ms"
      p99: "500ms"
    }
    throughput: {
      traces_per_second: 10000
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
      "trace_processing_latency",
      "trace_throughput",
      "anomaly_detection_accuracy",
      "service_graph_freshness",
      "storage_usage",
      "processing_lag"
    ]
    health_checks: [
      "kafka_connectivity",
      "elasticsearch_connectivity",
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
      on_storage_full: {
        threshold: 0.9
        severity: "critical"
      }
    }
  }
}
```

这个DSL设计提供了完整的追踪建模能力，支持多种追踪策略、采样规则、上下文传播、性能分析，并能够与主流追踪平台无缝集成。
