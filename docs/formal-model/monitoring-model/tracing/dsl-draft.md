# 追踪建模DSL草案

## 1. 设计目标

- 用统一DSL描述分布式追踪、链路追踪、性能分析等追踪要素
- 支持自动生成Jaeger、Zipkin、OpenTelemetry等主流追踪配置
- 支持追踪采样、过滤、聚合、分析等高级特性

## 2. 基本语法结构

```dsl
trace "web_request_trace" {
  description: "Web请求追踪"
  version: "1.0.0"
  author: "system"
  
  service: "web-service"
  operation: "handle_request"
  
  sampling: {
    type: "probabilistic"
    rate: 0.1
    max_traces_per_second: 100
  }
  
  propagation: {
    type: "w3c"
    headers: [
      "traceparent",
      "tracestate"
    ]
  }
  
  spans: [
    {
      name: "http_request"
      type: "http"
      attributes: {
        method: "GET"
        url: "/api/users"
        status_code: 200
      }
    },
    {
      name: "database_query"
      type: "database"
      attributes: {
        db_system: "postgresql"
        db_statement: "SELECT * FROM users"
        db_operation: "SELECT"
      }
    },
    {
      name: "cache_lookup"
      type: "cache"
      attributes: {
        cache_system: "redis"
        cache_operation: "GET"
        cache_key: "user:123"
      }
    }
  ]
  
  attributes: {
    environment: "production"
    version: "1.0.0"
    team: "frontend"
  }
  
  error_handling: {
    enabled: true
    capture_exceptions: true
    log_errors: true
  }
  
  performance: {
    enabled: true
    metrics: [
      "duration",
      "throughput",
      "error_rate"
    ]
    thresholds: {
      slow_query: "1s"
      error_threshold: 0.05
    }
  }
}
```

## 3. 关键元素

- trace：追踪声明
- description：描述信息
- version：版本号
- author：作者
- service：服务名称
- operation：操作名称
- sampling：采样配置
- propagation：传播配置
- spans：跨度定义
- attributes：属性配置
- error_handling：错误处理
- performance：性能配置

## 4. 高级用法

### 4.1 分布式追踪

```dsl
trace "distributed_order_processing" {
  description: "分布式订单处理追踪"
  version: "1.0.0"
  author: "system"
  
  service: "order-service"
  operation: "process_order"
  
  sampling: {
    type: "adaptive"
    rate: 0.2
    max_traces_per_second: 200
    adaptive_config: {
      target_traces_per_second: 100
      adjustment_interval: "1m"
    }
  }
  
  propagation: {
    type: "b3"
    headers: [
      "X-B3-TraceId",
      "X-B3-SpanId",
      "X-B3-ParentSpanId",
      "X-B3-Sampled"
    ]
  }
  
  spans: [
    {
      name: "order_validation"
      type: "business_logic"
      attributes: {
        order_id: "{{ order_id }}"
        validation_rules: ["stock_check", "payment_validation"]
      }
      children: [
        {
          name: "stock_check"
          type: "database"
          attributes: {
            db_system: "postgresql"
            db_operation: "SELECT"
            table: "inventory"
          }
        },
        {
          name: "payment_validation"
          type: "http"
          attributes: {
            method: "POST"
            url: "/api/payments/validate"
            service: "payment-service"
          }
        }
      ]
    },
    {
      name: "order_creation"
      type: "database"
      attributes: {
        db_system: "postgresql"
        db_operation: "INSERT"
        table: "orders"
      }
    },
    {
      name: "notification_send"
      type: "messaging"
      attributes: {
        messaging_system: "kafka"
        topic: "order.created"
        message_type: "event"
      }
    }
  ]
  
  attributes: {
    environment: "production"
    version: "1.0.0"
    team: "backend"
    business_domain: "ecommerce"
  }
  
  error_handling: {
    enabled: true
    capture_exceptions: true
    log_errors: true
    error_attributes: [
      "error_type",
      "error_message",
      "stack_trace"
    ]
  }
  
  performance: {
    enabled: true
    metrics: [
      "duration",
      "throughput",
      "error_rate",
      "latency_p95",
      "latency_p99"
    ]
    thresholds: {
      slow_operation: "2s"
      error_threshold: 0.02
      high_latency_p95: "1s"
    }
    alerts: [
      {
        name: "high_latency"
        condition: "latency_p95 > 1s"
        duration: "5m"
      },
      {
        name: "high_error_rate"
        condition: "error_rate > 0.02"
        duration: "5m"
      }
    ]
  }
  
  correlation: {
    enabled: true
    correlation_ids: [
      "order_id",
      "user_id",
      "session_id"
    ]
    baggage: [
      "user_type",
      "region",
      "device_type"
    ]
  }
}
```

### 4.2 链路追踪

```dsl
trace "api_gateway_trace" {
  description: "API网关链路追踪"
  version: "1.0.0"
  author: "system"
  
  service: "api-gateway"
  operation: "route_request"
  
  sampling: {
    type: "rate_limiting"
    rate: 0.3
    max_traces_per_second: 500
  }
  
  propagation: {
    type: "jaeger"
    headers: [
      "uber-trace-id"
    ]
  }
  
  spans: [
    {
      name: "request_received"
      type: "http"
      attributes: {
        method: "{{ request.method }}"
        url: "{{ request.url }}"
        user_agent: "{{ request.user_agent }}"
        client_ip: "{{ request.client_ip }}"
      }
    },
    {
      name: "authentication"
      type: "auth"
      attributes: {
        auth_type: "jwt"
        user_id: "{{ user.id }}"
        permissions: "{{ user.permissions }}"
      }
    },
    {
      name: "rate_limiting"
      type: "rate_limit"
      attributes: {
        limit: "{{ rate_limit.limit }}"
        remaining: "{{ rate_limit.remaining }}"
        reset_time: "{{ rate_limit.reset_time }}"
      }
    },
    {
      name: "service_routing"
      type: "routing"
      attributes: {
        target_service: "{{ route.target_service }}"
        route_path: "{{ route.path }}"
        load_balancer: "{{ route.load_balancer }}"
      }
    },
    {
      name: "response_sent"
      type: "http"
      attributes: {
        status_code: "{{ response.status_code }}"
        content_length: "{{ response.content_length }}"
        response_time: "{{ response.time }}"
      }
    }
  ]
  
  attributes: {
    environment: "production"
    version: "1.0.0"
    team: "platform"
    component: "gateway"
  }
  
  error_handling: {
    enabled: true
    capture_exceptions: true
    log_errors: true
    error_attributes: [
      "error_type",
      "error_message",
      "http_status_code"
    ]
  }
  
  performance: {
    enabled: true
    metrics: [
      "request_duration",
      "requests_per_second",
      "error_rate",
      "upstream_latency"
    ]
    thresholds: {
      slow_request: "500ms"
      error_threshold: 0.01
      upstream_timeout: "10s"
    }
  }
  
  security: {
    enabled: true
    sensitive_attributes: [
      "password",
      "token",
      "credit_card"
    ]
    redaction_rules: [
      {
        pattern: "password=.*"
        replacement: "password=***"
      },
      {
        pattern: "token=.*"
        replacement: "token=***"
      }
    ]
  }
}
```

## 5. 代码生成模板

### 5.1 OpenTelemetry生成

```python
# tracing_config.py
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.jaeger.thrift import JaegerExporter
from opentelemetry.instrumentation.flask import FlaskInstrumentor
from opentelemetry.instrumentation.requests import RequestsInstrumentor
from opentelemetry.instrumentation.sqlalchemy import SQLAlchemyInstrumentor

def setup_tracing():
    # 设置追踪提供者
    trace.set_tracer_provider(TracerProvider())
    
    # 配置Jaeger导出器
    jaeger_exporter = JaegerExporter(
        agent_host_name="localhost",
        agent_port=6831,
    )
    
    # 设置批处理处理器
    span_processor = BatchSpanProcessor(jaeger_exporter)
    trace.get_tracer_provider().add_span_processor(span_processor)
    
    # 获取追踪器
    tracer = trace.get_tracer(__name__)
    
    return tracer

# 使用示例
tracer = setup_tracing()

def process_order(order_id: str):
    with tracer.start_as_current_span("process_order") as span:
        span.set_attribute("order_id", order_id)
        span.set_attribute("service", "order-service")
        span.set_attribute("operation", "process_order")
        
        # 验证订单
        with tracer.start_as_current_span("order_validation") as validation_span:
            validation_span.set_attribute("validation_type", "business_logic")
            # 验证逻辑...
            
            # 库存检查
            with tracer.start_as_current_span("stock_check") as stock_span:
                stock_span.set_attribute("db_system", "postgresql")
                stock_span.set_attribute("db_operation", "SELECT")
                stock_span.set_attribute("table", "inventory")
                # 库存检查逻辑...
                
            # 支付验证
            with tracer.start_as_current_span("payment_validation") as payment_span:
                payment_span.set_attribute("method", "POST")
                payment_span.set_attribute("url", "/api/payments/validate")
                payment_span.set_attribute("service", "payment-service")
                # 支付验证逻辑...
        
        # 创建订单
        with tracer.start_as_current_span("order_creation") as creation_span:
            creation_span.set_attribute("db_system", "postgresql")
            creation_span.set_attribute("db_operation", "INSERT")
            creation_span.set_attribute("table", "orders")
            # 订单创建逻辑...
        
        # 发送通知
        with tracer.start_as_current_span("notification_send") as notification_span:
            notification_span.set_attribute("messaging_system", "kafka")
            notification_span.set_attribute("topic", "order.created")
            notification_span.set_attribute("message_type", "event")
            # 通知发送逻辑...
```

### 5.2 Jaeger配置生成

```yaml
# jaeger-config.yaml
apiVersion: jaegertracing.io/v1
kind: Jaeger
metadata:
  name: jaeger
  namespace: monitoring
spec:
  strategy: production
  storage:
    type: elasticsearch
    options:
      es:
        server-urls: http://elasticsearch:9200
        index-prefix: jaeger
  ingress:
    enabled: true
    hosts:
      - jaeger.example.com
    tls:
      - secretName: jaeger-tls
  agent:
    strategy: DaemonSet
    options:
      log-level: info
  collector:
    options:
      log-level: info
      sampling:
        default_strategy:
          type: probabilistic
          param: 0.1
        default_sampling_probability: 0.1
        default_lower_bound_traces_per_second: 0.1
  query:
    options:
      log-level: info
      query:
        base-path: /jaeger
```

### 5.3 Zipkin配置生成

```yaml
# zipkin-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: zipkin-config
  namespace: monitoring
data:
  zipkin.yml: |
    server:
      port: 9411
      admin:
        port: 9900
    
    storage:
      type: elasticsearch
      elasticsearch:
        hosts: http://elasticsearch:9200
        index: zipkin
        index-shards: 5
        index-replicas: 1
    
    sampling:
      probability: 0.1
    
    query:
      lookback: 86400000  # 1 day in milliseconds
      default-lookback: 900000  # 15 minutes in milliseconds
      max-queries: 10
    
    collector:
      sample-rate: 0.1
      http:
        enabled: true
        port: 9411
      kafka:
        enabled: false
      scribe:
        enabled: false

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: zipkin
  namespace: monitoring
spec:
  replicas: 1
  selector:
    matchLabels:
      app: zipkin
  template:
    metadata:
      labels:
        app: zipkin
    spec:
      containers:
        - name: zipkin
          image: openzipkin/zipkin:latest
          ports:
            - containerPort: 9411
          volumeMounts:
            - name: config
              mountPath: /config
          args:
            - -f
            - /config/zipkin.yml
      volumes:
        - name: config
          configMap:
            name: zipkin-config
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - trace.name
    - trace.description
    - trace.version
    - trace.service
    - trace.operation
  
  type_constraints:
    - field: "trace.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "trace.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "trace.sampling.type"
      type: "string"
      enum: ["probabilistic", "adaptive", "rate_limiting"]
```

### 6.2 追踪验证规则

```yaml
trace_validation:
  span_consistency:
    - rule: "all spans must have valid names"
    - rule: "span types must be valid"
    - rule: "span attributes must be properly formatted"
  
  sampling_validation:
    - rule: "sampling rate must be between 0 and 1"
    - rule: "max traces per second must be positive"
    - rule: "adaptive config must be valid if enabled"
```

## 7. 最佳实践

### 7.1 追踪设计模式

```dsl
# 基础追踪模式
trace "basic_trace" {
  description: "基础追踪"
  version: "1.0.0"
  
  service: "service-name"
  operation: "operation-name"
  
  sampling: {
    type: "probabilistic"
    rate: 0.1
  }
  
  spans: [
    {
      name: "operation"
      type: "http"
      attributes: {
        method: "GET"
        url: "/api/endpoint"
      }
    }
  ]
}

# 分布式追踪模式
trace "distributed_trace" {
  description: "分布式追踪"
  version: "1.0.0"
  
  service: "service-name"
  operation: "distributed_operation"
  
  sampling: {
    type: "adaptive"
    rate: 0.2
  }
  
  propagation: {
    type: "w3c"
    headers: ["traceparent", "tracestate"]
  }
  
  spans: [
    {
      name: "parent_operation"
      type: "business_logic"
      children: [
        {
          name: "child_operation"
          type: "database"
        }
      ]
    }
  ]
}
```

### 7.2 追踪命名规范

```dsl
# 推荐命名模式
trace "service_operation_trace" {
  # 服务_操作_追踪
}

trace "domain_workflow_trace" {
  # 领域_工作流_追踪
}

trace "component_function_trace" {
  # 组件_功能_追踪
}
```

## 8. 与主流标准的映射

| DSL元素 | OpenTelemetry | Jaeger | Zipkin | AWS X-Ray |
|---------|---------------|--------|--------|-----------|
| trace | trace | trace | trace | trace |
| span | span | span | span | segment |
| sampling | sampling | sampling | sampling | sampling |
| propagation | propagation | propagation | propagation | propagation |
| attributes | attributes | tags | tags | annotations |

## 9. 工程实践示例

```dsl
# 生产环境追踪配置示例
trace "production_api_trace" {
  description: "生产环境API追踪"
  version: "1.0.0"
  author: "system"
  
  service: "api-service"
  operation: "handle_api_request"
  
  sampling: {
    type: "adaptive"
    rate: 0.15
    max_traces_per_second: 1000
    adaptive_config: {
      target_traces_per_second: 500
      adjustment_interval: "2m"
      min_rate: 0.01
      max_rate: 0.5
    }
  }
  
  propagation: {
    type: "w3c"
    headers: [
      "traceparent",
      "tracestate"
    ]
    baggage: [
      "user_id",
      "session_id",
      "request_id"
    ]
  }
  
  spans: [
    {
      name: "request_received"
      type: "http"
      attributes: {
        method: "{{ request.method }}"
        url: "{{ request.url }}"
        user_agent: "{{ request.user_agent }}"
        client_ip: "{{ request.client_ip }}"
        content_length: "{{ request.content_length }}"
      }
    },
    {
      name: "authentication"
      type: "auth"
      attributes: {
        auth_type: "jwt"
        user_id: "{{ user.id }}"
        permissions: "{{ user.permissions }}"
        token_expiry: "{{ token.expiry }}"
      }
    },
    {
      name: "rate_limiting"
      type: "rate_limit"
      attributes: {
        limit: "{{ rate_limit.limit }}"
        remaining: "{{ rate_limit.remaining }}"
        reset_time: "{{ rate_limit.reset_time }}"
        window_size: "{{ rate_limit.window_size }}"
      }
    },
    {
      name: "request_validation"
      type: "validation"
      attributes: {
        validation_rules: "{{ validation.rules }}"
        validation_result: "{{ validation.result }}"
        validation_errors: "{{ validation.errors }}"
      }
    },
    {
      name: "business_logic"
      type: "business_logic"
      attributes: {
        business_operation: "{{ business.operation }}"
        business_rules: "{{ business.rules }}"
        business_result: "{{ business.result }}"
      }
      children: [
        {
          name: "database_operation"
          type: "database"
          attributes: {
            db_system: "{{ database.system }}"
            db_operation: "{{ database.operation }}"
            db_statement: "{{ database.statement }}"
            db_table: "{{ database.table }}"
            db_rows_affected: "{{ database.rows_affected }}"
          }
        },
        {
          name: "cache_operation"
          type: "cache"
          attributes: {
            cache_system: "{{ cache.system }}"
            cache_operation: "{{ cache.operation }}"
            cache_key: "{{ cache.key }}"
            cache_hit: "{{ cache.hit }}"
          }
        },
        {
          name: "external_api_call"
          type: "http"
          attributes: {
            method: "{{ external.method }}"
            url: "{{ external.url }}"
            service: "{{ external.service }}"
            status_code: "{{ external.status_code }}"
            response_time: "{{ external.response_time }}"
          }
        }
      ]
    },
    {
      name: "response_preparation"
      type: "response"
      attributes: {
        status_code: "{{ response.status_code }}"
        content_type: "{{ response.content_type }}"
        content_length: "{{ response.content_length }}"
        response_time: "{{ response.time }}"
      }
    },
    {
      name: "response_sent"
      type: "http"
      attributes: {
        status_code: "{{ response.status_code }}"
        content_length: "{{ response.content_length }}"
        response_time: "{{ response.time }}"
        client_ip: "{{ request.client_ip }}"
      }
    }
  ]
  
  attributes: {
    environment: "production"
    version: "1.0.0"
    team: "backend"
    component: "api"
    datacenter: "us-east-1"
    region: "us-east-1"
  }
  
  error_handling: {
    enabled: true
    capture_exceptions: true
    log_errors: true
    error_attributes: [
      "error_type",
      "error_message",
      "stack_trace",
      "error_code",
      "http_status_code"
    ]
    error_sampling: {
      enabled: true
      rate: 1.0  # 总是采样错误
    }
  }
  
  performance: {
    enabled: true
    metrics: [
      "duration",
      "throughput",
      "error_rate",
      "latency_p50",
      "latency_p95",
      "latency_p99",
      "upstream_latency"
    ]
    thresholds: {
      slow_request: "500ms"
      error_threshold: 0.01
      upstream_timeout: "10s"
      high_latency_p95: "1s"
      high_latency_p99: "2s"
    }
    alerts: [
      {
        name: "high_latency"
        condition: "latency_p95 > 1s"
        duration: "5m"
        severity: "warning"
      },
      {
        name: "high_error_rate"
        condition: "error_rate > 0.01"
        duration: "5m"
        severity: "critical"
      },
      {
        name: "upstream_timeout"
        condition: "upstream_latency > 10s"
        duration: "2m"
        severity: "critical"
      }
    ]
  }
  
  correlation: {
    enabled: true
    correlation_ids: [
      "request_id",
      "user_id",
      "session_id",
      "transaction_id"
    ]
    baggage: [
      "user_type",
      "region",
      "device_type",
      "api_version"
    ]
    distributed_context: {
      enabled: true
      propagation: "w3c"
      injection: ["http", "grpc", "kafka"]
      extraction: ["http", "grpc", "kafka"]
    }
  }
  
  security: {
    enabled: true
    sensitive_attributes: [
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
  }
  
  storage: {
    type: "elasticsearch"
    retention: "30d"
    index_pattern: "traces-*"
    shards: 5
    replicas: 1
    compression: true
  }
  
  analysis: {
    enabled: true
    anomaly_detection: {
      enabled: true
      algorithms: ["isolation_forest", "dbscan"]
      features: ["duration", "error_rate", "throughput"]
      training_window: "7d"
      update_frequency: "1h"
    }
    performance_analysis: {
      enabled: true
      slow_query_analysis: true
      bottleneck_detection: true
      dependency_analysis: true
    }
    business_metrics: {
      enabled: true
      metrics: [
        "user_journey_completion",
        "conversion_rate",
        "abandonment_rate"
      ]
    }
  }
}
```

这个DSL设计为追踪建模提供了完整的配置语言，支持基础追踪、分布式追踪、链路追踪等多种模式，同时保持了良好的可扩展性和可维护性。
