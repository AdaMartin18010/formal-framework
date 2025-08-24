# 消息建模DSL草案

## 1. 设计目标

- 用统一DSL描述请求/响应、事件、流等消息要素
- 支持自动生成Kafka、RabbitMQ、MQTT、CloudEvents等主流消息配置与代码
- 支持消息过滤、分区、优先级、追踪、监控等高级特性

## 2. 基本语法结构

```dsl
message "order_created_event" {
  description: "订单创建事件"
  version: "1.0.0"
  author: "system"
  
  type: "event"
  format: "json"
  priority: "normal"
  
  schema: {
    type: "object"
    required: ["order_id", "user_id", "amount", "timestamp"]
    properties: {
      order_id: { type: "string", format: "uuid" }
      user_id: { type: "string", format: "uuid" }
      amount: { type: "number", minimum: 0 }
      currency: { type: "string", default: "USD" }
      items: {
        type: "array"
        items: {
          type: "object"
          properties: {
            product_id: { type: "string" }
            quantity: { type: "integer", minimum: 1 }
            price: { type: "number", minimum: 0 }
          }
        }
      }
      timestamp: { type: "string", format: "date-time" }
      metadata: {
        type: "object"
        properties: {
          source: { type: "string" }
          version: { type: "string" }
          correlation_id: { type: "string" }
        }
      }
    }
  }
  
  routing: {
    topic: "order.events"
    partition_key: "user_id"
    partition_count: 10
    replication_factor: 3
  }
  
  headers: [
    {
      name: "event_type"
      value: "order.created"
      required: true
    },
    {
      name: "event_version"
      value: "1.0"
      required: true
    },
    {
      name: "correlation_id"
      value: "{{correlation_id}}"
      required: true
    }
  ]
  
  validation: {
    enabled: true
    rules: [
      {
        name: "amount_positive"
        condition: "amount > 0"
        error_message: "订单金额必须大于0"
      },
      {
        name: "items_not_empty"
        condition: "items.length > 0"
        error_message: "订单必须包含至少一个商品"
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
        value: "{{current_timestamp}}"
      },
      {
        name: "add_correlation_id"
        action: "set_header"
        header: "correlation_id"
        value: "{{generate_uuid}}"
      }
    ]
  }
  
  delivery: {
    guaranteed: true
    retry_policy: {
      max_attempts: 3
      backoff: "exponential"
      initial_delay: "1s"
      max_delay: "30s"
    }
    dead_letter_queue: "order.events.dlq"
  }
  
  monitoring: {
    metrics: [
      "message_count",
      "delivery_latency",
      "error_rate",
      "throughput"
    ]
    alerts: [
      {
        name: "high_error_rate"
        condition: "error_rate > 5%"
        duration: "5m"
      },
      {
        name: "high_latency"
        condition: "delivery_latency > 1s"
        duration: "5m"
      }
    ]
  }
}
```

## 3. 关键元素

- message：消息声明
- description：描述信息
- version：版本号
- author：作者
- type：消息类型
- format：序列化格式
- priority：优先级
- schema：消息结构
- routing：路由配置
- headers：消息头
- validation：验证规则
- transformation：转换规则
- delivery：投递配置
- monitoring：监控配置

## 4. 高级用法

### 4.1 请求/响应消息

```dsl
message "payment_request" {
  description: "支付请求消息"
  version: "1.0.0"
  type: "request"
  format: "protobuf"
  priority: "high"
  
  schema: {
    type: "object"
    required: ["payment_id", "amount", "currency"]
    properties: {
      payment_id: { type: "string", format: "uuid" }
      order_id: { type: "string", format: "uuid" }
      amount: { type: "number", minimum: 0 }
      currency: { type: "string", enum: ["USD", "EUR", "CNY"] }
      payment_method: {
        type: "object"
        properties: {
          type: { type: "string", enum: ["credit_card", "debit_card", "bank_transfer"] }
          token: { type: "string" }
        }
      }
      metadata: {
        type: "object"
        properties: {
          user_id: { type: "string" }
          ip_address: { type: "string" }
          user_agent: { type: "string" }
        }
      }
    }
  }
  
  routing: {
    queue: "payment.requests"
    exchange: "payment"
    routing_key: "payment.request"
    durable: true
    auto_delete: false
  }
  
  headers: [
    {
      name: "message_type"
      value: "payment.request"
      required: true
    },
    {
      name: "priority"
      value: "high"
      required: true
    },
    {
      name: "correlation_id"
      value: "{{correlation_id}}"
      required: true
    }
  ]
  
  validation: {
    enabled: true
    rules: [
      {
        name: "amount_positive"
        condition: "amount > 0"
        error_message: "支付金额必须大于0"
      },
      {
        name: "valid_currency"
        condition: "currency in ['USD', 'EUR', 'CNY']"
        error_message: "不支持的货币类型"
      }
    ]
  }
  
  delivery: {
    guaranteed: true
    retry_policy: {
      max_attempts: 5
      backoff: "exponential"
      initial_delay: "1s"
      max_delay: "60s"
    }
    dead_letter_queue: "payment.requests.dlq"
    ttl: "5m"
  }
  
  response: {
    expected: true
    timeout: "30s"
    correlation_id: "{{correlation_id}}"
    response_queue: "payment.responses"
  }
}

message "payment_response" {
  description: "支付响应消息"
  version: "1.0.0"
  type: "response"
  format: "protobuf"
  
  schema: {
    type: "object"
    required: ["payment_id", "status", "timestamp"]
    properties: {
      payment_id: { type: "string", format: "uuid" }
      status: { type: "string", enum: ["success", "failed", "pending"] }
      transaction_id: { type: "string" }
      amount: { type: "number" }
      currency: { type: "string" }
      error_code: { type: "string" }
      error_message: { type: "string" }
      timestamp: { type: "string", format: "date-time" }
    }
  }
  
  routing: {
    queue: "payment.responses"
    exchange: "payment"
    routing_key: "payment.response"
  }
  
  headers: [
    {
      name: "message_type"
      value: "payment.response"
      required: true
    },
    {
      name: "correlation_id"
      value: "{{correlation_id}}"
      required: true
    }
  ]
}
```

### 4.2 流式消息

```dsl
message "sensor_data_stream" {
  description: "传感器数据流消息"
  version: "1.0.0"
  type: "stream"
  format: "avro"
  priority: "low"
  
  schema: {
    type: "object"
    required: ["sensor_id", "value", "timestamp"]
    properties: {
      sensor_id: { type: "string" }
      value: { type: "number" }
      unit: { type: "string" }
      timestamp: { type: "string", format: "date-time" }
      location: {
        type: "object"
        properties: {
          latitude: { type: "number" }
          longitude: { type: "number" }
          altitude: { type: "number" }
        }
      }
      metadata: {
        type: "object"
        properties: {
          battery_level: { type: "number" }
          signal_strength: { type: "number" }
          firmware_version: { type: "string" }
        }
      }
    }
  }
  
  routing: {
    topic: "sensor.data"
    partition_key: "sensor_id"
    partition_count: 20
    replication_factor: 2
    retention: "7d"
    cleanup_policy: "delete"
  }
  
  headers: [
    {
      name: "message_type"
      value: "sensor.data"
      required: true
    },
    {
      name: "sensor_type"
      value: "{{sensor_type}}"
      required: true
    }
  ]
  
  batching: {
    enabled: true
    max_batch_size: 1000
    max_batch_delay: "5s"
    compression: "snappy"
  }
  
  delivery: {
    guaranteed: false
    retry_policy: {
      max_attempts: 1
      backoff: "fixed"
      initial_delay: "1s"
    }
  }
  
  monitoring: {
    metrics: [
      "message_count",
      "batch_size",
      "compression_ratio",
      "throughput"
    ]
    alerts: [
      {
        name: "low_throughput"
        condition: "throughput < 1000/min"
        duration: "10m"
      }
    ]
  }
}
```

### 4.3 命令消息

```dsl
message "device_control_command" {
  description: "设备控制命令消息"
  version: "1.0.0"
  type: "command"
  format: "json"
  priority: "high"
  
  schema: {
    type: "object"
    required: ["device_id", "command", "timestamp"]
    properties: {
      device_id: { type: "string" }
      command: { type: "string", enum: ["start", "stop", "restart", "configure"] }
      parameters: {
        type: "object"
        properties: {
          temperature: { type: "number" }
          humidity: { type: "number" }
          duration: { type: "number" }
        }
      }
      timestamp: { type: "string", format: "date-time" }
      expires_at: { type: "string", format: "date-time" }
      metadata: {
        type: "object"
        properties: {
          user_id: { type: "string" }
          session_id: { type: "string" }
          source: { type: "string" }
        }
      }
    }
  }
  
  routing: {
    topic: "device.commands"
    partition_key: "device_id"
    partition_count: 5
    replication_factor: 3
  }
  
  headers: [
    {
      name: "message_type"
      value: "device.command"
      required: true
    },
    {
      name: "priority"
      value: "high"
      required: true
    },
    {
      name: "correlation_id"
      value: "{{correlation_id}}"
      required: true
    }
  ]
  
  validation: {
    enabled: true
    rules: [
      {
        name: "valid_device_id"
        condition: "device_id matches '^[A-Za-z0-9-]+$'"
        error_message: "设备ID格式不正确"
      },
      {
        name: "not_expired"
        condition: "expires_at > current_timestamp"
        error_message: "命令已过期"
      }
    ]
  }
  
  delivery: {
    guaranteed: true
    retry_policy: {
      max_attempts: 3
      backoff: "exponential"
      initial_delay: "1s"
      max_delay: "30s"
    }
    dead_letter_queue: "device.commands.dlq"
    ttl: "1h"
  }
  
  response: {
    expected: true
    timeout: "60s"
    correlation_id: "{{correlation_id}}"
    response_topic: "device.responses"
  }
  
  monitoring: {
    metrics: [
      "command_count",
      "execution_time",
      "success_rate",
      "error_rate"
    ]
    alerts: [
      {
        name: "high_error_rate"
        condition: "error_rate > 10%"
        duration: "5m"
      },
      {
        name: "slow_execution"
        condition: "execution_time > 30s"
        duration: "5m"
      }
    ]
  }
}
```

## 5. 代码生成模板

### 5.1 Kafka消息生成

```java
// OrderCreatedEvent.java
@JsonIgnoreProperties(ignoreUnknown = true)
public class OrderCreatedEvent {
    @JsonProperty("order_id")
    private String orderId;
    
    @JsonProperty("user_id")
    private String userId;
    
    @JsonProperty("amount")
    private BigDecimal amount;
    
    @JsonProperty("currency")
    private String currency = "USD";
    
    @JsonProperty("items")
    private List<OrderItem> items;
    
    @JsonProperty("timestamp")
    private String timestamp;
    
    @JsonProperty("metadata")
    private Map<String, Object> metadata;
    
    // Constructors, getters, setters
    
    public static class OrderItem {
        @JsonProperty("product_id")
        private String productId;
        
        @JsonProperty("quantity")
        private Integer quantity;
        
        @JsonProperty("price")
        private BigDecimal price;
        
        // Getters and setters
    }
}

// OrderEventProducer.java
@Component
public class OrderEventProducer {
    
    @Autowired
    private KafkaTemplate<String, OrderCreatedEvent> kafkaTemplate;
    
    @Value("${kafka.topic.order.events}")
    private String orderEventsTopic;
    
    public void sendOrderCreatedEvent(OrderCreatedEvent event) {
        // 添加消息头
        ProducerRecord<String, OrderCreatedEvent> record = 
            new ProducerRecord<>(orderEventsTopic, event.getUserId(), event);
        
        record.headers().add("event_type", "order.created".getBytes());
        record.headers().add("event_version", "1.0".getBytes());
        record.headers().add("correlation_id", 
            UUID.randomUUID().toString().getBytes());
        
        // 发送消息
        kafkaTemplate.send(record)
            .addCallback(
                result -> log.info("Order created event sent successfully"),
                ex -> log.error("Failed to send order created event", ex)
            );
    }
}

// OrderEventConsumer.java
@Component
public class OrderEventConsumer {
    
    @KafkaListener(
        topics = "${kafka.topic.order.events}",
        groupId = "order-processing-group",
        containerFactory = "kafkaListenerContainerFactory"
    )
    public void handleOrderCreatedEvent(
            @Payload OrderCreatedEvent event,
            @Header(KafkaHeaders.RECEIVED_TOPIC) String topic,
            @Header(KafkaHeaders.RECEIVED_PARTITION_ID) int partition,
            @Header(KafkaHeaders.OFFSET) long offset) {
        
        log.info("Received order created event: {}", event);
        
        try {
            // 验证消息
            validateOrderCreatedEvent(event);
            
            // 处理订单创建事件
            orderService.processOrderCreated(event);
            
        } catch (Exception e) {
            log.error("Error processing order created event", e);
            throw e; // 触发重试
        }
    }
    
    private void validateOrderCreatedEvent(OrderCreatedEvent event) {
        if (event.getAmount().compareTo(BigDecimal.ZERO) <= 0) {
            throw new IllegalArgumentException("订单金额必须大于0");
        }
        if (event.getItems() == null || event.getItems().isEmpty()) {
            throw new IllegalArgumentException("订单必须包含至少一个商品");
        }
    }
}
```

### 5.2 RabbitMQ消息生成

```java
// PaymentRequest.java
public class PaymentRequest {
    private String paymentId;
    private String orderId;
    private BigDecimal amount;
    private String currency;
    private PaymentMethod paymentMethod;
    private Map<String, Object> metadata;
    
    // Constructors, getters, setters
    
    public static class PaymentMethod {
        private String type;
        private String token;
        
        // Getters and setters
    }
}

// PaymentRequestProducer.java
@Component
public class PaymentRequestProducer {
    
    @Autowired
    private RabbitTemplate rabbitTemplate;
    
    @Value("${rabbitmq.exchange.payment}")
    private String paymentExchange;
    
    @Value("${rabbitmq.routing.key.payment.request}")
    private String paymentRequestRoutingKey;
    
    public void sendPaymentRequest(PaymentRequest request) {
        // 设置消息属性
        MessageProperties props = new MessageProperties();
        props.setContentType(MessageProperties.CONTENT_TYPE_JSON);
        props.setPriority(9); // 高优先级
        props.setExpiration("300000"); // 5分钟TTL
        props.setHeader("message_type", "payment.request");
        props.setHeader("priority", "high");
        props.setHeader("correlation_id", UUID.randomUUID().toString());
        
        // 创建消息
        Message message = new Message(
            objectMapper.writeValueAsBytes(request), props);
        
        // 发送消息
        rabbitTemplate.send(paymentExchange, paymentRequestRoutingKey, message);
    }
}

// PaymentRequestConsumer.java
@Component
public class PaymentRequestConsumer {
    
    @RabbitListener(
        queues = "${rabbitmq.queue.payment.requests}",
        containerFactory = "rabbitListenerContainerFactory"
    )
    public void handlePaymentRequest(PaymentRequest request) {
        log.info("Received payment request: {}", request);
        
        try {
            // 验证请求
            validatePaymentRequest(request);
            
            // 处理支付请求
            PaymentResponse response = paymentService.processPayment(request);
            
            // 发送响应
            sendPaymentResponse(response);
            
        } catch (Exception e) {
            log.error("Error processing payment request", e);
            throw e; // 触发重试
        }
    }
    
    private void validatePaymentRequest(PaymentRequest request) {
        if (request.getAmount().compareTo(BigDecimal.ZERO) <= 0) {
            throw new IllegalArgumentException("支付金额必须大于0");
        }
        if (!Arrays.asList("USD", "EUR", "CNY").contains(request.getCurrency())) {
            throw new IllegalArgumentException("不支持的货币类型");
        }
    }
}
```

### 5.3 CloudEvents生成

```json
{
  "specversion": "1.0",
  "id": "uuid-1234-5678-9012",
  "source": "/order-service",
  "type": "order.created",
  "datacontenttype": "application/json",
  "data": {
    "order_id": "uuid-order-1234",
    "user_id": "uuid-user-5678",
    "amount": 99.99,
    "currency": "USD",
    "items": [
      {
        "product_id": "prod-123",
        "quantity": 2,
        "price": 49.99
      }
    ],
    "timestamp": "2024-01-15T10:30:00Z"
  },
  "time": "2024-01-15T10:30:00Z",
  "correlationid": "uuid-correlation-9012"
}
```

```java
// CloudEventsProducer.java
@Component
public class CloudEventsProducer {
    
    @Autowired
    private KafkaTemplate<String, CloudEvent> kafkaTemplate;
    
    public void sendOrderCreatedEvent(OrderCreatedEvent event) {
        CloudEvent cloudEvent = CloudEventBuilder.v1()
            .withId(UUID.randomUUID().toString())
            .withSource("/order-service")
            .withType("order.created")
            .withDataContentType("application/json")
            .withData(objectMapper.writeValueAsBytes(event))
            .withTime(Instant.now())
            .withExtension("correlationid", UUID.randomUUID().toString())
            .build();
        
        kafkaTemplate.send("order.events", cloudEvent);
    }
}
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - message.name
    - message.description
    - message.version
    - message.type
    - message.schema
  
  type_constraints:
    - field: "message.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "message.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "message.type"
      type: "string"
      enum: ["event", "request", "response", "stream", "command"]
    - field: "message.format"
      type: "string"
      enum: ["json", "protobuf", "avro", "xml", "yaml"]
```

### 6.2 消息验证规则

```yaml
message_validation:
  schema_consistency:
    - rule: "all required fields must be defined in schema"
    - rule: "field types must be valid"
    - rule: "enum values must be consistent"
  
  routing_validation:
    - rule: "routing configuration must be valid for message type"
    - rule: "partition keys must reference existing fields"
    - rule: "queue/topic names must follow naming conventions"
  
  delivery_validation:
    - rule: "retry policy must be valid"
    - rule: "TTL must be positive if specified"
    - rule: "dead letter queue must be configured for guaranteed delivery"
```

## 7. 最佳实践

### 7.1 消息设计模式

```dsl
# 事件消息模式
message "domain_event" {
  description: "领域事件消息"
  type: "event"
  format: "json"
  
  schema: {
    type: "object"
    required: ["event_id", "aggregate_id", "event_type", "timestamp"]
    properties: {
      event_id: { type: "string", format: "uuid" }
      aggregate_id: { type: "string" }
      event_type: { type: "string" }
      event_version: { type: "string" }
      timestamp: { type: "string", format: "date-time" }
      data: { type: "object" }
      metadata: { type: "object" }
    }
  }
  
  routing: {
    topic: "domain.events"
    partition_key: "aggregate_id"
  }
  
  headers: [
    {
      name: "event_type"
      value: "{{event_type}}"
      required: true
    }
  ]
}

# 命令消息模式
message "domain_command" {
  description: "领域命令消息"
  type: "command"
  format: "json"
  
  schema: {
    type: "object"
    required: ["command_id", "aggregate_id", "command_type", "timestamp"]
    properties: {
      command_id: { type: "string", format: "uuid" }
      aggregate_id: { type: "string" }
      command_type: { type: "string" }
      command_version: { type: "string" }
      timestamp: { type: "string", format: "date-time" }
      data: { type: "object" }
      metadata: { type: "object" }
    }
  }
  
  routing: {
    queue: "domain.commands"
    exchange: "domain"
    routing_key: "domain.command"
  }
  
  delivery: {
    guaranteed: true
    retry_policy: {
      max_attempts: 3
      backoff: "exponential"
    }
  }
  
  response: {
    expected: true
    timeout: "30s"
  }
}
```

### 7.2 消息命名规范

```dsl
# 推荐命名模式
message "domain_action_type" {
  # 领域_动作_类型
}

message "service_operation_type" {
  # 服务_操作_类型
}

message "version_domain_type" {
  # 版本_领域_类型
}
```

## 8. 与主流标准的映射

| DSL元素 | Kafka | RabbitMQ | MQTT | CloudEvents | Apache Pulsar |
|---------|-------|----------|------|-------------|---------------|
| message | record | message | message | event | message |
| schema | schema | - | - | data schema | schema |
| routing | topic/partition | exchange/queue | topic | source/type | topic |
| headers | headers | headers | properties | extensions | properties |
| delivery | acks | confirm | qos | - | delivery semantics |

## 9. 工程实践示例

```dsl
# 生产环境订单事件消息示例
message "production_order_created_event" {
  description: "生产环境订单创建事件"
  version: "1.0.0"
  author: "system"
  
  type: "event"
  format: "json"
  priority: "normal"
  
  schema: {
    type: "object"
    required: ["order_id", "user_id", "amount", "timestamp"]
    properties: {
      order_id: { type: "string", format: "uuid" }
      user_id: { type: "string", format: "uuid" }
      amount: { type: "number", minimum: 0 }
      currency: { type: "string", default: "USD" }
      items: {
        type: "array"
        items: {
          type: "object"
          properties: {
            product_id: { type: "string" }
            quantity: { type: "integer", minimum: 1 }
            price: { type: "number", minimum: 0 }
          }
        }
      }
      timestamp: { type: "string", format: "date-time" }
      metadata: {
        type: "object"
        properties: {
          source: { type: "string" }
          version: { type: "string" }
          correlation_id: { type: "string" }
          user_agent: { type: "string" }
          ip_address: { type: "string" }
        }
      }
    }
  }
  
  routing: {
    topic: "order.events"
    partition_key: "user_id"
    partition_count: 20
    replication_factor: 3
    retention: "30d"
    cleanup_policy: "delete"
  }
  
  headers: [
    {
      name: "event_type"
      value: "order.created"
      required: true
    },
    {
      name: "event_version"
      value: "1.0"
      required: true
    },
    {
      name: "correlation_id"
      value: "{{correlation_id}}"
      required: true
    },
    {
      name: "source"
      value: "order-service"
      required: true
    }
  ]
  
  validation: {
    enabled: true
    rules: [
      {
        name: "amount_positive"
        condition: "amount > 0"
        error_message: "订单金额必须大于0"
      },
      {
        name: "items_not_empty"
        condition: "items.length > 0"
        error_message: "订单必须包含至少一个商品"
      },
      {
        name: "valid_currency"
        condition: "currency in ['USD', 'EUR', 'CNY']"
        error_message: "不支持的货币类型"
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
        value: "{{current_timestamp}}"
      },
      {
        name: "add_correlation_id"
        action: "set_header"
        header: "correlation_id"
        value: "{{generate_uuid}}"
      },
      {
        name: "add_source"
        action: "set_header"
        header: "source"
        value: "order-service"
      }
    ]
  }
  
  delivery: {
    guaranteed: true
    retry_policy: {
      max_attempts: 3
      backoff: "exponential"
      initial_delay: "1s"
      max_delay: "30s"
    }
    dead_letter_queue: "order.events.dlq"
  }
  
  monitoring: {
    metrics: [
      "message_count",
      "delivery_latency",
      "error_rate",
      "throughput",
      "partition_lag"
    ]
    alerts: [
      {
        name: "high_error_rate"
        condition: "error_rate > 5%"
        duration: "5m"
        severity: "critical"
      },
      {
        name: "high_latency"
        condition: "delivery_latency > 1s"
        duration: "5m"
        severity: "warning"
      },
      {
        name: "high_partition_lag"
        condition: "partition_lag > 1000"
        duration: "10m"
        severity: "warning"
      }
    ]
    tracing: {
      enabled: true
      provider: "jaeger"
      sampling_rate: 0.1
    }
  }
  
  security: {
    encryption: {
      enabled: true
      algorithm: "AES-256-GCM"
    }
    authentication: {
      enabled: true
      type: "sasl_ssl"
    }
    authorization: {
      enabled: true
      acl: [
        {
          resource: "order.events"
          operation: "write"
          principal: "order-service"
        }
      ]
    }
  }
}
```

这个DSL设计为消息建模提供了完整的配置语言，支持事件、请求/响应、流、命令等多种消息类型，同时保持了良好的可扩展性和可维护性。
