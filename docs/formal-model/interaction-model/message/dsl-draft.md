# 消息建模DSL草案

## 1. 设计目标

- 用统一DSL描述请求/响应、事件、流等消息要素。
- 支持自动生成Kafka、RabbitMQ、MQTT、CloudEvents等主流消息配置与代码。

## 2. 基本语法结构

```dsl
message OrderCreated {
  type: event
  format: json
  fields: {
    orderId: string
    userId: string
    amount: float
  }
  route: topic("order.events")
}

message PaymentRequest {
  type: request
  format: protobuf
  fields: {
    paymentId: string
    amount: float
  }
  route: queue("payment.requests")
}
```

## 3. 关键元素

- message：消息定义
- type：消息类型（event/request/response/stream/command）
- format：序列化格式
- fields：字段结构
- route：路由规则（topic/queue/subject等）

## 4. 示例

```dsl
message UserRegistered {
  type: event
  format: json
  fields: {
    userId: string
    email: string
  }
  route: topic("user.events")
}

message DataStream {
  type: stream
  format: protobuf
  fields: {
    chunk: bytes
    seq: int
  }
  route: subject("data.stream")
}
```

## 5. 与主流标准的映射

- 可自动转换为Kafka、RabbitMQ、MQTT、CloudEvents等配置
- 支持与主流消息中间件、事件总线集成

## 6. 递归扩展建议

- 支持消息过滤、分区、优先级等高级特性
- 支持消息追踪、监控与重试策略
