# 交互标准模型

## 概述

交互标准模型定义了系统组件间交互的标准化实现，基于交互元模型构建，提供统一的交互模式和通信协议。

## 标准交互模式

### 1. 同步交互模式

#### 请求-响应模式

```yaml
RequestResponsePattern:
  protocol: HTTP/HTTPS
  method: POST
  headers:
    Content-Type: application/json
    Authorization: Bearer {token}
  request:
    body: RequestPayload
    timeout: 30s
  response:
    status: 200|201|400|500
    body: ResponsePayload
    headers:
      Content-Type: application/json
```

#### 实现示例

```python
import requests
import json
from typing import Dict, Any

class RequestResponseClient:
    def __init__(self, base_url: str, timeout: int = 30):
        self.base_url = base_url
        self.timeout = timeout
        self.session = requests.Session()
    
    def send_request(self, endpoint: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """发送请求-响应交互"""
        url = f"{self.base_url}{endpoint}"
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.get_token()}"
        }
        
        try:
            response = self.session.post(
                url, 
                json=payload, 
                headers=headers, 
                timeout=self.timeout
            )
            response.raise_for_status()
            return response.json()
        except requests.exceptions.RequestException as e:
            raise InteractionError(f"请求失败: {e}")
```

### 2. 异步交互模式

#### 消息传递模式

```yaml
MessagePassingPattern:
  protocol: AMQP/MQTT
  exchange: topic
  routing_key: "service.action"
  message:
    headers:
      message_id: string
      timestamp: datetime
      correlation_id: string
    body: MessagePayload
  acknowledgment: auto|manual
  retry_policy:
    max_retries: 3
    backoff: exponential
```

#### 实现示例1

```python
import pika
import json
from datetime import datetime
from typing import Dict, Any

class MessagePassingClient:
    def __init__(self, connection_string: str):
        self.connection_string = connection_string
        self.connection = None
        self.channel = None
    
    def connect(self):
        """建立连接"""
        self.connection = pika.BlockingConnection(
            pika.URLParameters(self.connection_string)
        )
        self.channel = self.connection.channel()
        self.channel.exchange_declare(exchange='services', exchange_type='topic')
    
    def send_message(self, routing_key: str, payload: Dict[str, Any]) -> str:
        """发送异步消息"""
        message_id = self.generate_message_id()
        message = {
            "message_id": message_id,
            "timestamp": datetime.utcnow().isoformat(),
            "payload": payload
        }
        
        self.channel.basic_publish(
            exchange='services',
            routing_key=routing_key,
            body=json.dumps(message),
            properties=pika.BasicProperties(
                message_id=message_id,
                timestamp=int(datetime.utcnow().timestamp())
            )
        )
        
        return message_id
```

### 3. 事件驱动模式

#### 发布-订阅模式

```yaml
PubSubPattern:
  protocol: WebSocket/Server-Sent Events
  topics:
    - "user.events"
    - "system.events"
    - "business.events"
  subscription:
    filters: Filter[]
    callback: CallbackFunction
  event:
    type: EventType
    data: EventData
    metadata: EventMetadata
```

#### 实现示例2

```python
import asyncio
import websockets
import json
from typing import Callable, Dict, Any

class EventDrivenClient:
    def __init__(self, websocket_url: str):
        self.websocket_url = websocket_url
        self.subscriptions = {}
    
    async def connect(self):
        """建立WebSocket连接"""
        self.websocket = await websockets.connect(self.websocket_url)
        asyncio.create_task(self.listen_for_events())
    
    async def subscribe(self, topic: str, callback: Callable):
        """订阅事件主题"""
        self.subscriptions[topic] = callback
        await self.websocket.send(json.dumps({
            "action": "subscribe",
            "topic": topic
        }))
    
    async def publish(self, topic: str, event_data: Dict[str, Any]):
        """发布事件"""
        event = {
            "topic": topic,
            "data": event_data,
            "timestamp": datetime.utcnow().isoformat()
        }
        await self.websocket.send(json.dumps({
            "action": "publish",
            "event": event
        }))
    
    async def listen_for_events(self):
        """监听事件"""
        async for message in self.websocket:
            event = json.loads(message)
            topic = event.get("topic")
            if topic in self.subscriptions:
                await self.subscriptions[topic](event)
```

## 标准通信协议

### 1. HTTP/HTTPS协议

#### 标准端点定义

```yaml
HTTPEndpoints:
  health:
    path: "/health"
    method: GET
    response: HealthStatus
  
  metrics:
    path: "/metrics"
    method: GET
    response: MetricsData
  
  api:
    path: "/api/v1/{resource}"
    method: GET|POST|PUT|DELETE
    response: ResourceData
```

#### 标准响应格式

```json
{
  "status": "success|error",
  "data": {},
  "message": "string",
  "timestamp": "2024-01-01T00:00:00Z",
  "request_id": "uuid"
}
```

### 2. gRPC协议

#### 服务定义

```protobuf
syntax = "proto3";

package formal.framework.v1;

service InteractionService {
  rpc SendRequest(Request) returns (Response);
  rpc StreamMessages(stream Message) returns (stream Message);
}

message Request {
  string id = 1;
  string endpoint = 2;
  bytes payload = 3;
  map<string, string> headers = 4;
}

message Response {
  string id = 1;
  int32 status_code = 2;
  bytes payload = 3;
  map<string, string> headers = 4;
}
```

### 3. GraphQL协议

#### Schema定义

```graphql
type Query {
  health: HealthStatus
  metrics: MetricsData
  resource(id: ID!): Resource
}

type Mutation {
  createResource(input: ResourceInput!): Resource
  updateResource(id: ID!, input: ResourceInput!): Resource
  deleteResource(id: ID!): Boolean
}

type Subscription {
  resourceUpdated(id: ID!): Resource
  systemEvents: SystemEvent
}
```

## 标准错误处理

### 错误分类

```yaml
ErrorTypes:
  client_errors:
    - code: 400
      name: "BadRequest"
      description: "请求参数错误"
    - code: 401
      name: "Unauthorized"
      description: "未授权访问"
    - code: 403
      name: "Forbidden"
      description: "禁止访问"
    - code: 404
      name: "NotFound"
      description: "资源不存在"
  
  server_errors:
    - code: 500
      name: "InternalServerError"
      description: "服务器内部错误"
    - code: 502
      name: "BadGateway"
      description: "网关错误"
    - code: 503
      name: "ServiceUnavailable"
      description: "服务不可用"
    - code: 504
      name: "GatewayTimeout"
      description: "网关超时"
```

### 错误响应格式

```json
{
  "error": {
    "code": "400",
    "name": "BadRequest",
    "message": "请求参数错误",
    "details": {
      "field": "email",
      "reason": "invalid_format"
    },
    "timestamp": "2024-01-01T00:00:00Z",
    "request_id": "uuid"
  }
}
```

## 标准重试机制

### 重试策略

```yaml
RetryPolicy:
  max_retries: 3
  backoff_strategy: exponential
  initial_delay: 1s
  max_delay: 30s
  jitter: true
  retryable_errors:
    - "timeout"
    - "connection_error"
    - "5xx_server_error"
```

### 实现示例3

```python
import time
import random
from typing import Callable, Any

class RetryMechanism:
    def __init__(self, max_retries: int = 3, initial_delay: float = 1.0):
        self.max_retries = max_retries
        self.initial_delay = initial_delay
    
    def execute_with_retry(self, func: Callable, *args, **kwargs) -> Any:
        """执行带重试的函数"""
        last_exception = None
        
        for attempt in range(self.max_retries + 1):
            try:
                return func(*args, **kwargs)
            except Exception as e:
                last_exception = e
                if attempt < self.max_retries and self.is_retryable(e):
                    delay = self.calculate_delay(attempt)
                    time.sleep(delay)
                else:
                    break
        
        raise last_exception
    
    def is_retryable(self, exception: Exception) -> bool:
        """判断异常是否可重试"""
        retryable_types = (TimeoutError, ConnectionError, ServerError)
        return isinstance(exception, retryable_types)
    
    def calculate_delay(self, attempt: int) -> float:
        """计算重试延迟"""
        delay = self.initial_delay * (2 ** attempt)
        jitter = random.uniform(0.1, 0.3) * delay
        return delay + jitter
```

## 标准监控指标

### 交互指标

```yaml
InteractionMetrics:
  request_count:
    type: counter
    labels: [method, endpoint, status]
    description: "请求总数"
  
  request_duration:
    type: histogram
    labels: [method, endpoint]
    buckets: [0.1, 0.5, 1.0, 2.0, 5.0]
    description: "请求持续时间"
  
  error_rate:
    type: gauge
    labels: [endpoint]
    description: "错误率"
  
  active_connections:
    type: gauge
    labels: [protocol]
    description: "活跃连接数"
```

## 验证和测试

### 交互验证

```python
def validate_interaction_pattern(pattern: str, implementation: Any) -> bool:
    """验证交互模式实现"""
    validators = {
        "request_response": validate_request_response,
        "message_passing": validate_message_passing,
        "event_driven": validate_event_driven
    }
    
    validator = validators.get(pattern)
    if not validator:
        raise ValueError(f"未知的交互模式: {pattern}")
    
    return validator(implementation)

def validate_request_response(implementation: Any) -> bool:
    """验证请求-响应模式"""
    required_methods = ["send_request", "handle_response"]
    return all(hasattr(implementation, method) for method in required_methods)
```

### 性能测试

```python
def test_interaction_performance(client: Any, test_cases: List[Dict]) -> Dict:
    """测试交互性能"""
    results = {}
    
    for test_case in test_cases:
        start_time = time.time()
        try:
            response = client.send_request(
                test_case["endpoint"], 
                test_case["payload"]
            )
            duration = time.time() - start_time
            results[test_case["name"]] = {
                "success": True,
                "duration": duration,
                "response_size": len(str(response))
            }
        except Exception as e:
            results[test_case["name"]] = {
                "success": False,
                "error": str(e)
            }
    
    return results
```

## 最佳实践

1. **协议选择**: 根据交互类型选择合适的协议
2. **错误处理**: 实现统一的错误处理机制
3. **重试策略**: 配置合理的重试策略
4. **监控指标**: 收集关键的交互指标
5. **安全考虑**: 实现适当的认证和授权
6. **性能优化**: 优化交互性能
7. **文档维护**: 保持API文档的更新

## 相关文档

- [交互元模型](../meta-models/interaction-model/README.md)
- [验证脚本](../../tools/verification-scripts/README.md)
- [监控工具](../../tools/monitoring/README.md)
