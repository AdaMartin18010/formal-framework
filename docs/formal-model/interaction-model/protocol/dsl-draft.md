# 协议建模DSL草案

## 1. 设计目标

- 用统一DSL描述HTTP、WebSocket、gRPC、MQTT等协议要素
- 支持自动生成协议配置、适配层、协议转换代码
- 支持协议安全、加密、认证、负载均衡等高级特性

## 2. 基本语法结构

```dsl
protocol "http_protocol" {
  description: "HTTP协议配置"
  version: "1.0.0"
  author: "system"
  
  type: "http"
  version: "1.1"
  
  connection: {
    keep_alive: true
    timeout: "30s"
    max_connections: 1000
    max_requests_per_connection: 100
  }
  
  security: {
    tls: {
      enabled: true
      certificate_file: "/etc/ssl/certs/server.crt"
      private_key_file: "/etc/ssl/private/server.key"
      cipher_suites: ["TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384"]
      min_version: "TLSv1.2"
    }
    cors: {
      enabled: true
      allowed_origins: ["https://app.example.com"]
      allowed_methods: ["GET", "POST", "PUT", "DELETE"]
      allowed_headers: ["Content-Type", "Authorization"]
    }
  }
  
  compression: {
    enabled: true
    algorithms: ["gzip", "deflate"]
    min_size: 1024
  }
  
  caching: {
    enabled: true
    max_age: 3600
    etag: true
    last_modified: true
  }
  
  rate_limiting: {
    enabled: true
    requests_per_minute: 100
    burst_limit: 20
    window_size: "1m"
  }
  
  monitoring: {
    metrics: [
      "request_count",
      "response_time",
      "error_rate",
      "throughput"
    ]
    logging: {
      enabled: true
      level: "info"
      format: "json"
    }
  }
}
```

## 3. 关键元素

- protocol：协议声明
- description：描述信息
- version：版本号
- author：作者
- type：协议类型
- connection：连接配置
- security：安全配置
- compression：压缩配置
- caching：缓存配置
- rate_limiting：限流配置
- monitoring：监控配置

## 4. 高级用法

### 4.1 WebSocket协议

```dsl
protocol "websocket_protocol" {
  description: "WebSocket协议配置"
  version: "1.0.0"
  type: "websocket"
  
  connection: {
    path: "/ws"
    heartbeat: "10s"
    max_connections: 1000
    max_message_size: "1MB"
    ping_interval: "30s"
    pong_timeout: "10s"
  }
  
  subprotocols: [
    {
      name: "json"
      version: "1.0"
    },
    {
      name: "binary"
      version: "1.0"
    }
  ]
  
  message_types: [
    {
      name: "chat"
      format: "json"
      schema: {
        type: "object"
        properties: {
          type: { type: "string" }
          message: { type: "string" }
          timestamp: { type: "string", format: "date-time" }
        }
      }
    },
    {
      name: "notification"
      format: "json"
      schema: {
        type: "object"
        properties: {
          type: { type: "string" }
          title: { type: "string" }
          body: { type: "string" }
          priority: { type: "string", enum: ["low", "medium", "high"] }
        }
      }
    }
  ]
  
  security: {
    authentication: {
      type: "jwt"
      required: true
      token_header: "Authorization"
    }
    origin_validation: {
      enabled: true
      allowed_origins: ["https://app.example.com"]
    }
  }
  
  clustering: {
    enabled: true
    adapter: "redis"
    redis_url: "redis://localhost:6379"
    channel: "websocket"
  }
  
  monitoring: {
    metrics: [
      "connection_count",
      "message_count",
      "error_count",
      "latency"
    ]
    alerts: [
      {
        name: "high_connection_count"
        condition: "connection_count > 800"
        duration: "5m"
      },
      {
        name: "high_error_rate"
        condition: "error_rate > 5%"
        duration: "5m"
      }
    ]
  }
}
```

### 4.2 gRPC协议

```dsl
protocol "grpc_protocol" {
  description: "gRPC协议配置"
  version: "1.0.0"
  type: "grpc"
  
  connection: {
    port: 9090
    max_concurrent_streams: 100
    max_connection_idle: "1h"
    max_connection_age: "24h"
    max_connection_age_grace: "1h"
    time: "1h"
    timeout: "1h"
  }
  
  proto_files: [
    {
      path: "service.proto"
      import_paths: ["./protos"]
    }
  ]
  
  services: [
    {
      name: "UserService"
      methods: [
        {
          name: "GetUser"
          request_type: "GetUserRequest"
          response_type: "User"
          streaming: false
        },
        {
          name: "ListUsers"
          request_type: "ListUsersRequest"
          response_type: "User"
          streaming: "server"
        }
      ]
    }
  ]
  
  interceptors: [
    {
      name: "logging"
      type: "unary"
      config: {
        log_requests: true
        log_responses: true
        log_errors: true
      }
    },
    {
      name: "metrics"
      type: "unary"
      config: {
        record_requests: true
        record_responses: true
        record_errors: true
      }
    },
    {
      name: "auth"
      type: "unary"
      config: {
        token_header: "Authorization"
        required: true
      }
    }
  ]
  
  security: {
    tls: {
      enabled: true
      certificate_file: "/etc/ssl/certs/grpc.crt"
      private_key_file: "/etc/ssl/private/grpc.key"
      ca_file: "/etc/ssl/certs/ca.crt"
    }
    authentication: {
      type: "jwt"
      required: true
    }
  }
  
  load_balancing: {
    policy: "round_robin"
    health_check: {
      enabled: true
      interval: "30s"
      timeout: "5s"
    }
  }
  
  monitoring: {
    metrics: [
      "request_count",
      "response_time",
      "error_rate",
      "stream_count"
    ]
    tracing: {
      enabled: true
      provider: "jaeger"
      sampling_rate: 0.1
    }
  }
}
```

### 4.3 MQTT协议

```dsl
protocol "mqtt_protocol" {
  description: "MQTT协议配置"
  version: "1.0.0"
  type: "mqtt"
  
  connection: {
    broker: "mqtt.example.com"
    port: 1883
    keep_alive: "60s"
    clean_session: true
    max_inflight: 20
    max_queued: 100
  }
  
  authentication: {
    type: "username_password"
    username: "client"
    password: "secret"
  }
  
  topics: [
    {
      name: "sensors/temperature"
      qos: 1
      retain: false
      wildcard: false
    },
    {
      name: "sensors/humidity"
      qos: 1
      retain: false
      wildcard: false
    },
    {
      name: "devices/+/status"
      qos: 0
      retain: true
      wildcard: true
    }
  ]
  
  subscriptions: [
    {
      topic: "sensors/#"
      qos: 1
      callback: "handle_sensor_data"
    },
    {
      topic: "devices/+/status"
      qos: 0
      callback: "handle_device_status"
    }
  ]
  
  message_formats: [
    {
      name: "sensor_data"
      format: "json"
      schema: {
        type: "object"
        properties: {
          sensor_id: { type: "string" }
          value: { type: "number" }
          unit: { type: "string" }
          timestamp: { type: "string", format: "date-time" }
        }
      }
    },
    {
      name: "device_status"
      format: "json"
      schema: {
        type: "object"
        properties: {
          device_id: { type: "string" }
          status: { type: "string", enum: ["online", "offline", "error"] }
          battery: { type: "number" }
          timestamp: { type: "string", format: "date-time" }
        }
      }
    }
  ]
  
  security: {
    tls: {
      enabled: true
      certificate_file: "/etc/ssl/certs/mqtt.crt"
      private_key_file: "/etc/ssl/private/mqtt.key"
      ca_file: "/etc/ssl/certs/ca.crt"
    }
  }
  
  persistence: {
    enabled: true
    type: "file"
    directory: "/var/lib/mqtt"
    max_messages: 10000
  }
  
  monitoring: {
    metrics: [
      "message_count",
      "connection_count",
      "subscription_count",
      "error_count"
    ]
    alerts: [
      {
        name: "high_message_rate"
        condition: "message_count > 1000/min"
        duration: "5m"
      }
    ]
  }
}
```

## 5. 代码生成模板

### 5.1 HTTP协议生成

```nginx
# nginx.conf
http {
    # 基础配置
    keepalive_timeout 30s;
    keepalive_requests 100;
    client_max_body_size 10m;
    
    # 压缩配置
    gzip on;
    gzip_types text/plain text/css application/json application/javascript;
    gzip_min_length 1024;
    
    # 缓存配置
    location ~* \.(css|js|png|jpg|jpeg|gif|ico|svg)$ {
        expires 1y;
        add_header Cache-Control "public, immutable";
    }
    
    # 限流配置
    limit_req_zone $binary_remote_addr zone=api:10m rate=100r/m;
    limit_req zone=api burst=20 nodelay;
    
    # 安全配置
    add_header X-Frame-Options DENY;
    add_header X-Content-Type-Options nosniff;
    add_header X-XSS-Protection "1; mode=block";
    
    # CORS配置
    add_header Access-Control-Allow-Origin "https://app.example.com";
    add_header Access-Control-Allow-Methods "GET, POST, PUT, DELETE";
    add_header Access-Control-Allow-Headers "Content-Type, Authorization";
    
    server {
        listen 80;
        server_name api.example.com;
        
        # SSL配置
        listen 443 ssl http2;
        ssl_certificate /etc/ssl/certs/server.crt;
        ssl_certificate_key /etc/ssl/private/server.key;
        ssl_protocols TLSv1.2 TLSv1.3;
        ssl_ciphers ECDHE-RSA-AES256-GCM-SHA384;
        
        location / {
            proxy_pass http://backend;
            proxy_set_header Host $host;
            proxy_set_header X-Real-IP $remote_addr;
            proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
            proxy_set_header X-Forwarded-Proto $scheme;
        }
    }
}
```

### 5.2 WebSocket协议生成

```javascript
// websocket-server.js
const WebSocket = require('ws');
const jwt = require('jsonwebtoken');
const Redis = require('ioredis');

const wss = new WebSocket.Server({
  port: 8080,
  path: '/ws',
  maxPayload: 1024 * 1024, // 1MB
});

const redis = new Redis('redis://localhost:6379');

// 心跳配置
const HEARTBEAT_INTERVAL = 10000; // 10s
const PONG_TIMEOUT = 10000; // 10s

wss.on('connection', (ws, req) => {
  console.log('New WebSocket connection');
  
  // 认证
  const token = req.headers.authorization?.replace('Bearer ', '');
  if (!token) {
    ws.close(1008, 'Authentication required');
    return;
  }
  
  try {
    const decoded = jwt.verify(token, process.env.JWT_SECRET);
    ws.userId = decoded.userId;
  } catch (error) {
    ws.close(1008, 'Invalid token');
    return;
  }
  
  // 心跳
  ws.isAlive = true;
  ws.on('pong', () => {
    ws.isAlive = true;
  });
  
  // 消息处理
  ws.on('message', (data) => {
    try {
      const message = JSON.parse(data);
      handleMessage(ws, message);
    } catch (error) {
      ws.send(JSON.stringify({
        type: 'error',
        message: 'Invalid message format'
      }));
    }
  });
  
  // 广播到集群
  redis.publish('websocket', JSON.stringify({
    type: 'user_connected',
    userId: ws.userId
  }));
});

// 心跳检查
setInterval(() => {
  wss.clients.forEach((ws) => {
    if (ws.isAlive === false) {
      return ws.terminate();
    }
    ws.isAlive = false;
    ws.ping();
  });
}, HEARTBEAT_INTERVAL);

function handleMessage(ws, message) {
  switch (message.type) {
    case 'chat':
      // 处理聊天消息
      broadcastMessage({
        type: 'chat',
        userId: ws.userId,
        message: message.message,
        timestamp: new Date().toISOString()
      });
      break;
    case 'notification':
      // 处理通知消息
      broadcastMessage({
        type: 'notification',
        title: message.title,
        body: message.body,
        priority: message.priority
      });
      break;
    default:
      ws.send(JSON.stringify({
        type: 'error',
        message: 'Unknown message type'
      }));
  }
}

function broadcastMessage(message) {
  wss.clients.forEach((client) => {
    if (client.readyState === WebSocket.OPEN) {
      client.send(JSON.stringify(message));
    }
  });
}
```

### 5.3 gRPC协议生成

```protobuf
// service.proto
syntax = "proto3";

package user;

import "google/protobuf/timestamp.proto";

service UserService {
  rpc GetUser(GetUserRequest) returns (User);
  rpc ListUsers(ListUsersRequest) returns (stream User);
  rpc CreateUser(CreateUserRequest) returns (User);
  rpc UpdateUser(UpdateUserRequest) returns (User);
  rpc DeleteUser(DeleteUserRequest) returns (DeleteUserResponse);
}

message User {
  string id = 1;
  string name = 2;
  string email = 3;
  int32 age = 4;
  google.protobuf.Timestamp created_at = 5;
}

message GetUserRequest {
  string id = 1;
}

message ListUsersRequest {
  int32 limit = 1;
  int32 offset = 2;
}

message CreateUserRequest {
  string name = 1;
  string email = 2;
  int32 age = 3;
}

message UpdateUserRequest {
  string id = 1;
  string name = 2;
  string email = 3;
  int32 age = 4;
}

message DeleteUserRequest {
  string id = 1;
}

message DeleteUserResponse {
  bool success = 1;
}
```

```go
// server.go
package main

import (
    "context"
    "log"
    "net"
    "time"

    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials"
    "google.golang.org/grpc/keepalive"
    pb "path/to/proto"
)

type server struct {
    pb.UnimplementedUserServiceServer
}

func (s *server) GetUser(ctx context.Context, req *pb.GetUserRequest) (*pb.User, error) {
    // 实现获取用户逻辑
    return &pb.User{
        Id:   req.Id,
        Name: "John Doe",
        Email: "john@example.com",
        Age:  30,
    }, nil
}

func (s *server) ListUsers(req *pb.ListUsersRequest, stream pb.UserService_ListUsersServer) error {
    // 实现流式获取用户列表逻辑
    users := []*pb.User{
        {Id: "1", Name: "User 1", Email: "user1@example.com", Age: 25},
        {Id: "2", Name: "User 2", Email: "user2@example.com", Age: 30},
    }
    
    for _, user := range users {
        if err := stream.Send(user); err != nil {
            return err
        }
        time.Sleep(100 * time.Millisecond)
    }
    return nil
}

func main() {
    lis, err := net.Listen("tcp", ":9090")
    if err != nil {
        log.Fatalf("failed to listen: %v", err)
    }

    // TLS配置
    creds, err := credentials.NewServerTLSFromFile("server.crt", "server.key")
    if err != nil {
        log.Fatalf("failed to load TLS: %v", err)
    }

    // 服务器配置
    s := grpc.NewServer(
        grpc.Creds(creds),
        grpc.KeepaliveParams(keepalive.ServerParameters{
            MaxConnectionIdle: 1 * time.Hour,
            MaxConnectionAge:  24 * time.Hour,
            MaxConnectionAgeGrace: 1 * time.Hour,
            Time:              1 * time.Hour,
            Timeout:           1 * time.Hour,
        }),
        grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy{
            MinTime:             30 * time.Second,
            PermitWithoutStream: true,
        }),
    )

    pb.RegisterUserServiceServer(s, &server{})

    log.Printf("Server listening on :9090")
    if err := s.Serve(lis); err != nil {
        log.Fatalf("failed to serve: %v", err)
    }
}
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - protocol.name
    - protocol.description
    - protocol.version
    - protocol.type
  
  type_constraints:
    - field: "protocol.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "protocol.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "protocol.type"
      type: "string"
      enum: ["http", "websocket", "grpc", "mqtt", "tcp", "udp"]
```

### 6.2 协议验证规则

```yaml
protocol_validation:
  connection_consistency:
    - rule: "all connection parameters must be valid"
    - rule: "timeout values must be positive"
    - rule: "port numbers must be in valid range"
  
  security_validation:
    - rule: "TLS certificates must exist if enabled"
    - rule: "authentication must be configured if required"
    - rule: "CORS origins must be valid URLs"
```

## 7. 最佳实践

### 7.1 协议设计模式

```dsl
# HTTP协议模式
protocol "http_protocol" {
  description: "HTTP协议配置"
  type: "http"
  version: "1.1"
  
  connection: {
    keep_alive: true
    timeout: "30s"
    max_connections: 1000
  }
  
  security: {
    tls: {
      enabled: true
      certificate_file: "/etc/ssl/certs/server.crt"
      private_key_file: "/etc/ssl/private/server.key"
    }
    cors: {
      enabled: true
      allowed_origins: ["https://app.example.com"]
    }
  }
  
  compression: {
    enabled: true
    algorithms: ["gzip", "deflate"]
  }
}

# WebSocket协议模式
protocol "websocket_protocol" {
  description: "WebSocket协议配置"
  type: "websocket"
  
  connection: {
    path: "/ws"
    heartbeat: "10s"
    max_connections: 1000
  }
  
  security: {
    authentication: {
      type: "jwt"
      required: true
    }
  }
  
  clustering: {
    enabled: true
    adapter: "redis"
  }
}
```

### 7.2 协议命名规范

```dsl
# 推荐命名模式
protocol "type_service_protocol" {
  # 类型_服务_协议
}

protocol "version_type_protocol" {
  # 版本_类型_协议
}

protocol "environment_type_protocol" {
  # 环境_类型_协议
}
```

## 8. 与主流标准的映射

| DSL元素 | HTTP | WebSocket | gRPC | MQTT | Nginx | Envoy |
|---------|------|-----------|------|------|-------|-------|
| protocol | - | - | - | - | - | - |
| connection | keepalive | heartbeat | keepalive | keepalive | keepalive | keepalive |
| security | TLS/CORS | auth | TLS/auth | TLS/auth | ssl | tls |
| compression | gzip | - | - | - | gzip | compression |
| monitoring | logs | metrics | metrics | metrics | access_log | stats |

## 9. 工程实践示例

```dsl
# 生产环境HTTP协议配置示例
protocol "production_http_protocol" {
  description: "生产环境HTTP协议配置"
  version: "1.0.0"
  author: "system"
  
  type: "http"
  version: "1.1"
  
  connection: {
    keep_alive: true
    timeout: "30s"
    max_connections: 10000
    max_requests_per_connection: 1000
    send_timeout: "30s"
    read_timeout: "30s"
  }
  
  security: {
    tls: {
      enabled: true
      certificate_file: "/etc/ssl/certs/production.crt"
      private_key_file: "/etc/ssl/private/production.key"
      ca_file: "/etc/ssl/certs/ca.crt"
      cipher_suites: [
        "TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384",
        "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256"
      ]
      min_version: "TLSv1.2"
      max_version: "TLSv1.3"
    }
    cors: {
      enabled: true
      allowed_origins: [
        "https://app.example.com",
        "https://admin.example.com"
      ]
      allowed_methods: ["GET", "POST", "PUT", "DELETE", "OPTIONS"]
      allowed_headers: [
        "Content-Type",
        "Authorization",
        "X-Requested-With"
      ]
      exposed_headers: ["X-Total-Count", "X-Page-Count"]
      allow_credentials: true
      max_age: 86400
    }
    headers: {
      x_frame_options: "DENY"
      x_content_type_options: "nosniff"
      x_xss_protection: "1; mode=block"
      strict_transport_security: "max-age=31536000; includeSubDomains"
      content_security_policy: "default-src 'self'"
    }
  }
  
  compression: {
    enabled: true
    algorithms: ["gzip", "deflate", "br"]
    min_size: 1024
    level: 6
  }
  
  caching: {
    enabled: true
    max_age: 3600
    etag: true
    last_modified: true
    vary: ["Accept-Encoding", "Accept-Language"]
  }
  
  rate_limiting: {
    enabled: true
    requests_per_minute: 1000
    burst_limit: 100
    window_size: "1m"
    storage: "redis"
    redis_url: "redis://localhost:6379"
  }
  
  load_balancing: {
    enabled: true
    algorithm: "round_robin"
    health_check: {
      enabled: true
      interval: "30s"
      timeout: "5s"
      path: "/health"
      expected_status: 200
    }
    upstream_servers: [
      "http://backend1:8080",
      "http://backend2:8080",
      "http://backend3:8080"
    ]
  }
  
  monitoring: {
    metrics: [
      "request_count",
      "response_time",
      "error_rate",
      "throughput",
      "connection_count"
    ]
    logging: {
      enabled: true
      level: "info"
      format: "json"
      destination: "file"
      file_path: "/var/log/nginx/access.log"
      rotation: {
        enabled: true
        max_size: "100m"
        max_files: 10
      }
    }
    alerts: [
      {
        name: "high_error_rate"
        condition: "error_rate > 5%"
        duration: "5m"
        severity: "critical"
      },
      {
        name: "high_response_time"
        condition: "response_time > 2s"
        duration: "5m"
        severity: "warning"
      },
      {
        name: "high_connection_count"
        condition: "connection_count > 8000"
        duration: "5m"
        severity: "warning"
      }
    ]
  }
  
  performance: {
    worker_processes: 4
    worker_connections: 1024
    multi_accept: true
    use: "epoll"
    accept_mutex: true
    accept_mutex_delay: "500ms"
  }
}
```

这个DSL设计为协议建模提供了完整的配置语言，支持HTTP、WebSocket、gRPC、MQTT等多种协议，同时保持了良好的可扩展性和可维护性。
