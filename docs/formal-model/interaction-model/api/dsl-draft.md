# API建模DSL草案

## 1. 设计目标

- 用统一DSL描述RESTful、GraphQL、gRPC等API接口
- 支持自动生成OpenAPI、GraphQL SDL、gRPC proto等主流标准
- 支持API版本管理、认证授权、安全策略等高级特性

## 2. 基本语法结构

```dsl
api "user_management_api" {
  description: "用户管理API"
  version: "1.0.0"
  author: "system"
  
  base_url: "https://api.example.com/v1"
  protocol: "rest"
  
  authentication: {
    type: "bearer_token"
    required: true
    scopes: ["read:users", "write:users"]
  }
  
  endpoints: [
    {
      name: "get_user"
      method: "GET"
      path: "/users/{id}"
      description: "获取用户信息"
      parameters: [
        {
          name: "id"
          type: "string"
          required: true
          location: "path"
          description: "用户ID"
        },
        {
          name: "fields"
          type: "string"
          required: false
          location: "query"
          description: "返回字段，逗号分隔"
        }
      ]
      responses: [
        {
          code: 200
          description: "成功"
          schema: {
            type: "object"
            properties: {
              id: { type: "string" }
              name: { type: "string" }
              email: { type: "string" }
              age: { type: "integer" }
              created_at: { type: "string", format: "date-time" }
            }
          }
        },
        {
          code: 404
          description: "用户不存在"
          schema: {
            type: "object"
            properties: {
              error: { type: "string" }
              message: { type: "string" }
            }
          }
        }
      ]
    },
    {
      name: "create_user"
      method: "POST"
      path: "/users"
      description: "创建新用户"
      request_body: {
        type: "object"
        required: ["name", "email"]
        properties: {
          name: { type: "string", min_length: 1, max_length: 100 }
          email: { type: "string", format: "email" }
          age: { type: "integer", minimum: 0, maximum: 150 }
          password: { type: "string", min_length: 8 }
        }
      }
      responses: [
        {
          code: 201
          description: "创建成功"
          schema: {
            type: "object"
            properties: {
              id: { type: "string" }
              name: { type: "string" }
              email: { type: "string" }
              created_at: { type: "string", format: "date-time" }
            }
          }
        },
        {
          code: 400
          description: "请求参数错误"
          schema: {
            type: "object"
            properties: {
              error: { type: "string" }
              message: { type: "string" }
              details: { type: "array", items: { type: "string" } }
            }
          }
        }
      ]
    },
    {
      name: "update_user"
      method: "PUT"
      path: "/users/{id}"
      description: "更新用户信息"
      parameters: [
        {
          name: "id"
          type: "string"
          required: true
          location: "path"
          description: "用户ID"
        }
      ]
      request_body: {
        type: "object"
        properties: {
          name: { type: "string", min_length: 1, max_length: 100 }
          email: { type: "string", format: "email" }
          age: { type: "integer", minimum: 0, maximum: 150 }
        }
      }
      responses: [
        {
          code: 200
          description: "更新成功"
          schema: {
            type: "object"
            properties: {
              id: { type: "string" }
              name: { type: "string" }
              email: { type: "string" }
              updated_at: { type: "string", format: "date-time" }
            }
          }
        }
      ]
    },
    {
      name: "delete_user"
      method: "DELETE"
      path: "/users/{id}"
      description: "删除用户"
      parameters: [
        {
          name: "id"
          type: "string"
          required: true
          location: "path"
          description: "用户ID"
        }
      ]
      responses: [
        {
          code: 204
          description: "删除成功"
        },
        {
          code: 404
          description: "用户不存在"
        }
      ]
    }
  ]
  
  error_responses: [
    {
      code: 401
      description: "未授权"
      schema: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
        }
      }
    },
    {
      code: 403
      description: "禁止访问"
      schema: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
        }
      }
    },
    {
      code: 500
      description: "服务器内部错误"
      schema: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
        }
      }
    }
  ]
  
  rate_limiting: {
    enabled: true
    requests_per_minute: 100
    burst_limit: 20
  }
  
  caching: {
    enabled: true
    ttl: 300
    cacheable_endpoints: ["get_user"]
  }
  
  monitoring: {
    metrics: [
      "request_count",
      "response_time",
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
        name: "high_response_time"
        condition: "response_time > 2s"
        duration: "5m"
      }
    ]
  }
}
```

## 3. 关键元素

- api：API声明
- description：描述信息
- version：版本号
- author：作者
- base_url：基础URL
- protocol：协议类型
- authentication：认证配置
- endpoints：端点定义
- error_responses：错误响应
- rate_limiting：限流配置
- caching：缓存配置
- monitoring：监控配置

## 4. 高级用法

### 4.1 GraphQL API

```dsl
api "user_graphql_api" {
  description: "用户管理GraphQL API"
  version: "1.0.0"
  protocol: "graphql"
  
  schema: {
    types: [
      {
        name: "User"
        fields: [
          { name: "id", type: "ID!", description: "用户ID" },
          { name: "name", type: "String!", description: "用户名" },
          { name: "email", type: "String!", description: "邮箱" },
          { name: "age", type: "Int", description: "年龄" },
          { name: "createdAt", type: "DateTime!", description: "创建时间" }
        ]
      },
      {
        name: "UserInput"
        fields: [
          { name: "name", type: "String!", description: "用户名" },
          { name: "email", type: "String!", description: "邮箱" },
          { name: "age", type: "Int", description: "年龄" }
        ]
      }
    ]
    
    queries: [
      {
        name: "user"
        type: "User"
        args: [
          { name: "id", type: "ID!", description: "用户ID" }
        ]
        description: "获取用户信息"
      },
      {
        name: "users"
        type: "[User!]!"
        args: [
          { name: "limit", type: "Int", description: "限制数量" },
          { name: "offset", type: "Int", description: "偏移量" }
        ]
        description: "获取用户列表"
      }
    ]
    
    mutations: [
      {
        name: "createUser"
        type: "User!"
        args: [
          { name: "input", type: "UserInput!", description: "用户输入" }
        ]
        description: "创建用户"
      },
      {
        name: "updateUser"
        type: "User!"
        args: [
          { name: "id", type: "ID!", description: "用户ID" },
          { name: "input", type: "UserInput!", description: "用户输入" }
        ]
        description: "更新用户"
      },
      {
        name: "deleteUser"
        type: "Boolean!"
        args: [
          { name: "id", type: "ID!", description: "用户ID" }
        ]
        description: "删除用户"
      }
    ]
  }
  
  authentication: {
    type: "jwt"
    required: true
  }
  
  rate_limiting: {
    enabled: true
    requests_per_minute: 1000
  }
}
```

### 4.2 gRPC API

```dsl
api "user_grpc_api" {
  description: "用户管理gRPC API"
  version: "1.0.0"
  protocol: "grpc"
  
  services: [
    {
      name: "UserService"
      description: "用户服务"
      methods: [
        {
          name: "GetUser"
          request: {
            type: "GetUserRequest"
            fields: [
              { name: "id", type: "string", number: 1 }
            ]
          }
          response: {
            type: "User"
            fields: [
              { name: "id", type: "string", number: 1 }
              { name: "name", type: "string", number: 2 }
              { name: "email", type: "string", number: 3 }
              { name: "age", type: "int32", number: 4 }
            ]
          }
          description: "获取用户信息"
        },
        {
          name: "CreateUser"
          request: {
            type: "CreateUserRequest"
            fields: [
              { name: "name", type: "string", number: 1 }
              { name: "email", type: "string", number: 2 }
              { name: "age", type: "int32", number: 3 }
            ]
          }
          response: {
            type: "User"
          }
          description: "创建用户"
        },
        {
          name: "UpdateUser"
          request: {
            type: "UpdateUserRequest"
            fields: [
              { name: "id", type: "string", number: 1 }
              { name: "name", type: "string", number: 2 }
              { name: "email", type: "string", number: 3 }
              { name: "age", type: "int32", number: 4 }
            ]
          }
          response: {
            type: "User"
          }
          description: "更新用户"
        },
        {
          name: "DeleteUser"
          request: {
            type: "DeleteUserRequest"
            fields: [
              { name: "id", type: "string", number: 1 }
            ]
          }
          response: {
            type: "DeleteUserResponse"
            fields: [
              { name: "success", type: "bool", number: 1 }
            ]
          }
          description: "删除用户"
        }
      ]
    }
  ]
  
  authentication: {
    type: "grpc_auth"
    required: true
  }
  
  interceptors: [
    {
      name: "logging"
      type: "unary"
    },
    {
      name: "metrics"
      type: "unary"
    }
  ]
}
```

## 5. 代码生成模板

### 5.1 OpenAPI生成

```yaml
openapi: 3.0.0
info:
  title: User Management API
  version: 1.0.0
  description: 用户管理API

servers:
  - url: https://api.example.com/v1

components:
  securitySchemes:
    bearerAuth:
      type: http
      scheme: bearer
      bearerFormat: JWT

  schemas:
    User:
      type: object
      properties:
        id:
          type: string
        name:
          type: string
        email:
          type: string
        age:
          type: integer
        created_at:
          type: string
          format: date-time

paths:
  /users/{id}:
    get:
      summary: 获取用户信息
      parameters:
        - name: id
          in: path
          required: true
          schema:
            type: string
        - name: fields
          in: query
          schema:
            type: string
      responses:
        '200':
          description: 成功
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/User'
        '404':
          description: 用户不存在
          content:
            application/json:
              schema:
                type: object
                properties:
                  error:
                    type: string
                  message:
                    type: string

  /users:
    post:
      summary: 创建新用户
      requestBody:
        required: true
        content:
          application/json:
            schema:
              type: object
              required:
                - name
                - email
              properties:
                name:
                  type: string
                  minLength: 1
                  maxLength: 100
                email:
                  type: string
                  format: email
                age:
                  type: integer
                  minimum: 0
                  maximum: 150
      responses:
        '201':
          description: 创建成功
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/User'
```

### 5.2 GraphQL SDL生成

```graphql
type User {
  id: ID!
  name: String!
  email: String!
  age: Int
  createdAt: DateTime!
}

input UserInput {
  name: String!
  email: String!
  age: Int
}

type Query {
  user(id: ID!): User
  users(limit: Int, offset: Int): [User!]!
}

type Mutation {
  createUser(input: UserInput!): User!
  updateUser(id: ID!, input: UserInput!): User!
  deleteUser(id: ID!): Boolean!
}

scalar DateTime
```

### 5.3 gRPC Proto生成

```protobuf
syntax = "proto3";

package user;

service UserService {
  rpc GetUser(GetUserRequest) returns (User);
  rpc CreateUser(CreateUserRequest) returns (User);
  rpc UpdateUser(UpdateUserRequest) returns (User);
  rpc DeleteUser(DeleteUserRequest) returns (DeleteUserResponse);
}

message User {
  string id = 1;
  string name = 2;
  string email = 3;
  int32 age = 4;
  string created_at = 5;
}

message GetUserRequest {
  string id = 1;
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

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - api.name
    - api.description
    - api.version
    - api.endpoints
  
  type_constraints:
    - field: "api.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "api.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "api.endpoints"
      type: "array"
      min_items: 1
```

### 6.2 API验证规则

```yaml
api_validation:
  endpoint_consistency:
    - rule: "all endpoint paths must be unique"
    - rule: "all endpoint methods must be valid"
    - rule: "all parameters must have valid types"
  
  response_validation:
    - rule: "all responses must have valid status codes"
    - rule: "all response schemas must be valid"
    - rule: "error responses must be defined"
```

## 7. 最佳实践

### 7.1 API设计模式

```dsl
# RESTful API模式
api "restful_api" {
  description: "RESTful API设计"
  protocol: "rest"
  
  endpoints: [
    {
      name: "list_resources"
      method: "GET"
      path: "/resources"
      description: "获取资源列表"
    },
    {
      name: "get_resource"
      method: "GET"
      path: "/resources/{id}"
      description: "获取单个资源"
    },
    {
      name: "create_resource"
      method: "POST"
      path: "/resources"
      description: "创建资源"
    },
    {
      name: "update_resource"
      method: "PUT"
      path: "/resources/{id}"
      description: "更新资源"
    },
    {
      name: "delete_resource"
      method: "DELETE"
      path: "/resources/{id}"
      description: "删除资源"
    }
  ]
}

# GraphQL API模式
api "graphql_api" {
  description: "GraphQL API设计"
  protocol: "graphql"
  
  schema: {
    types: [
      {
        name: "Resource"
        fields: [
          { name: "id", type: "ID!" },
          { name: "name", type: "String!" },
          { name: "description", type: "String" }
        ]
      }
    ]
    
    queries: [
      {
        name: "resource"
        type: "Resource"
        args: [{ name: "id", type: "ID!" }]
      },
      {
        name: "resources"
        type: "[Resource!]!"
      }
    ]
    
    mutations: [
      {
        name: "createResource"
        type: "Resource!"
        args: [{ name: "input", type: "ResourceInput!" }]
      }
    ]
  }
}
```

### 7.2 API命名规范

```dsl
# 推荐命名模式
api "domain_service_api" {
  # 领域_服务_API
}

api "version_domain_api" {
  # 版本_领域_API
}

api "protocol_service_api" {
  # 协议_服务_API
}
```

## 8. 与主流标准的映射

| DSL元素 | OpenAPI | GraphQL | gRPC | Swagger |
|---------|---------|---------|------|---------|
| api | info | schema | service | info |
| endpoints | paths | queries/mutations | methods | paths |
| parameters | parameters | args | request | parameters |
| responses | responses | types | response | responses |
| authentication | securitySchemes | directives | interceptors | securityDefinitions |

## 9. 工程实践示例

```dsl
# 生产环境用户管理API示例
api "production_user_api" {
  description: "生产环境用户管理API"
  version: "1.0.0"
  author: "system"
  
  base_url: "https://api.example.com/v1"
  protocol: "rest"
  
  authentication: {
    type: "bearer_token"
    required: true
    scopes: ["read:users", "write:users", "delete:users"]
  }
  
  endpoints: [
    {
      name: "get_user"
      method: "GET"
      path: "/users/{id}"
      description: "获取用户信息"
      parameters: [
        {
          name: "id"
          type: "string"
          required: true
          location: "path"
          description: "用户ID"
        }
      ]
      responses: [
        {
          code: 200
          description: "成功"
          schema: {
            type: "object"
            properties: {
              id: { type: "string" }
              name: { type: "string" }
              email: { type: "string" }
              age: { type: "integer" }
              created_at: { type: "string", format: "date-time" }
            }
          }
        }
      ]
    },
    {
      name: "create_user"
      method: "POST"
      path: "/users"
      description: "创建新用户"
      request_body: {
        type: "object"
        required: ["name", "email"]
        properties: {
          name: { type: "string", min_length: 1, max_length: 100 }
          email: { type: "string", format: "email" }
          age: { type: "integer", minimum: 0, maximum: 150 }
        }
      }
      responses: [
        {
          code: 201
          description: "创建成功"
          schema: {
            type: "object"
            properties: {
              id: { type: "string" }
              name: { type: "string" }
              email: { type: "string" }
              created_at: { type: "string", format: "date-time" }
            }
          }
        }
      ]
    }
  ]
  
  error_responses: [
    {
      code: 401
      description: "未授权"
      schema: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
        }
      }
    },
    {
      code: 403
      description: "禁止访问"
      schema: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
        }
      }
    },
    {
      code: 500
      description: "服务器内部错误"
      schema: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
        }
      }
    }
  ]
  
  rate_limiting: {
    enabled: true
    requests_per_minute: 100
    burst_limit: 20
  }
  
  caching: {
    enabled: true
    ttl: 300
    cacheable_endpoints: ["get_user"]
  }
  
  monitoring: {
    metrics: [
      "request_count",
      "response_time",
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
        name: "high_response_time"
        condition: "response_time > 2s"
        duration: "5m"
      }
    ]
  }
  
  security: {
    cors: {
      enabled: true
      allowed_origins: ["https://app.example.com"]
      allowed_methods: ["GET", "POST", "PUT", "DELETE"]
      allowed_headers: ["Content-Type", "Authorization"]
    }
    rate_limiting: {
      enabled: true
      requests_per_minute: 100
      burst_limit: 20
    }
  }
}
```

这个DSL设计为API建模提供了完整的配置语言，支持RESTful、GraphQL、gRPC等多种协议，同时保持了良好的可扩展性和可维护性。
