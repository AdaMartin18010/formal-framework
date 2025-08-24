# 契约建模DSL草案

## 1. 设计目标

- 用统一DSL描述接口、数据、行为等契约要素
- 支持自动生成OpenAPI、Pact、Avro Schema等主流契约文档与测试
- 支持契约变更检测、兼容性校验、契约驱动开发（CDC）等高级特性

## 2. 基本语法结构

```dsl
contract "user_service_v1" {
  description: "用户服务契约V1"
  version: "1.0.0"
  author: "system"
  
  service: "user-service"
  interface: "getUser"
  
  request: {
    method: "GET"
    path: "/users/{id}"
    headers: [
      {
        name: "Authorization"
        type: "string"
        required: true
        description: "Bearer token"
      }
    ]
    parameters: [
      {
        name: "id"
        type: "string"
        location: "path"
        required: true
        description: "用户ID"
        format: "uuid"
      }
    ]
    body: null
  }
  
  response: {
    status: 200
    headers: [
      {
        name: "Content-Type"
        value: "application/json"
      }
    ]
    body: {
      type: "object"
      properties: {
        id: { type: "string", format: "uuid" }
        name: { type: "string", min_length: 1, max_length: 100 }
        email: { type: "string", format: "email" }
        age: { type: "integer", minimum: 0, maximum: 150 }
        created_at: { type: "string", format: "date-time" }
      }
      required: ["id", "name", "email"]
    }
  }
  
  error_responses: [
    {
      status: 404
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          code: { type: "string" }
        }
        required: ["error", "message"]
      }
    },
    {
      status: 401
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
        }
        required: ["error", "message"]
      }
    }
  ]
  
  compatibility: {
    backward_compatible: true
    compatible_versions: ["0.9.0", "0.9.1"]
    breaking_changes: []
    deprecation_notice: null
  }
  
  validation: {
    enabled: true
    rules: [
      {
        name: "user_id_format"
        condition: "id matches UUID pattern"
        error_message: "用户ID必须是有效的UUID格式"
      },
      {
        name: "email_format"
        condition: "email matches email pattern"
        error_message: "邮箱格式不正确"
      }
    ]
  }
  
  testing: {
    enabled: true
    test_cases: [
      {
        name: "get_existing_user"
        request: {
          id: "123e4567-e89b-12d3-a456-426614174000"
        }
        expected_response: {
          status: 200
          body: {
            id: "123e4567-e89b-12d3-a456-426614174000"
            name: "John Doe"
            email: "john@example.com"
            age: 30
          }
        }
      },
      {
        name: "get_nonexistent_user"
        request: {
          id: "00000000-0000-0000-0000-000000000000"
        }
        expected_response: {
          status: 404
          body: {
            error: "not_found"
            message: "User not found"
          }
        }
      }
    ]
  }
  
  documentation: {
    summary: "获取用户信息"
    description: "根据用户ID获取用户的详细信息"
    examples: [
      {
        name: "基本用法"
        request: "GET /users/123e4567-e89b-12d3-a456-426614174000"
        response: {
          status: 200
          body: {
            "id": "123e4567-e89b-12d3-a456-426614174000",
            "name": "John Doe",
            "email": "john@example.com",
            "age": 30,
            "created_at": "2024-01-15T10:30:00Z"
          }
        }
      }
    ]
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
      }
    ]
  }
}
```

## 3. 关键元素

- contract：契约声明
- description：描述信息
- version：版本号
- author：作者
- service：服务名称
- interface：接口名称
- request：请求定义
- response：响应定义
- error_responses：错误响应
- compatibility：兼容性配置
- validation：验证规则
- testing：测试配置
- documentation：文档配置
- monitoring：监控配置

## 4. 高级用法

### 4.1 复杂契约定义

```dsl
contract "order_service_v2" {
  description: "订单服务契约V2"
  version: "2.0.0"
  author: "system"
  
  service: "order-service"
  interface: "createOrder"
  
  request: {
    method: "POST"
    path: "/orders"
    headers: [
      {
        name: "Authorization"
        type: "string"
        required: true
        description: "Bearer token"
      },
      {
        name: "Content-Type"
        value: "application/json"
        required: true
      }
    ]
    body: {
      type: "object"
      required: ["user_id", "items"]
      properties: {
        user_id: { type: "string", format: "uuid" }
        items: {
          type: "array"
          min_items: 1
          items: {
            type: "object"
            required: ["product_id", "quantity"]
            properties: {
              product_id: { type: "string" }
              quantity: { type: "integer", minimum: 1 }
              price: { type: "number", minimum: 0 }
            }
          }
        }
        shipping_address: {
          type: "object"
          properties: {
            street: { type: "string" }
            city: { type: "string" }
            state: { type: "string" }
            zip_code: { type: "string" }
            country: { type: "string" }
          }
        }
        payment_method: {
          type: "object"
          properties: {
            type: { type: "string", enum: ["credit_card", "debit_card", "bank_transfer"] }
            token: { type: "string" }
          }
        }
        metadata: {
          type: "object"
          additional_properties: true
        }
      }
    }
  }
  
  response: {
    status: 201
    headers: [
      {
        name: "Content-Type"
        value: "application/json"
      },
      {
        name: "Location"
        value: "/orders/{order_id}"
      }
    ]
    body: {
      type: "object"
      properties: {
        order_id: { type: "string", format: "uuid" }
        user_id: { type: "string", format: "uuid" }
        status: { type: "string", enum: ["pending", "confirmed", "cancelled"] }
        total_amount: { type: "number", minimum: 0 }
        currency: { type: "string", default: "USD" }
        items: {
          type: "array"
          items: {
            type: "object"
            properties: {
              product_id: { type: "string" }
              quantity: { type: "integer" }
              price: { type: "number" }
              subtotal: { type: "number" }
            }
          }
        }
        created_at: { type: "string", format: "date-time" }
        updated_at: { type: "string", format: "date-time" }
      }
      required: ["order_id", "user_id", "status", "total_amount"]
    }
  }
  
  error_responses: [
    {
      status: 400
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          details: {
            type: "array"
            items: {
              type: "object"
              properties: {
                field: { type: "string" }
                message: { type: "string" }
              }
            }
          }
        }
        required: ["error", "message"]
      }
    },
    {
      status: 422
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          validation_errors: {
            type: "array"
            items: {
              type: "object"
              properties: {
                field: { type: "string" }
                code: { type: "string" }
                message: { type: "string" }
              }
            }
          }
        }
        required: ["error", "message"]
      }
    }
  ]
  
  compatibility: {
    backward_compatible: false
    compatible_versions: ["1.0.0", "1.1.0"]
    breaking_changes: [
      {
        type: "field_removed"
        field: "customer_id"
        message: "customer_id字段已移除，请使用user_id"
      },
      {
        type: "field_type_changed"
        field: "total_amount"
        old_type: "string"
        new_type: "number"
        message: "total_amount字段类型从string改为number"
      }
    ]
    migration_guide: "https://docs.example.com/migration/v1-to-v2"
  }
  
  validation: {
    enabled: true
    rules: [
      {
        name: "user_id_format"
        condition: "user_id matches UUID pattern"
        error_message: "用户ID必须是有效的UUID格式"
      },
      {
        name: "items_not_empty"
        condition: "items.length > 0"
        error_message: "订单必须包含至少一个商品"
      },
      {
        name: "quantity_positive"
        condition: "all items.quantity > 0"
        error_message: "商品数量必须大于0"
      },
      {
        name: "price_positive"
        condition: "all items.price >= 0"
        error_message: "商品价格不能为负数"
      }
    ]
  }
  
  testing: {
    enabled: true
    test_cases: [
      {
        name: "create_valid_order"
        request: {
          body: {
            user_id: "123e4567-e89b-12d3-a456-426614174000"
            items: [
              {
                product_id: "prod-123"
                quantity: 2
                price: 29.99
              }
            ]
          }
        }
        expected_response: {
          status: 201
          body: {
            order_id: "{{uuid}}"
            user_id: "123e4567-e89b-12d3-a456-426614174000"
            status: "pending"
            total_amount: 59.98
          }
        }
      },
      {
        name: "create_order_with_empty_items"
        request: {
          body: {
            user_id: "123e4567-e89b-12d3-a456-426614174000"
            items: []
          }
        }
        expected_response: {
          status: 400
          body: {
            error: "validation_error"
            message: "订单必须包含至少一个商品"
          }
        }
      }
    ]
  }
}
```

### 4.2 契约版本管理

```dsl
contract "payment_service_v1" {
  description: "支付服务契约V1"
  version: "1.0.0"
  author: "system"
  
  service: "payment-service"
  interface: "processPayment"
  
  request: {
    method: "POST"
    path: "/payments"
    body: {
      type: "object"
      required: ["order_id", "amount", "currency"]
      properties: {
        order_id: { type: "string", format: "uuid" }
        amount: { type: "number", minimum: 0 }
        currency: { type: "string", enum: ["USD", "EUR", "CNY"] }
        payment_method: {
          type: "object"
          properties: {
            type: { type: "string", enum: ["credit_card", "debit_card"] }
            token: { type: "string" }
          }
        }
      }
    }
  }
  
  response: {
    status: 200
    body: {
      type: "object"
      properties: {
        payment_id: { type: "string", format: "uuid" }
        order_id: { type: "string", format: "uuid" }
        status: { type: "string", enum: ["success", "failed", "pending"] }
        transaction_id: { type: "string" }
        amount: { type: "number" }
        currency: { type: "string" }
        processed_at: { type: "string", format: "date-time" }
      }
      required: ["payment_id", "order_id", "status"]
    }
  }
  
  compatibility: {
    backward_compatible: true
    compatible_versions: ["0.9.0"]
    breaking_changes: []
    deprecation_notice: null
  }
}

contract "payment_service_v2" {
  description: "支付服务契约V2"
  version: "2.0.0"
  author: "system"
  
  service: "payment-service"
  interface: "processPayment"
  
  request: {
    method: "POST"
    path: "/payments"
    body: {
      type: "object"
      required: ["order_id", "amount", "currency"]
      properties: {
        order_id: { type: "string", format: "uuid" }
        amount: { type: "number", minimum: 0 }
        currency: { type: "string", enum: ["USD", "EUR", "CNY", "JPY"] }
        payment_method: {
          type: "object"
          properties: {
            type: { type: "string", enum: ["credit_card", "debit_card", "bank_transfer"] }
            token: { type: "string" }
            metadata: { type: "object" }
          }
        }
        metadata: { type: "object" }
      }
    }
  }
  
  response: {
    status: 200
    body: {
      type: "object"
      properties: {
        payment_id: { type: "string", format: "uuid" }
        order_id: { type: "string", format: "uuid" }
        status: { type: "string", enum: ["success", "failed", "pending", "cancelled"] }
        transaction_id: { type: "string" }
        amount: { type: "number" }
        currency: { type: "string" }
        processed_at: { type: "string", format: "date-time" }
        metadata: { type: "object" }
      }
      required: ["payment_id", "order_id", "status"]
    }
  }
  
  compatibility: {
    backward_compatible: true
    compatible_versions: ["1.0.0", "1.1.0"]
    breaking_changes: []
    deprecation_notice: null
  }
}
```

## 5. 代码生成模板

### 5.1 OpenAPI生成

```yaml
openapi: 3.0.0
info:
  title: User Service API
  version: 1.0.0
  description: 用户服务API

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
      required:
        - id
        - name
        - email
      properties:
        id:
          type: string
          format: uuid
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
        created_at:
          type: string
          format: date-time

    Error:
      type: object
      required:
        - error
        - message
      properties:
        error:
          type: string
        message:
          type: string
        code:
          type: string

paths:
  /users/{id}:
    get:
      summary: 获取用户信息
      description: 根据用户ID获取用户的详细信息
      operationId: getUser
      security:
        - bearerAuth: []
      parameters:
        - name: id
          in: path
          required: true
          description: 用户ID
          schema:
            type: string
            format: uuid
      responses:
        '200':
          description: 成功
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/User'
        '401':
          description: 未授权
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Error'
        '404':
          description: 用户不存在
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/Error'
```

### 5.2 Pact契约测试生成

```javascript
// user-service-consumer.test.js
const { Pact } = require('@pact-foundation/pact');
const { getUser } = require('./user-service-client');

describe('User Service Contract', () => {
  const provider = new Pact({
    consumer: 'user-service-consumer',
    provider: 'user-service',
    port: 1234,
    log: '../logs/pact.log',
    dir: '../pacts',
    logLevel: 'INFO',
  });

  beforeAll(() => provider.setup());
  afterAll(() => provider.finalize());
  afterEach(() => provider.verify());

  describe('getUser', () => {
    it('should return user when user exists', async () => {
      const expectedUser = {
        id: '123e4567-e89b-12d3-a456-426614174000',
        name: 'John Doe',
        email: 'john@example.com',
        age: 30,
        created_at: '2024-01-15T10:30:00Z',
      };

      await provider.addInteraction({
        state: 'user exists',
        uponReceiving: 'a request for user',
        withRequest: {
          method: 'GET',
          path: '/users/123e4567-e89b-12d3-a456-426614174000',
          headers: {
            Authorization: 'Bearer token',
          },
        },
        willRespondWith: {
          status: 200,
          headers: {
            'Content-Type': 'application/json',
          },
          body: expectedUser,
        },
      });

      const user = await getUser('123e4567-e89b-12d3-a456-426614174000');
      expect(user).toEqual(expectedUser);
    });

    it('should return 404 when user does not exist', async () => {
      await provider.addInteraction({
        state: 'user does not exist',
        uponReceiving: 'a request for non-existent user',
        withRequest: {
          method: 'GET',
          path: '/users/00000000-0000-0000-0000-000000000000',
          headers: {
            Authorization: 'Bearer token',
          },
        },
        willRespondWith: {
          status: 404,
          headers: {
            'Content-Type': 'application/json',
          },
          body: {
            error: 'not_found',
            message: 'User not found',
          },
        },
      });

      await expect(
        getUser('00000000-0000-0000-0000-000000000000')
      ).rejects.toThrow('User not found');
    });
  });
});
```

### 5.3 Avro Schema生成

```json
{
  "namespace": "com.example.user",
  "type": "record",
  "name": "User",
  "version": "1.0.0",
  "fields": [
    {
      "name": "id",
      "type": "string",
      "doc": "用户ID"
    },
    {
      "name": "name",
      "type": "string",
      "doc": "用户名"
    },
    {
      "name": "email",
      "type": "string",
      "doc": "邮箱"
    },
    {
      "name": "age",
      "type": ["null", "int"],
      "default": null,
      "doc": "年龄"
    },
    {
      "name": "created_at",
      "type": "string",
      "doc": "创建时间"
    }
  ]
}
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - contract.name
    - contract.description
    - contract.version
    - contract.service
    - contract.interface
    - contract.request
    - contract.response
  
  type_constraints:
    - field: "contract.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "contract.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "contract.request.method"
      type: "string"
      enum: ["GET", "POST", "PUT", "DELETE", "PATCH"]
```

### 6.2 契约验证规则

```yaml
contract_validation:
  schema_consistency:
    - rule: "all required fields must be defined in schema"
    - rule: "field types must be valid"
    - rule: "enum values must be consistent"
  
  compatibility_validation:
    - rule: "backward compatibility must be maintained"
    - rule: "breaking changes must be documented"
    - rule: "version numbers must follow semantic versioning"
  
  testing_validation:
    - rule: "test cases must cover all scenarios"
    - rule: "expected responses must match schema"
    - rule: "error cases must be tested"
```

## 7. 最佳实践

### 7.1 契约设计模式

```dsl
# RESTful API契约模式
contract "restful_api_contract" {
  description: "RESTful API契约"
  version: "1.0.0"
  service: "api-service"
  interface: "resource"
  
  request: {
    method: "GET"
    path: "/resources/{id}"
    headers: [
      {
        name: "Authorization"
        type: "string"
        required: true
      }
    ]
    parameters: [
      {
        name: "id"
        type: "string"
        location: "path"
        required: true
      }
    ]
  }
  
  response: {
    status: 200
    body: {
      type: "object"
      properties: {
        id: { type: "string" }
        name: { type: "string" }
        created_at: { type: "string", format: "date-time" }
      }
    }
  }
  
  compatibility: {
    backward_compatible: true
    compatible_versions: ["0.9.0"]
  }
}

# 事件契约模式
contract "event_contract" {
  description: "事件契约"
  version: "1.0.0"
  service: "event-service"
  interface: "publishEvent"
  
  request: {
    method: "POST"
    path: "/events"
    body: {
      type: "object"
      required: ["event_type", "data"]
      properties: {
        event_type: { type: "string" }
        data: { type: "object" }
        metadata: { type: "object" }
      }
    }
  }
  
  response: {
    status: 202
    body: {
      type: "object"
      properties: {
        event_id: { type: "string" }
        status: { type: "string" }
      }
    }
  }
}
```

### 7.2 契约命名规范

```dsl
# 推荐命名模式
contract "service_interface_version" {
  # 服务_接口_版本
}

contract "domain_operation_version" {
  # 领域_操作_版本
}

contract "version_service_interface" {
  # 版本_服务_接口
}
```

## 8. 与主流标准的映射

| DSL元素 | OpenAPI | Pact | Avro | GraphQL | gRPC |
|---------|---------|------|------|---------|------|
| contract | info | consumer/provider | schema | schema | service |
| request | requestBody | request | - | input | request |
| response | responses | response | - | type | response |
| schema | schemas | - | fields | type | message |
| validation | - | - | - | - | - |

## 9. 工程实践示例

```dsl
# 生产环境用户服务契约示例
contract "production_user_service_v1" {
  description: "生产环境用户服务契约V1"
  version: "1.0.0"
  author: "system"
  
  service: "user-service"
  interface: "getUser"
  
  request: {
    method: "GET"
    path: "/users/{id}"
    headers: [
      {
        name: "Authorization"
        type: "string"
        required: true
        description: "Bearer token"
      },
      {
        name: "X-Request-ID"
        type: "string"
        required: false
        description: "请求ID，用于追踪"
      }
    ]
    parameters: [
      {
        name: "id"
        type: "string"
        location: "path"
        required: true
        description: "用户ID"
        format: "uuid"
      },
      {
        name: "fields"
        type: "string"
        location: "query"
        required: false
        description: "返回字段，逗号分隔"
        pattern: "^[a-zA-Z_,]+$"
      }
    ]
    body: null
  }
  
  response: {
    status: 200
    headers: [
      {
        name: "Content-Type"
        value: "application/json"
      },
      {
        name: "X-Response-Time"
        value: "{{response_time}}"
      }
    ]
    body: {
      type: "object"
      properties: {
        id: { type: "string", format: "uuid" }
        name: { type: "string", min_length: 1, max_length: 100 }
        email: { type: "string", format: "email" }
        age: { type: "integer", minimum: 0, maximum: 150 }
        phone: { type: "string", pattern: "^\\+?[1-9]\\d{1,14}$" }
        address: {
          type: "object"
          properties: {
            street: { type: "string" }
            city: { type: "string" }
            state: { type: "string" }
            zip_code: { type: "string" }
            country: { type: "string" }
          }
        }
        preferences: {
          type: "object"
          properties: {
            language: { type: "string", enum: ["en", "zh", "es"] }
            timezone: { type: "string" }
            notifications: {
              type: "object"
              properties: {
                email: { type: "boolean" }
                sms: { type: "boolean" }
                push: { type: "boolean" }
              }
            }
          }
        }
        created_at: { type: "string", format: "date-time" }
        updated_at: { type: "string", format: "date-time" }
        metadata: {
          type: "object"
          additional_properties: true
        }
      }
      required: ["id", "name", "email", "created_at"]
    }
  }
  
  error_responses: [
    {
      status: 400
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          code: { type: "string" }
          details: {
            type: "array"
            items: {
              type: "object"
              properties: {
                field: { type: "string" }
                message: { type: "string" }
                code: { type: "string" }
              }
            }
          }
        }
        required: ["error", "message"]
      }
    },
    {
      status: 401
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          code: { type: "string" }
        }
        required: ["error", "message"]
      }
    },
    {
      status: 403
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          code: { type: "string" }
        }
        required: ["error", "message"]
      }
    },
    {
      status: 404
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          code: { type: "string" }
        }
        required: ["error", "message"]
      }
    },
    {
      status: 429
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          retry_after: { type: "integer" }
        }
        required: ["error", "message"]
      }
    },
    {
      status: 500
      body: {
        type: "object"
        properties: {
          error: { type: "string" }
          message: { type: "string" }
          code: { type: "string" }
          request_id: { type: "string" }
        }
        required: ["error", "message"]
      }
    }
  ]
  
  compatibility: {
    backward_compatible: true
    compatible_versions: ["0.9.0", "0.9.1"]
    breaking_changes: []
    deprecation_notice: null
    migration_guide: null
  }
  
  validation: {
    enabled: true
    rules: [
      {
        name: "user_id_format"
        condition: "id matches UUID pattern"
        error_message: "用户ID必须是有效的UUID格式"
      },
      {
        name: "email_format"
        condition: "email matches email pattern"
        error_message: "邮箱格式不正确"
      },
      {
        name: "phone_format"
        condition: "phone matches phone pattern"
        error_message: "电话号码格式不正确"
      },
      {
        name: "age_range"
        condition: "age >= 0 AND age <= 150"
        error_message: "年龄必须在0-150之间"
      }
    ]
  }
  
  testing: {
    enabled: true
    test_cases: [
      {
        name: "get_existing_user"
        request: {
          id: "123e4567-e89b-12d3-a456-426614174000"
        }
        expected_response: {
          status: 200
          body: {
            id: "123e4567-e89b-12d3-a456-426614174000"
            name: "John Doe"
            email: "john@example.com"
            age: 30
            created_at: "{{timestamp}}"
          }
        }
      },
      {
        name: "get_nonexistent_user"
        request: {
          id: "00000000-0000-0000-0000-000000000000"
        }
        expected_response: {
          status: 404
          body: {
            error: "not_found"
            message: "User not found"
            code: "USER_NOT_FOUND"
          }
        }
      },
      {
        name: "get_user_with_fields"
        request: {
          id: "123e4567-e89b-12d3-a456-426614174000"
          fields: "name,email"
        }
        expected_response: {
          status: 200
          body: {
            name: "John Doe"
            email: "john@example.com"
          }
        }
      }
    ]
  }
  
  documentation: {
    summary: "获取用户信息"
    description: "根据用户ID获取用户的详细信息，支持字段过滤"
    examples: [
      {
        name: "基本用法"
        request: "GET /users/123e4567-e89b-12d3-a456-426614174000"
        response: {
          status: 200
          body: {
            "id": "123e4567-e89b-12d3-a456-426614174000",
            "name": "John Doe",
            "email": "john@example.com",
            "age": 30,
            "created_at": "2024-01-15T10:30:00Z"
          }
        }
      },
      {
        name: "字段过滤"
        request: "GET /users/123e4567-e89b-12d3-a456-426614174000?fields=name,email"
        response: {
          status: 200
          body: {
            "name": "John Doe",
            "email": "john@example.com"
          }
        }
      }
    ]
  }
  
  monitoring: {
    metrics: [
      "request_count",
      "response_time",
      "error_rate",
      "throughput",
      "cache_hit_rate"
    ]
    alerts: [
      {
        name: "high_error_rate"
        condition: "error_rate > 5%"
        duration: "5m"
        severity: "critical"
      },
      {
        name: "high_response_time"
        condition: "response_time > 1s"
        duration: "5m"
        severity: "warning"
      },
      {
        name: "high_throughput"
        condition: "throughput > 1000/min"
        duration: "5m"
        severity: "info"
      }
    ]
    tracing: {
      enabled: true
      provider: "jaeger"
      sampling_rate: 0.1
    }
  }
  
  security: {
    authentication: {
      required: true
      type: "bearer_token"
      scopes: ["read:users"]
    }
    authorization: {
      required: true
      rules: [
        {
          condition: "user can read user data"
          resource: "user"
          action: "read"
        }
      ]
    }
    rate_limiting: {
      enabled: true
      requests_per_minute: 100
      burst_limit: 20
    }
  }
}
```

这个DSL设计为契约建模提供了完整的配置语言，支持RESTful API、事件、命令等多种契约类型，同时保持了良好的可扩展性和可维护性。
