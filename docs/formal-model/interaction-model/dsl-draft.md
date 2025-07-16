# 交互模型DSL草案

## 1. 设计目标

- 用统一DSL描述API、协议、消息、契约等交互要素。
- 支持自动生成OpenAPI、gRPC proto等主流标准。

## 2. 基本语法结构

```dsl
service UserService {
  endpoint getUser {
    method: GET
    path: /user/{id}
    request: {
      id: string
    }
    response: {
      name: string
      age: int
    }
    error: {
      code: int
      message: string
    }
  }
}
```

## 3. 关键元素

- service：服务定义
- endpoint：接口定义
- method/path：HTTP方法与路径
- request/response/error：请求、响应、错误结构
- contract：契约声明（可选）

## 4. 示例

```dsl
service OrderService {
  endpoint createOrder {
    method: POST
    path: /order
    request: {
      productId: string
      quantity: int
    }
    response: {
      orderId: string
      status: string
    }
  }
}
```

## 5. 与主流标准的映射

- 可自动转换为OpenAPI、gRPC proto、AsyncAPI等格式。
- 支持扩展协议字段（如WebSocket、GraphQL等）。

## 6. 递归扩展建议

- 支持消息流、事件订阅等异步交互
- 支持契约版本与兼容性声明
- 支持安全、认证、限流等元数据
