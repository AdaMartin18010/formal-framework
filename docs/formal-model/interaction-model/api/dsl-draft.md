# API建模DSL草案

## 1. 设计目标

- 用统一DSL描述RESTful、GraphQL、gRPC等API接口。
- 支持自动生成OpenAPI、GraphQL SDL、gRPC proto等主流标准。

## 2. 基本语法结构

```dsl
api UserAPI {
  endpoint getUser {
    method: GET
    path: /user/{id}
    params: {
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

- api：API分组
- endpoint：接口定义
- method/path/params/response/error：常用API字段
- auth：认证声明（可选）
- version：版本声明（可选）

## 4. 示例

```dsl
api ProductAPI {
  endpoint listProducts {
    method: GET
    path: /products
    response: [
      { id: string, name: string, price: float }
    ]
  }
  endpoint createProduct {
    method: POST
    path: /products
    request: {
      name: string
      price: float
    }
    response: {
      id: string
      name: string
      price: float
    }
  }
}
```

## 5. 与主流标准的映射

- 可自动转换为OpenAPI、GraphQL SDL、gRPC proto等格式
- 支持与主流API网关、文档工具集成

## 6. 递归扩展建议

- 支持多协议（REST/gRPC/GraphQL）混合建模
- 支持API版本、认证、安全策略等高级特性
