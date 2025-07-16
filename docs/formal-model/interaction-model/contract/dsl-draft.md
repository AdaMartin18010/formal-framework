# 契约建模DSL草案

## 1. 设计目标

- 用统一DSL描述接口、数据、行为等契约要素。
- 支持自动生成OpenAPI、Pact、Avro Schema等主流契约文档与测试。

## 2. 基本语法结构

```dsl
contract UserServiceV1 {
  version: "1.0.0"
  interface: getUser
  request: {
    id: string
  }
  response: {
    name: string
    age: int
  }
  compatible_with: ["0.9.0"]
}

contract OrderServiceV2 {
  version: "2.0.0"
  interface: createOrder
  request: {
    productId: string
    quantity: int
  }
  response: {
    orderId: string
    status: string
  }
  compatible_with: ["1.0.0", "1.1.0"]
}
```

## 3. 关键元素

- contract：契约声明
- version/interface/request/response：契约核心字段
- compatible_with：兼容版本声明
- test/mock：契约测试与Mock（可扩展）

## 4. 示例

```dsl
contract PaymentServiceV1 {
  version: "1.0.0"
  interface: pay
  request: {
    orderId: string
    amount: float
  }
  response: {
    result: string
  }
  compatible_with: ["0.9.0"]
}

contract UserServiceV2 {
  version: "2.0.0"
  interface: getUser
  request: {
    id: string
  }
  response: {
    name: string
    age: int
    email: string
  }
  compatible_with: ["1.0.0", "1.1.0"]
}
```

## 5. 与主流标准的映射

- 可自动转换为OpenAPI、Pact、Avro Schema等契约文档与测试
- 支持与主流契约测试、Mock工具集成

## 6. 递归扩展建议

- 支持契约变更检测、兼容性校验
- 支持契约驱动开发（CDC）与自动化回归测试
