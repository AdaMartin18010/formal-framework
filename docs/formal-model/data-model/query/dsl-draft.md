# 查询建模DSL草案

## 1. 设计目标

- 用统一DSL描述SQL、NoSQL、GraphQL等查询要素。
- 支持自动生成SQL语句、NoSQL查询、GraphQL请求等。

## 2. 基本语法结构

```dsl
query GetUserById {
  select: [id, name, email]
  from: User
  where: { id = $id }
}

query ListOrders {
  select: [id, product_id, quantity]
  from: Order
  where: { quantity > 1 }
  order_by: id desc
  limit: 10
}

query UserStats {
  select: [count(*), avg(age)]
  from: User
  where: { age > 18 }
  group_by: []
}
```

## 3. 关键元素

- query：查询定义
- select/from/where/order_by/group_by/limit：常用查询字段
- 参数化：$变量

## 4. 示例

```dsl
query SearchProduct {
  select: [id, name, price]
  from: Product
  where: { price > $minPrice }
  order_by: price asc
  limit: 20
}

query UserByEmail {
  select: [id, name]
  from: User
  where: { email = $email }
}
```

## 5. 与主流标准的映射

- 可自动转换为SQL、MongoDB、Elasticsearch、GraphQL等查询
- 支持与ORM、API层集成

## 6. 递归扩展建议

- 支持复杂嵌套查询、子查询、联合查询
- 支持查询权限、审计与安全校验
