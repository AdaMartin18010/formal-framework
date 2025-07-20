# 查询建模DSL草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述SQL、NoSQL、GraphQL等查询要素，支持递归嵌套、复杂组合。
- 支持自动生成SQL语句、NoSQL查询、GraphQL请求等，便于多数据源集成。
- 支持权限、审计、安全、AI自动化等高级特性。

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
- 嵌套/子查询：支持递归组合
- 权限/安全：可声明权限、审计规则

## 4. 高级用法与递归扩展

### 4.1 嵌套与子查询

```dsl
query OrdersWithUser {
  select: [id, product_id, quantity, user]
  from: Order
  where: { quantity > 1 }
  join: {
    user: {
      select: [id, name, email]
      from: User
      where: { id = Order.user_id }
    }
  }
}

query TopProducts {
  select: [product_id, count(*) as sales]
  from: Order
  group_by: [product_id]
  order_by: sales desc
  limit: 5
}
```

### 4.2 复杂条件与表达式

```dsl
query ActiveUsers {
  select: [id, name, last_login]
  from: User
  where: {
    and: [
      { status = "active" },
      { or: [ { last_login > $since }, { created_at > $since } ] }
    ]
  }
}
```

### 4.3 权限与安全声明

```dsl
query SensitiveData {
  select: [id, name, email, ssn]
  from: User
  where: { role = "admin" }
  permission: "admin_only"
  audit: true
}
```

### 4.4 AI自动化与自然语言查询

```dsl
# 支持AI自动生成查询
ai_query "查询所有近30天注册且未下单的用户" {
  target: User
  time_range: 30d
  filter: "未下单"
}
```

## 5. 与主流标准的映射

- 可自动转换为SQL、MongoDB、Elasticsearch、GraphQL等查询
- 支持与ORM、API层集成
- 支持权限、审计、安全策略自动生成

## 6. 递归扩展建议

- 支持复杂嵌套查询、子查询、联合查询、窗口函数、递归查询
- 支持查询权限、审计与安全校验
- 支持AI自动生成与优化查询
- 支持多数据源、分布式查询、数据脱敏
- 支持查询缓存、性能分析与优化建议

## 7. 工程实践示例

```dsl
query RecentHighValueOrders {
  select: [id, user_id, total_amount, created_at]
  from: Order
  where: {
    and: [
      { created_at > $lastMonth },
      { total_amount > 1000 }
    ]
  }
  order_by: created_at desc
  limit: 20
  permission: "finance_audit"
  audit: true
}
```

---
