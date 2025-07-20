# 索引建模DSL草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述单列、多列、唯一、全文、空间、动态等索引要素，支持递归组合。
- 支持自动生成SQL索引DDL、优化建议、变更脚本、冗余检测等。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 基本语法结构

```dsl
index idx_user_email on User(email) unique
index idx_order_product on Order(product_id, quantity)
index idx_post_content on Post USING fulltext(content)
index idx_location on Place USING spatial(longitude, latitude)
```

## 3. 关键元素

- index：索引声明
- on：目标表与字段
- unique：唯一性
- USING：索引类型（fulltext/spatial/hash等）
- dynamic：动态索引声明
- permission/audit：权限与审计

## 4. 高级用法与递归扩展

### 4.1 多级与组合索引

```dsl
index idx_user_email_name on User(email, name) unique
index idx_order_time_status on Order(product_id, created_at, status)
```

### 4.2 动态与表达式索引

```dsl
index idx_user_active on User USING btree(active = true)
index idx_order_total on Order USING hash(total_amount * quantity)
```

### 4.3 冗余检测与优化建议

```dsl
index idx_user_email on User(email) unique
index idx_user_email_name on User(email, name)
# 系统自动检测idx_user_email为idx_user_email_name的前缀，建议合并或优化
```

### 4.4 权限与安全声明

```dsl
index idx_sensitive_data on User(ssn) permission: "security_audit" audit: true
```

### 4.5 AI自动化与智能索引建议

```dsl
# 支持AI自动推荐索引
ai_index "为Order表高频查询自动推荐最优索引" {
  target: Order
  query_pattern: "where product_id=? and created_at>?"
  optimize: true
}
```

## 5. 与主流标准的映射

- 可自动转换为PostgreSQL/MySQL/SQLite等索引DDL
- 可生成ORM模型索引声明、变更脚本、优化建议
- 支持权限、安全、审计策略自动生成

## 6. 递归扩展建议

- 支持多级索引、动态索引、表达式索引、冗余检测、索引重建
- 支持AI自动推荐与优化索引
- 支持多数据库、分布式索引、变更影响分析
- 支持索引安全、权限、审计、数据脱敏
- 支持索引性能分析、缓存与自动维护

## 7. 工程实践示例

```dsl
index idx_log_search on Log(level, timestamp, user_id) USING btree
index idx_geo_location on Place USING spatial(longitude, latitude)
index idx_fulltext_desc on Product USING fulltext(description)
index idx_sensitive_user on User(ssn) permission: "security_audit" audit: true
```

---
