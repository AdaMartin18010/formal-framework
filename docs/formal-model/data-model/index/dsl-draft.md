# 索引建模DSL草案

## 1. 设计目标

- 用统一DSL描述单列、多列、唯一、全文、空间等索引要素。
- 支持自动生成SQL索引DDL、优化建议、变更脚本等。

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

## 4. 常用索引声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| index idx_user_email on User(email) unique    | 唯一索引       |
| index idx_order_product on Order(product_id, quantity) | 多列索引 |
| index idx_post_content on Post USING fulltext(content) | 全文索引 |
| index idx_location on Place USING spatial(longitude, latitude) | 空间索引 |

## 5. 与主流标准的映射

- 可自动转换为PostgreSQL/MySQL/SQLite等索引DDL
- 支持与ORM、数据库工具集成

## 6. 递归扩展建议

- 支持索引重建、失效检测、冗余分析
- 支持索引变更脚本自动生成
