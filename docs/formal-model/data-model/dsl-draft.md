# 数据模型DSL草案

## 1. 设计目标

- 用统一DSL描述实体、属性、关系、索引、迁移等数据要素。
- 支持自动生成SQL DDL、ORM模型、迁移脚本等。

## 2. 基本语法结构

```dsl
entity User {
  id: int primary key auto_increment
  name: string not null
  email: string unique
  age: int
  created_at: datetime default now
}

entity Post {
  id: int primary key auto_increment
  title: string not null
  content: text
  author_id: int references User(id)
}

index idx_user_email on User(email)
```

## 3. 关键元素

- entity：实体/表定义
- 属性：字段名、类型、约束
- 关系：references、外键
- index：索引定义
- migration：迁移操作（可扩展）

## 4. 示例

```dsl
entity Product {
  id: int primary key
  name: string
  price: float
}

entity Order {
  id: int primary key
  product_id: int references Product(id)
  quantity: int
}
```

## 5. 与主流标准的映射

- 可自动转换为PostgreSQL/MySQL/SQLite等SQL DDL
- 可生成ORM模型（如Prisma、TypeORM等）
- 支持ER图导出

## 6. 递归扩展建议

- 支持复杂关系（多对多、继承等）
- 支持迁移脚本自动生成
- 支持数据填充与校验规则
