# 实体建模DSL草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述实体、属性、主键、约束、关系、继承、聚合、数据填充等要素，支持递归组合。
- 支持自动生成SQL DDL、ORM模型、ER图、数据填充脚本等。
- 支持权限、安全、审计、AI自动化等高级特性。

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
```

## 3. 关键元素

- entity：实体/表定义
- 属性：字段名、类型、约束、默认值
- references：外键/关联
- unique/primary key：唯一约束、主键
- extends/implements：继承与接口
- aggregate/compose：聚合与组合
- seed_data：数据填充
- permission/audit：权限与审计

## 4. 高级用法与递归扩展

### 4.1 复杂关系与多对多

```dsl
entity Student {
  id: int primary key auto_increment
  name: string
  courses: many_to_many Course
}

entity Course {
  id: int primary key auto_increment
  title: string
  students: many_to_many Student
}
```

### 4.2 继承与聚合

```dsl
entity Person {
  id: int primary key auto_increment
  name: string
}

entity Employee extends Person {
  employee_no: string unique
  department: string
}

entity Department {
  id: int primary key auto_increment
  name: string
  employees: aggregate Employee
}
```

### 4.3 数据填充与默认值

```dsl
entity Product {
  id: int primary key
  name: string
  price: float default 0.0
}

seed_data Product [
  { name: "商品A", price: 100 },
  { name: "商品B", price: 200 }
]
```

### 4.4 权限与安全声明

```dsl
entity User {
  id: int primary key auto_increment
  name: string
  email: string unique
  ssn: string permission: "security_audit" audit: true
}
```

### 4.5 AI自动化与智能实体建模

```dsl
# 支持AI自动生成实体结构
ai_entity "为电商系统自动生成订单、商品、用户等实体及关系" {
  domain: "ecommerce"
  optimize: true
}
```

## 5. 与主流标准的映射

- 可自动转换为PostgreSQL/MySQL/SQLite等SQL DDL
- 可生成ORM模型（如Prisma、TypeORM等）、ER图、数据填充脚本
- 支持权限、安全、审计策略自动生成

## 6. 递归扩展建议

- 支持复杂关系、多对多、继承、聚合、组合、数据填充、数据脱敏
- 支持AI自动生成与优化实体结构
- 支持多数据库、分布式实体、变更影响分析
- 支持实体安全、权限、审计、数据脱敏
- 支持实体性能分析、缓存与自动维护

## 7. 工程实践示例

```dsl
entity Log {
  id: int primary key auto_increment
  level: string
  message: text
  user_id: int references User(id)
  created_at: datetime default now
}

entity Address {
  id: int primary key auto_increment
  user_id: int references User(id)
  city: string
  detail: string
}

entity User {
  id: int primary key auto_increment
  name: string
  email: string unique
  addresses: one_to_many Address
}
```

---
