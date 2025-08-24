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

## 5. 扩展语法特性

### 5.1 索引与性能优化

```dsl
entity Order {
  id: int primary key auto_increment
  user_id: int references User(id) index
  order_no: string unique index
  status: string index
  created_at: datetime default now index
  total_amount: decimal(10,2)
  
  # 复合索引
  index idx_user_status (user_id, status)
  index idx_created_status (created_at, status)
}
```

### 5.2 约束与验证规则

```dsl
entity Product {
  id: int primary key auto_increment
  name: string not null
  price: decimal(10,2) check (price >= 0)
  stock: int check (stock >= 0)
  category: string check (category in ('electronics', 'clothing', 'books'))
  sku: string unique not null pattern: "^[A-Z]{2}[0-9]{6}$"
}
```

### 5.3 触发器与存储过程

```dsl
entity Inventory {
  id: int primary key auto_increment
  product_id: int references Product(id)
  quantity: int
  updated_at: datetime default now
  
  trigger before_update {
    action: "SET updated_at = NOW()"
  }
  
  trigger after_insert {
    action: "UPDATE Product SET stock = stock + NEW.quantity WHERE id = NEW.product_id"
  }
}
```

### 5.4 视图与物化视图

```dsl
view UserOrderSummary {
  select: "u.name, COUNT(o.id) as order_count, SUM(o.total_amount) as total_spent"
  from: "User u LEFT JOIN Order o ON u.id = o.user_id"
  group_by: "u.id, u.name"
}

materialized_view ProductSalesSummary {
  select: "p.name, SUM(oi.quantity) as total_sold, SUM(oi.quantity * oi.price) as revenue"
  from: "Product p JOIN OrderItem oi ON p.id = oi.product_id"
  group_by: "p.id, p.name"
  refresh: "daily"
}
```

### 5.5 分区与分表策略

```dsl
entity LogEntry {
  id: int primary key auto_increment
  level: string
  message: text
  created_at: datetime default now
  
  partition by: "RANGE (YEAR(created_at))" {
    partition p2023: "VALUES LESS THAN (2024)"
    partition p2024: "VALUES LESS THAN (2025)"
    partition p2025: "VALUES LESS THAN (2026)"
  }
}
```

## 6. 代码生成模板

### 6.1 SQL DDL生成

```sql
-- 生成的MySQL DDL示例
CREATE TABLE `User` (
  `id` int NOT NULL AUTO_INCREMENT,
  `name` varchar(255) NOT NULL,
  `email` varchar(255) UNIQUE NOT NULL,
  `age` int DEFAULT NULL,
  `created_at` datetime DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (`id`),
  UNIQUE KEY `uk_email` (`email`),
  INDEX `idx_created_at` (`created_at`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

CREATE TABLE `Post` (
  `id` int NOT NULL AUTO_INCREMENT,
  `title` varchar(255) NOT NULL,
  `content` text,
  `author_id` int NOT NULL,
  PRIMARY KEY (`id`),
  FOREIGN KEY (`author_id`) REFERENCES `User`(`id`) ON DELETE CASCADE
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;
```

### 6.2 TypeORM模型生成

```typescript
// 生成的TypeORM实体示例
import { Entity, PrimaryGeneratedColumn, Column, CreateDateColumn, OneToMany, ManyToOne } from "typeorm";

@Entity()
export class User {
  @PrimaryGeneratedColumn()
  id: number;

  @Column({ type: "varchar", length: 255, nullable: false })
  name: string;

  @Column({ type: "varchar", length: 255, unique: true, nullable: false })
  email: string;

  @Column({ type: "int", nullable: true })
  age: number;

  @CreateDateColumn()
  created_at: Date;

  @OneToMany(() => Post, post => post.author)
  posts: Post[];
}

@Entity()
export class Post {
  @PrimaryGeneratedColumn()
  id: number;

  @Column({ type: "varchar", length: 255, nullable: false })
  title: string;

  @Column({ type: "text", nullable: true })
  content: string;

  @ManyToOne(() => User, user => user.posts, { onDelete: "CASCADE" })
  author: User;
}
```

### 6.3 Prisma Schema生成

```prisma
// 生成的Prisma Schema示例
model User {
  id        Int      @id @default(autoincrement())
  name      String
  email     String   @unique
  age       Int?
  created_at DateTime @default(now())
  posts     Post[]
}

model Post {
  id        Int      @id @default(autoincrement())
  title     String
  content   String?
  author    User     @relation(fields: [author_id], references: [id], onDelete: Cascade)
  author_id Int
}
```

### 6.4 GraphQL Schema生成

```graphql
# 生成的GraphQL Schema示例
type User {
  id: ID!
  name: String!
  email: String!
  age: Int
  created_at: DateTime!
  posts: [Post!]!
}

type Post {
  id: ID!
  title: String!
  content: String
  author: User!
  author_id: ID!
}

type Query {
  users: [User!]!
  user(id: ID!): User
  posts: [Post!]!
  post(id: ID!): Post
}

type Mutation {
  createUser(input: CreateUserInput!): User!
  updateUser(id: ID!, input: UpdateUserInput!): User!
  deleteUser(id: ID!): Boolean!
}
```

## 7. 验证规则与约束

### 7.1 语法验证规则

```yaml
validation:
  required_fields:
    - entity.name
    - entity.attributes[].name
    - entity.attributes[].type
  
  type_constraints:
    - field: "entity.attributes[].type"
      allowed_values: ["int", "string", "float", "datetime", "text", "boolean", "decimal"]
    - field: "entity.attributes[].constraints[]"
      allowed_values: ["primary key", "unique", "not null", "auto_increment", "default"]
  
  business_rules:
    - rule: "Primary key must be unique across all entities"
    - rule: "Foreign key references must exist"
    - rule: "Unique constraints must have unique field names"
    - rule: "Default values must match field type"
```

### 7.2 性能约束

```yaml
performance:
  max_attributes_per_entity: 50
  max_entities_per_model: 100
  max_indexes_per_entity: 10
  max_foreign_keys_per_entity: 20
  
  optimization:
    auto_index_foreign_keys: true
    auto_index_unique_fields: true
    suggest_composite_indexes: true
    analyze_query_patterns: true
```

## 8. 最佳实践与设计模式

### 8.1 实体设计模式

```dsl
# 软删除模式
entity BaseEntity {
  id: int primary key auto_increment
  created_at: datetime default now
  updated_at: datetime default now on update now
  deleted_at: datetime nullable
}

entity User extends BaseEntity {
  name: string not null
  email: string unique
}

# 审计模式
entity AuditableEntity {
  id: int primary key auto_increment
  created_by: int references User(id)
  created_at: datetime default now
  updated_by: int references User(id)
  updated_at: datetime default now on update now
  version: int default 1
}

# 多租户模式
entity TenantEntity {
  id: int primary key auto_increment
  tenant_id: int references Tenant(id) not null
  created_at: datetime default now
}
```

### 8.2 关系设计模式

```dsl
# 一对多关系
entity Department {
  id: int primary key auto_increment
  name: string
  employees: one_to_many Employee
}

entity Employee {
  id: int primary key auto_increment
  name: string
  department_id: int references Department(id)
}

# 多对多关系
entity Student {
  id: int primary key auto_increment
  name: string
  enrollments: many_to_many Course through Enrollment
}

entity Course {
  id: int primary key auto_increment
  title: string
  enrollments: many_to_many Student through Enrollment
}

entity Enrollment {
  id: int primary key auto_increment
  student_id: int references Student(id)
  course_id: int references Course(id)
  enrolled_at: datetime default now
  grade: string nullable
}
```

## 9. 工具链集成

### 9.1 开发工具

- **DSL编辑器**: 语法高亮、自动补全、错误提示
- **实体预览**: 实时预览生成的数据库结构
- **关系图生成**: 自动生成ER图和关系图
- **代码生成**: 一键生成多平台代码

### 9.2 构建工具

- **编译检查**: 编译时检查实体定义的正确性
- **代码优化**: 自动优化生成的代码结构
- **依赖分析**: 分析实体间的依赖关系
- **变更影响**: 分析实体变更的影响范围

### 9.3 监控工具

- **性能监控**: 监控实体查询性能
- **关系监控**: 监控实体关系的完整性
- **变更追踪**: 追踪实体结构的变更历史
- **使用统计**: 统计实体的使用情况

## 10. 与主流标准的映射

| DSL元素 | SQL | TypeORM | Prisma | GraphQL |
|---------|-----|---------|--------|---------|
| entity | CREATE TABLE | @Entity() | model | type |
| primary key | PRIMARY KEY | @PrimaryGeneratedColumn() | @id | ID! |
| unique | UNIQUE | @Column({unique: true}) | @unique | unique constraint |
| foreign key | FOREIGN KEY | @ManyToOne() | @relation | relation field |
| index | INDEX | @Index() | @@index | index directive |

## 11. 递归扩展建议

- 支持复杂关系、多对多、继承、聚合、组合、数据填充、数据脱敏
- 支持AI自动生成与优化实体结构
- 支持多数据库、分布式实体、变更影响分析
- 支持实体安全、权限、审计、数据脱敏
- 支持实体性能分析、缓存与自动维护

## 12. 工程实践示例

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

这个DSL设计为实体建模提供了完整的配置语言，支持从简单的实体定义到复杂的业务模型的各种需求，同时保持了良好的可扩展性和可维护性。
