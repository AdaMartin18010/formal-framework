# 数据模型DSL设计

## 设计目标

数据模型DSL旨在提供声明式语言定义复杂的数据模型配置，支持多种数据类型、关系定义、约束规则、索引策略，并与主流数据库平台无缝集成。

## 基本语法

### 核心结构

```dsl
data_model "ecommerce_system" {
  description: "电商系统数据模型"
  version: "1.0.0"
  
  namespace: "ecommerce"
  labels: {
    domain: "ecommerce"
    environment: "production"
    version: "1.0.0"
  }
  
  entities: [
    {
      name: "user"
      description: "用户实体"
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
        }
      ]
    }
  ]
  
  relationships: [
    {
      name: "user_orders"
      from: "user"
      to: "order"
      type: "one_to_many"
    }
  ]
}
```

### 实体定义

```dsl
entity "user" {
  description: "用户实体"
  
  fields: [
    {
      name: "id"
      type: "uuid"
      primary_key: true
      auto_generate: true
      description: "用户唯一标识"
    },
    {
      name: "username"
      type: "string"
      length: 50
      unique: true
      not_null: true
      description: "用户名"
    },
    {
      name: "email"
      type: "string"
      length: 100
      unique: true
      not_null: true
      validation: "email"
      description: "邮箱地址"
    },
    {
      name: "password_hash"
      type: "string"
      length: 255
      not_null: true
      description: "密码哈希"
    },
    {
      name: "first_name"
      type: "string"
      length: 50
      description: "名字"
    },
    {
      name: "last_name"
      type: "string"
      length: 50
      description: "姓氏"
    },
    {
      name: "phone"
      type: "string"
      length: 20
      validation: "phone"
      description: "电话号码"
    },
    {
      name: "status"
      type: "enum"
      values: ["active", "inactive", "suspended"]
      default: "active"
      description: "用户状态"
    },
    {
      name: "created_at"
      type: "timestamp"
      default: "now()"
      not_null: true
      description: "创建时间"
    },
    {
      name: "updated_at"
      type: "timestamp"
      default: "now()"
      on_update: "now()"
      not_null: true
      description: "更新时间"
    }
  ]
  
  indexes: [
    {
      name: "idx_user_email"
      fields: ["email"]
      type: "unique"
    },
    {
      name: "idx_user_username"
      fields: ["username"]
      type: "unique"
    },
    {
      name: "idx_user_status"
      fields: ["status"]
      type: "btree"
    },
    {
      name: "idx_user_created_at"
      fields: ["created_at"]
      type: "btree"
    }
  ]
  
  constraints: [
    {
      name: "chk_user_email_format"
      type: "check"
      expression: "email ~* '^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,}$'"
    },
    {
      name: "chk_user_phone_format"
      type: "check"
      expression: "phone ~* '^\\+?[1-9]\\d{1,14}$'"
    }
  ]
}
```

### 关系定义

```dsl
relationship "user_orders" {
  description: "用户订单关系"
  
  from: {
    entity: "user"
    field: "id"
  }
  
  to: {
    entity: "order"
    field: "user_id"
  }
  
  type: "one_to_many"
  
  constraints: [
    {
      name: "fk_order_user"
      type: "foreign_key"
      on_delete: "cascade"
      on_update: "cascade"
    }
  ]
  
  indexes: [
    {
      name: "idx_order_user_id"
      fields: ["user_id"]
      type: "btree"
    }
  ]
}

relationship "order_items" {
  description: "订单商品关系"
  
  from: {
    entity: "order"
    field: "id"
  }
  
  to: {
    entity: "order_item"
    field: "order_id"
  }
  
  type: "one_to_many"
  
  constraints: [
    {
      name: "fk_order_item_order"
      type: "foreign_key"
      on_delete: "cascade"
      on_update: "cascade"
    }
  ]
  
  indexes: [
    {
      name: "idx_order_item_order_id"
      fields: ["order_id"]
      type: "btree"
    }
  ]
}

relationship "product_category" {
  description: "商品分类关系"
  
  from: {
    entity: "product"
    field: "category_id"
  }
  
  to: {
    entity: "category"
    field: "id"
  }
  
  type: "many_to_one"
  
  constraints: [
    {
      name: "fk_product_category"
      type: "foreign_key"
      on_delete: "restrict"
      on_update: "cascade"
    }
  ]
  
  indexes: [
    {
      name: "idx_product_category_id"
      fields: ["category_id"]
      type: "btree"
    }
  ]
}
```

### 复杂实体

```dsl
entity "order" {
  description: "订单实体"
  
  fields: [
    {
      name: "id"
      type: "uuid"
      primary_key: true
      auto_generate: true
      description: "订单唯一标识"
    },
    {
      name: "user_id"
      type: "uuid"
      not_null: true
      description: "用户ID"
    },
    {
      name: "order_number"
      type: "string"
      length: 20
      unique: true
      not_null: true
      description: "订单号"
    },
    {
      name: "status"
      type: "enum"
      values: ["pending", "confirmed", "processing", "shipped", "delivered", "cancelled"]
      default: "pending"
      not_null: true
      description: "订单状态"
    },
    {
      name: "total_amount"
      type: "decimal"
      precision: 10
      scale: 2
      not_null: true
      default: 0.00
      description: "订单总金额"
    },
    {
      name: "currency"
      type: "string"
      length: 3
      default: "USD"
      not_null: true
      description: "货币类型"
    },
    {
      name: "shipping_address"
      type: "json"
      description: "收货地址"
    },
    {
      name: "billing_address"
      type: "json"
      description: "账单地址"
    },
    {
      name: "payment_method"
      type: "string"
      length: 50
      description: "支付方式"
    },
    {
      name: "payment_status"
      type: "enum"
      values: ["pending", "paid", "failed", "refunded"]
      default: "pending"
      description: "支付状态"
    },
    {
      name: "notes"
      type: "text"
      description: "订单备注"
    },
    {
      name: "created_at"
      type: "timestamp"
      default: "now()"
      not_null: true
      description: "创建时间"
    },
    {
      name: "updated_at"
      type: "timestamp"
      default: "now()"
      on_update: "now()"
      not_null: true
      description: "更新时间"
    }
  ]
  
  indexes: [
    {
      name: "idx_order_user_id"
      fields: ["user_id"]
      type: "btree"
    },
    {
      name: "idx_order_status"
      fields: ["status"]
      type: "btree"
    },
    {
      name: "idx_order_created_at"
      fields: ["created_at"]
      type: "btree"
    },
    {
      name: "idx_order_payment_status"
      fields: ["payment_status"]
      type: "btree"
    },
    {
      name: "idx_order_number"
      fields: ["order_number"]
      type: "unique"
    }
  ]
  
  constraints: [
    {
      name: "chk_order_total_amount"
      type: "check"
      expression: "total_amount >= 0"
    },
    {
      name: "chk_order_currency"
      type: "check"
      expression: "currency IN ('USD', 'EUR', 'GBP', 'JPY')"
    }
  ]
  
  computed_fields: [
    {
      name: "item_count"
      type: "integer"
      expression: "SELECT COUNT(*) FROM order_item WHERE order_id = id"
      description: "商品数量"
    },
    {
      name: "is_paid"
      type: "boolean"
      expression: "payment_status = 'paid'"
      description: "是否已支付"
    }
  ]
}
```

## 高级用法

### 继承关系

```dsl
entity "person" {
  description: "人员基类"
  
  fields: [
    {
      name: "id"
      type: "uuid"
      primary_key: true
      auto_generate: true
    },
    {
      name: "first_name"
      type: "string"
      length: 50
      not_null: true
    },
    {
      name: "last_name"
      type: "string"
      length: 50
      not_null: true
    },
    {
      name: "email"
      type: "string"
      length: 100
      unique: true
      not_null: true
    },
    {
      name: "phone"
      type: "string"
      length: 20
    },
    {
      name: "created_at"
      type: "timestamp"
      default: "now()"
      not_null: true
    }
  ]
  
  abstract: true
}

entity "customer" {
  description: "客户实体"
  
  extends: "person"
  
  fields: [
    {
      name: "customer_number"
      type: "string"
      length: 20
      unique: true
      not_null: true
    },
    {
      name: "membership_level"
      type: "enum"
      values: ["bronze", "silver", "gold", "platinum"]
      default: "bronze"
    },
    {
      name: "total_spent"
      type: "decimal"
      precision: 10
      scale: 2
      default: 0.00
    }
  ]
  
  indexes: [
    {
      name: "idx_customer_number"
      fields: ["customer_number"]
      type: "unique"
    },
    {
      name: "idx_customer_membership"
      fields: ["membership_level"]
      type: "btree"
    }
  ]
}

entity "employee" {
  description: "员工实体"
  
  extends: "person"
  
  fields: [
    {
      name: "employee_id"
      type: "string"
      length: 20
      unique: true
      not_null: true
    },
    {
      name: "department"
      type: "string"
      length: 50
      not_null: true
    },
    {
      name: "position"
      type: "string"
      length: 50
      not_null: true
    },
    {
      name: "hire_date"
      type: "date"
      not_null: true
    },
    {
      name: "salary"
      type: "decimal"
      precision: 10
      scale: 2
    }
  ]
  
  indexes: [
    {
      name: "idx_employee_id"
      fields: ["employee_id"]
      type: "unique"
    },
    {
      name: "idx_employee_department"
      fields: ["department"]
      type: "btree"
    }
  ]
}
```

### 多态关系

```dsl
entity "payment" {
  description: "支付基类"
  
  fields: [
    {
      name: "id"
      type: "uuid"
      primary_key: true
      auto_generate: true
    },
    {
      name: "order_id"
      type: "uuid"
      not_null: true
    },
    {
      name: "amount"
      type: "decimal"
      precision: 10
      scale: 2
      not_null: true
    },
    {
      name: "currency"
      type: "string"
      length: 3
      default: "USD"
      not_null: true
    },
    {
      name: "status"
      type: "enum"
      values: ["pending", "completed", "failed", "refunded"]
      default: "pending"
      not_null: true
    },
    {
      name: "payment_type"
      type: "string"
      length: 20
      not_null: true
    },
    {
      name: "created_at"
      type: "timestamp"
      default: "now()"
      not_null: true
    }
  ]
  
  abstract: true
  
  indexes: [
    {
      name: "idx_payment_order_id"
      fields: ["order_id"]
      type: "btree"
    },
    {
      name: "idx_payment_status"
      fields: ["status"]
      type: "btree"
    }
  ]
}

entity "credit_card_payment" {
  description: "信用卡支付"
  
  extends: "payment"
  
  fields: [
    {
      name: "card_last_four"
      type: "string"
      length: 4
      not_null: true
    },
    {
      name: "card_type"
      type: "string"
      length: 20
      not_null: true
    },
    {
      name: "transaction_id"
      type: "string"
      length: 50
      unique: true
    }
  ]
  
  constraints: [
    {
      name: "chk_credit_card_payment_type"
      type: "check"
      expression: "payment_type = 'credit_card'"
    }
  ]
}

entity "paypal_payment" {
  description: "PayPal支付"
  
  extends: "payment"
  
  fields: [
    {
      name: "paypal_email"
      type: "string"
      length: 100
      not_null: true
    },
    {
      name: "paypal_transaction_id"
      type: "string"
      length: 50
      unique: true
    }
  ]
  
  constraints: [
    {
      name: "chk_paypal_payment_type"
      type: "check"
      expression: "payment_type = 'paypal'"
    }
  ]
}
```

### 审计追踪

```dsl
entity "audit_log" {
  description: "审计日志"
  
  fields: [
    {
      name: "id"
      type: "uuid"
      primary_key: true
      auto_generate: true
    },
    {
      name: "table_name"
      type: "string"
      length: 50
      not_null: true
    },
    {
      name: "record_id"
      type: "uuid"
      not_null: true
    },
    {
      name: "operation"
      type: "enum"
      values: ["insert", "update", "delete"]
      not_null: true
    },
    {
      name: "old_values"
      type: "json"
      description: "修改前的值"
    },
    {
      name: "new_values"
      type: "json"
      description: "修改后的值"
    },
    {
      name: "changed_fields"
      type: "string[]"
      description: "修改的字段"
    },
    {
      name: "user_id"
      type: "uuid"
      description: "操作用户"
    },
    {
      name: "ip_address"
      type: "inet"
      description: "IP地址"
    },
    {
      name: "user_agent"
      type: "text"
      description: "用户代理"
    },
    {
      name: "created_at"
      type: "timestamp"
      default: "now()"
      not_null: true
    }
  ]
  
  indexes: [
    {
      name: "idx_audit_table_record"
      fields: ["table_name", "record_id"]
      type: "btree"
    },
    {
      name: "idx_audit_operation"
      fields: ["operation"]
      type: "btree"
    },
    {
      name: "idx_audit_user"
      fields: ["user_id"]
      type: "btree"
    },
    {
      name: "idx_audit_created_at"
      fields: ["created_at"]
      type: "btree"
    }
  ]
  
  partitioning: {
    type: "range"
    field: "created_at"
    interval: "month"
  }
}
```

## 代码生成模板

### SQL DDL

```sql
-- 生成的SQL DDL
-- 创建用户表
CREATE TABLE "user" (
    "id" UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    "username" VARCHAR(50) UNIQUE NOT NULL,
    "email" VARCHAR(100) UNIQUE NOT NULL,
    "password_hash" VARCHAR(255) NOT NULL,
    "first_name" VARCHAR(50),
    "last_name" VARCHAR(50),
    "phone" VARCHAR(20),
    "status" VARCHAR(20) DEFAULT 'active' CHECK (status IN ('active', 'inactive', 'suspended')),
    "created_at" TIMESTAMP DEFAULT NOW() NOT NULL,
    "updated_at" TIMESTAMP DEFAULT NOW() NOT NULL,
    CONSTRAINT "chk_user_email_format" CHECK (email ~* '^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,}$'),
    CONSTRAINT "chk_user_phone_format" CHECK (phone ~* '^\+?[1-9]\d{1,14}$')
);

-- 创建订单表
CREATE TABLE "order" (
    "id" UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    "user_id" UUID NOT NULL,
    "order_number" VARCHAR(20) UNIQUE NOT NULL,
    "status" VARCHAR(20) DEFAULT 'pending' NOT NULL CHECK (status IN ('pending', 'confirmed', 'processing', 'shipped', 'delivered', 'cancelled')),
    "total_amount" DECIMAL(10,2) DEFAULT 0.00 NOT NULL,
    "currency" VARCHAR(3) DEFAULT 'USD' NOT NULL,
    "shipping_address" JSONB,
    "billing_address" JSONB,
    "payment_method" VARCHAR(50),
    "payment_status" VARCHAR(20) DEFAULT 'pending' CHECK (payment_status IN ('pending', 'paid', 'failed', 'refunded')),
    "notes" TEXT,
    "created_at" TIMESTAMP DEFAULT NOW() NOT NULL,
    "updated_at" TIMESTAMP DEFAULT NOW() NOT NULL,
    CONSTRAINT "chk_order_total_amount" CHECK (total_amount >= 0),
    CONSTRAINT "chk_order_currency" CHECK (currency IN ('USD', 'EUR', 'GBP', 'JPY')),
    CONSTRAINT "fk_order_user" FOREIGN KEY ("user_id") REFERENCES "user"("id") ON DELETE CASCADE ON UPDATE CASCADE
);

-- 创建索引
CREATE UNIQUE INDEX "idx_user_email" ON "user"("email");
CREATE UNIQUE INDEX "idx_user_username" ON "user"("username");
CREATE INDEX "idx_user_status" ON "user"("status");
CREATE INDEX "idx_user_created_at" ON "user"("created_at");

CREATE INDEX "idx_order_user_id" ON "order"("user_id");
CREATE INDEX "idx_order_status" ON "order"("status");
CREATE INDEX "idx_order_created_at" ON "order"("created_at");
CREATE INDEX "idx_order_payment_status" ON "order"("payment_status");
CREATE UNIQUE INDEX "idx_order_number" ON "order"("order_number");

-- 创建触发器
CREATE OR REPLACE FUNCTION update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = NOW();
    RETURN NEW;
END;
$$ language 'plpgsql';

CREATE TRIGGER update_user_updated_at BEFORE UPDATE ON "user"
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_order_updated_at BEFORE UPDATE ON "order"
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

-- 创建审计日志表
CREATE TABLE "audit_log" (
    "id" UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    "table_name" VARCHAR(50) NOT NULL,
    "record_id" UUID NOT NULL,
    "operation" VARCHAR(20) NOT NULL CHECK (operation IN ('insert', 'update', 'delete')),
    "old_values" JSONB,
    "new_values" JSONB,
    "changed_fields" VARCHAR(50)[],
    "user_id" UUID,
    "ip_address" INET,
    "user_agent" TEXT,
    "created_at" TIMESTAMP DEFAULT NOW() NOT NULL
) PARTITION BY RANGE (created_at);

-- 创建分区
CREATE TABLE audit_log_2024_01 PARTITION OF audit_log
    FOR VALUES FROM ('2024-01-01') TO ('2024-02-01');

CREATE TABLE audit_log_2024_02 PARTITION OF audit_log
    FOR VALUES FROM ('2024-02-01') TO ('2024-03-01');

-- 创建审计日志索引
CREATE INDEX "idx_audit_table_record" ON "audit_log"("table_name", "record_id");
CREATE INDEX "idx_audit_operation" ON "audit_log"("operation");
CREATE INDEX "idx_audit_user" ON "audit_log"("user_id");
CREATE INDEX "idx_audit_created_at" ON "audit_log"("created_at");
```

### TypeScript类型定义

```typescript
// 生成的TypeScript类型定义
export interface User {
  id: string;
  username: string;
  email: string;
  passwordHash: string;
  firstName?: string;
  lastName?: string;
  phone?: string;
  status: 'active' | 'inactive' | 'suspended';
  createdAt: Date;
  updatedAt: Date;
}

export interface Order {
  id: string;
  userId: string;
  orderNumber: string;
  status: 'pending' | 'confirmed' | 'processing' | 'shipped' | 'delivered' | 'cancelled';
  totalAmount: number;
  currency: 'USD' | 'EUR' | 'GBP' | 'JPY';
  shippingAddress?: Address;
  billingAddress?: Address;
  paymentMethod?: string;
  paymentStatus: 'pending' | 'paid' | 'failed' | 'refunded';
  notes?: string;
  createdAt: Date;
  updatedAt: Date;
  // 关联数据
  user?: User;
  items?: OrderItem[];
}

export interface Address {
  street: string;
  city: string;
  state: string;
  zipCode: string;
  country: string;
}

export interface OrderItem {
  id: string;
  orderId: string;
  productId: string;
  quantity: number;
  unitPrice: number;
  totalPrice: number;
  // 关联数据
  order?: Order;
  product?: Product;
}

export interface Product {
  id: string;
  name: string;
  description?: string;
  price: number;
  currency: string;
  categoryId: string;
  stockQuantity: number;
  isActive: boolean;
  createdAt: Date;
  updatedAt: Date;
  // 关联数据
  category?: Category;
}

export interface Category {
  id: string;
  name: string;
  description?: string;
  parentId?: string;
  isActive: boolean;
  createdAt: Date;
  updatedAt: Date;
  // 关联数据
  parent?: Category;
  children?: Category[];
  products?: Product[];
}

export interface AuditLog {
  id: string;
  tableName: string;
  recordId: string;
  operation: 'insert' | 'update' | 'delete';
  oldValues?: Record<string, any>;
  newValues?: Record<string, any>;
  changedFields?: string[];
  userId?: string;
  ipAddress?: string;
  userAgent?: string;
  createdAt: Date;
}

// 创建类型
export type CreateUser = Omit<User, 'id' | 'createdAt' | 'updatedAt'>;
export type CreateOrder = Omit<Order, 'id' | 'createdAt' | 'updatedAt'>;
export type CreateProduct = Omit<Product, 'id' | 'createdAt' | 'updatedAt'>;

// 更新类型
export type UpdateUser = Partial<Omit<User, 'id' | 'createdAt' | 'updatedAt'>>;
export type UpdateOrder = Partial<Omit<Order, 'id' | 'createdAt' | 'updatedAt'>>;
export type UpdateProduct = Partial<Omit<Product, 'id' | 'createdAt' | 'updatedAt'>>;

// 查询类型
export interface UserQuery {
  id?: string;
  username?: string;
  email?: string;
  status?: User['status'];
  createdAt?: Date;
  limit?: number;
  offset?: number;
}

export interface OrderQuery {
  id?: string;
  userId?: string;
  orderNumber?: string;
  status?: Order['status'];
  paymentStatus?: Order['paymentStatus'];
  createdAt?: Date;
  limit?: number;
  offset?: number;
}
```

### Prisma Schema

```prisma
// 生成的Prisma Schema
generator client {
  provider = "prisma-client-js"
}

datasource db {
  provider = "postgresql"
  url      = env("DATABASE_URL")
}

model User {
  id            String   @id @default(uuid())
  username      String   @unique @db.VarChar(50)
  email         String   @unique @db.VarChar(100)
  passwordHash  String   @db.VarChar(255)
  firstName     String?  @db.VarChar(50)
  lastName      String?  @db.VarChar(50)
  phone         String?  @db.VarChar(20)
  status        UserStatus @default(ACTIVE)
  createdAt     DateTime @default(now())
  updatedAt     DateTime @updatedAt

  // 关联
  orders        Order[]

  @@map("user")
}

model Order {
  id            String   @id @default(uuid())
  userId        String
  orderNumber   String   @unique @db.VarChar(20)
  status        OrderStatus @default(PENDING)
  totalAmount   Decimal  @default(0) @db.Decimal(10, 2)
  currency      Currency @default(USD)
  shippingAddress Json?
  billingAddress   Json?
  paymentMethod String?  @db.VarChar(50)
  paymentStatus PaymentStatus @default(PENDING)
  notes         String?
  createdAt     DateTime @default(now())
  updatedAt     DateTime @updatedAt

  // 关联
  user          User     @relation(fields: [userId], references: [id], onDelete: Cascade)
  items         OrderItem[]

  @@map("order")
}

model OrderItem {
  id          String   @id @default(uuid())
  orderId     String
  productId   String
  quantity    Int
  unitPrice   Decimal  @db.Decimal(10, 2)
  totalPrice  Decimal  @db.Decimal(10, 2)

  // 关联
  order       Order    @relation(fields: [orderId], references: [id], onDelete: Cascade)
  product     Product  @relation(fields: [productId], references: [id])

  @@map("order_item")
}

model Product {
  id            String   @id @default(uuid())
  name          String   @db.VarChar(100)
  description   String?
  price         Decimal  @db.Decimal(10, 2)
  currency      Currency @default(USD)
  categoryId    String
  stockQuantity Int      @default(0)
  isActive      Boolean  @default(true)
  createdAt     DateTime @default(now())
  updatedAt     DateTime @updatedAt

  // 关联
  category     Category @relation(fields: [categoryId], references: [id])
  orderItems   OrderItem[]

  @@map("product")
}

model Category {
  id          String   @id @default(uuid())
  name        String   @db.VarChar(50)
  description String?
  parentId    String?
  isActive    Boolean  @default(true)
  createdAt   DateTime @default(now())
  updatedAt   DateTime @updatedAt

  // 关联
  parent      Category? @relation("CategoryHierarchy", fields: [parentId], references: [id])
  children    Category[] @relation("CategoryHierarchy")
  products    Product[]

  @@map("category")
}

model AuditLog {
  id            String      @id @default(uuid())
  tableName     String      @db.VarChar(50)
  recordId      String
  operation     AuditOperation
  oldValues     Json?
  newValues     Json?
  changedFields String[]
  userId        String?
  ipAddress     String?
  userAgent     String?
  createdAt     DateTime    @default(now())

  @@map("audit_log")
}

enum UserStatus {
  ACTIVE
  INACTIVE
  SUSPENDED
}

enum OrderStatus {
  PENDING
  CONFIRMED
  PROCESSING
  SHIPPED
  DELIVERED
  CANCELLED
}

enum PaymentStatus {
  PENDING
  PAID
  FAILED
  REFUNDED
}

enum Currency {
  USD
  EUR
  GBP
  JPY
}

enum AuditOperation {
  INSERT
  UPDATE
  DELETE
}
```

## 验证规则

### 语法验证

```dsl
validation_rules "data_model_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "version", "namespace", "entities"]
      message: "必须包含描述、版本、命名空间和实体"
    },
    {
      rule: "valid_field_type"
      allowed_types: ["string", "integer", "decimal", "boolean", "date", "timestamp", "uuid", "json", "enum"]
      message: "字段类型必须是支持的类型"
    },
    {
      rule: "valid_relationship_type"
      allowed_types: ["one_to_one", "one_to_many", "many_to_one", "many_to_many"]
      message: "关系类型必须是支持的类型"
    }
  ]
  
  semantic: [
    {
      rule: "entity_uniqueness"
      condition: "entity names are unique within namespace"
      message: "实体名称在命名空间内必须唯一"
    },
    {
      rule: "field_uniqueness"
      condition: "field names are unique within entity"
      message: "字段名称在实体内必须唯一"
    },
    {
      rule: "relationship_validity"
      condition: "referenced entities and fields exist"
      message: "引用的实体和字段必须存在"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "data_model_performance" {
  constraints: [
    {
      metric: "table_size"
      threshold: "1GB"
      action: "warn"
    },
    {
      metric: "index_count"
      threshold: 10
      action: "error"
    },
    {
      metric: "foreign_key_depth"
      threshold: 5
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "index_optimization"
      enabled: true
      target_efficiency: 0.95
    },
    {
      strategy: "normalization"
      enabled: true
      target_nf: 3
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "data_model_patterns" {
  patterns: [
    {
      name: "audit_trail"
      description: "审计追踪模式"
      implementation: {
        strategy: "audit_logging"
        tracking: "all_changes"
        retention: "configurable"
      }
    },
    {
      name: "soft_delete"
      description: "软删除模式"
      implementation: {
        strategy: "deleted_at_field"
        filtering: "automatic"
        cleanup: "scheduled"
      }
    },
    {
      name: "versioning"
      description: "版本控制模式"
      implementation: {
        strategy: "version_field"
        tracking: "major_minor"
        migration: "automatic"
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "over_normalization"
      description: "过度规范化"
      symptoms: ["too_many_joins", "poor_performance"]
      solution: "denormalize_carefully"
    },
    {
      name: "under_normalization"
      description: "规范化不足"
      symptoms: ["data_redundancy", "inconsistency"]
      solution: "normalize_to_3nf"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "data_model_monitoring" {
  metrics: [
    {
      name: "table_size_bytes"
      type: "gauge"
      labels: ["table_name", "schema"]
      unit: "bytes"
    },
    {
      name: "index_usage_rate"
      type: "gauge"
      labels: ["table_name", "index_name"]
      range: [0, 1]
    },
    {
      name: "query_performance"
      type: "histogram"
      labels: ["table_name", "operation"]
      buckets: [0.1, 0.5, 1, 5, 10, 30]
    }
  ]
  
  alerts: [
    {
      name: "table_size_growth"
      condition: "table_size_bytes > 1GB"
      severity: "warning"
      action: "partition_table"
    },
    {
      name: "index_unused"
      condition: "index_usage_rate < 0.01"
      severity: "info"
      action: "review_index"
    }
  ]
}
```

## 主流标准映射

### 数据库集成

```dsl
database_integration "postgresql_integration" {
  database: {
    type: "postgresql"
    version: "14"
    connection: {
      host: "localhost"
      port: 5432
      database: "ecommerce"
      username: "${DB_USERNAME}"
      password: "${DB_PASSWORD}"
    }
  }
  
  schema: {
    name: "public"
    search_path: ["public"]
  }
  
  extensions: [
    "uuid-ossp",
    "pg_trgm",
    "btree_gin"
  ]
  
  configuration: {
    max_connections: 100
    shared_buffers: "256MB"
    effective_cache_size: "1GB"
    maintenance_work_mem: "64MB"
    checkpoint_completion_target: 0.9
    wal_buffers: "16MB"
    default_statistics_target: 100
    random_page_cost: 1.1
    effective_io_concurrency: 200
  }
  
  backup: {
    enabled: true
    strategy: "pg_dump"
    schedule: "0 2 * * *"
    retention: "30d"
    compression: "gzip"
  }
  
  replication: {
    enabled: true
    type: "streaming"
    replicas: 2
    lag_threshold: "10s"
  }
}
```

## 工程实践示例

### 电商数据模型

```dsl
ecommerce_data_model "complete_ecommerce" {
  description: "完整电商数据模型"
  
  namespace: "ecommerce"
  
  entities: [
    {
      name: "user"
      description: "用户实体"
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
          auto_generate: true
        },
        {
          name: "username"
          type: "string"
          length: 50
          unique: true
          not_null: true
        },
        {
          name: "email"
          type: "string"
          length: 100
          unique: true
          not_null: true
          validation: "email"
        },
        {
          name: "password_hash"
          type: "string"
          length: 255
          not_null: true
        },
        {
          name: "first_name"
          type: "string"
          length: 50
        },
        {
          name: "last_name"
          type: "string"
          length: 50
        },
        {
          name: "phone"
          type: "string"
          length: 20
          validation: "phone"
        },
        {
          name: "status"
          type: "enum"
          values: ["active", "inactive", "suspended"]
          default: "active"
        },
        {
          name: "created_at"
          type: "timestamp"
          default: "now()"
          not_null: true
        },
        {
          name: "updated_at"
          type: "timestamp"
          default: "now()"
          on_update: "now()"
          not_null: true
        }
      ]
    },
    {
      name: "product"
      description: "商品实体"
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
          auto_generate: true
        },
        {
          name: "name"
          type: "string"
          length: 100
          not_null: true
        },
        {
          name: "description"
          type: "text"
        },
        {
          name: "price"
          type: "decimal"
          precision: 10
          scale: 2
          not_null: true
        },
        {
          name: "currency"
          type: "string"
          length: 3
          default: "USD"
          not_null: true
        },
        {
          name: "category_id"
          type: "uuid"
          not_null: true
        },
        {
          name: "stock_quantity"
          type: "integer"
          default: 0
          not_null: true
        },
        {
          name: "is_active"
          type: "boolean"
          default: true
          not_null: true
        },
        {
          name: "created_at"
          type: "timestamp"
          default: "now()"
          not_null: true
        },
        {
          name: "updated_at"
          type: "timestamp"
          default: "now()"
          on_update: "now()"
          not_null: true
        }
      ]
    },
    {
      name: "order"
      description: "订单实体"
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
          auto_generate: true
        },
        {
          name: "user_id"
          type: "uuid"
          not_null: true
        },
        {
          name: "order_number"
          type: "string"
          length: 20
          unique: true
          not_null: true
        },
        {
          name: "status"
          type: "enum"
          values: ["pending", "confirmed", "processing", "shipped", "delivered", "cancelled"]
          default: "pending"
          not_null: true
        },
        {
          name: "total_amount"
          type: "decimal"
          precision: 10
          scale: 2
          not_null: true
          default: 0.00
        },
        {
          name: "currency"
          type: "string"
          length: 3
          default: "USD"
          not_null: true
        },
        {
          name: "shipping_address"
          type: "json"
        },
        {
          name: "billing_address"
          type: "json"
        },
        {
          name: "payment_method"
          type: "string"
          length: 50
        },
        {
          name: "payment_status"
          type: "enum"
          values: ["pending", "paid", "failed", "refunded"]
          default: "pending"
        },
        {
          name: "notes"
          type: "text"
        },
        {
          name: "created_at"
          type: "timestamp"
          default: "now()"
          not_null: true
        },
        {
          name: "updated_at"
          type: "timestamp"
          default: "now()"
          on_update: "now()"
          not_null: true
        }
      ]
    }
  ]
  
  relationships: [
    {
      name: "user_orders"
      from: "user"
      to: "order"
      type: "one_to_many"
      foreign_key: "user_id"
    },
    {
      name: "product_category"
      from: "product"
      to: "category"
      type: "many_to_one"
      foreign_key: "category_id"
    },
    {
      name: "order_items"
      from: "order"
      to: "order_item"
      type: "one_to_many"
      foreign_key: "order_id"
    }
  ]
  
  indexes: [
    {
      name: "idx_user_email"
      table: "user"
      fields: ["email"]
      type: "unique"
    },
    {
      name: "idx_user_username"
      table: "user"
      fields: ["username"]
      type: "unique"
    },
    {
      name: "idx_product_category"
      table: "product"
      fields: ["category_id"]
      type: "btree"
    },
    {
      name: "idx_order_user"
      table: "order"
      fields: ["user_id"]
      type: "btree"
    },
    {
      name: "idx_order_status"
      table: "order"
      fields: ["status"]
      type: "btree"
    }
  ]
  
  constraints: [
    {
      name: "chk_user_email_format"
      table: "user"
      type: "check"
      expression: "email ~* '^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,}$'"
    },
    {
      name: "chk_order_total_amount"
      table: "order"
      type: "check"
      expression: "total_amount >= 0"
    }
  ]
  
  audit: {
    enabled: true
    tables: ["user", "product", "order"]
    fields: ["id", "created_at", "updated_at"]
    retention: "1y"
  }
  
  backup: {
    enabled: true
    strategy: "pg_dump"
    schedule: "0 2 * * *"
    retention: "30d"
    compression: "gzip"
  }
  
  monitoring: {
    metrics: [
      "table_size",
      "index_usage",
      "query_performance",
      "connection_count"
    ]
    alerting: {
      on_table_growth: {
        threshold: "1GB"
        severity: "warning"
        action: "partition_table"
      }
      on_slow_queries: {
        threshold: "5s"
        severity: "warning"
        action: "optimize_query"
      }
    }
  }
}
```

这个DSL设计提供了完整的数据模型建模能力，支持多种数据类型、关系定义、约束规则、索引策略，并能够与主流数据库平台无缝集成。
