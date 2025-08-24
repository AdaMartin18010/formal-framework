# 约束建模DSL草案

## 1. 设计目标

- 用统一DSL描述字段级、对象级、跨对象的校验约束
- 支持自动生成JSON Schema、Protobuf、OpenAPI、数据库约束等
- 支持权限、安全、审计、AI自动化等高级特性

## 2. 基本语法结构

```dsl
constraints "user_constraints" {
  field_level: [
    {
      target: "user.age"
      rules: [
        { type: "min", value: 0 },
        { type: "max", value: 150 }
      ]
    },
    {
      target: "user.email"
      rules: [
        { type: "format", value: "email" },
        { type: "unique", value: true }
      ]
    },
    {
      target: "user.password"
      rules: [
        { type: "min_length", value: 8 },
        { type: "pattern", value: "^(?=.*[a-z])(?=.*[A-Z])(?=.*\\d)" }
      ]
    }
  ]
  
  object_level: [
    {
      target: "user"
      rules: [
        { type: "required_fields", value: ["name", "email", "age"] },
        { type: "unique_combination", value: ["email", "phone"] }
      ]
    }
  ]
  
  cross_object: [
    {
      target: "order.user_id"
      rules: [
        { type: "foreign_key", value: "user.id" },
        { type: "exists", value: "user.active = true" }
      ]
    }
  ]
}
```

## 3. 关键元素

- constraints：约束声明
- field_level：字段级约束
- object_level：对象级约束
- cross_object：跨对象约束
- target：约束目标
- rules：约束规则列表
- type：约束类型
- value：约束值

## 4. 高级用法

### 4.1 复杂业务规则约束

```dsl
constraints "order_business_rules" {
  field_level: [
    {
      target: "order.amount"
      rules: [
        { type: "min", value: 0.01 },
        { type: "max", value: 1000000.00 },
        { type: "precision", value: 2 }
      ]
    },
    {
      target: "order.status"
      rules: [
        { type: "enum", value: ["pending", "confirmed", "shipped", "delivered", "cancelled"] }
      ]
    }
  ]
  
  object_level: [
    {
      target: "order"
      rules: [
        { type: "business_rule", value: "amount > 0 AND status != 'cancelled'" },
        { type: "conditional_required", value: "payment_method required when amount > 1000" }
      ]
    }
  ]
  
  cross_object: [
    {
      target: "order.customer_id"
      rules: [
        { type: "foreign_key", value: "customer.id" },
        { type: "business_rule", value: "customer.status = 'active'" }
      ]
    }
  ]
}
```

### 4.2 数据完整性约束

```dsl
constraints "data_integrity" {
  field_level: [
    {
      target: "product.sku"
      rules: [
        { type: "unique", value: true },
        { type: "pattern", value: "^[A-Z]{2}[0-9]{6}$" },
        { type: "not_null", value: true }
      ]
    },
    {
      target: "product.price"
      rules: [
        { type: "min", value: 0 },
        { type: "precision", value: 2 }
      ]
    }
  ]
  
  object_level: [
    {
      target: "product"
      rules: [
        { type: "unique_combination", value: ["name", "category"] },
        { type: "business_rule", value: "price > cost_price" }
      ]
    }
  ]
}
```

## 5. 代码生成模板

### 5.1 JSON Schema生成

```json
{
  "type": "object",
  "properties": {
    "age": {
      "type": "integer",
      "minimum": 0,
      "maximum": 150
    },
    "email": {
      "type": "string",
      "format": "email",
      "unique": true
    },
    "password": {
      "type": "string",
      "minLength": 8,
      "pattern": "^(?=.*[a-z])(?=.*[A-Z])(?=.*\\d)"
    }
  },
  "required": ["name", "email", "age"]
}
```

### 5.2 数据库约束生成

```sql
-- MySQL
CREATE TABLE users (
  id INT PRIMARY KEY AUTO_INCREMENT,
  name VARCHAR(100) NOT NULL,
  email VARCHAR(255) UNIQUE NOT NULL,
  age INT NOT NULL,
  password VARCHAR(255) NOT NULL,
  
  -- 字段级约束
  CONSTRAINT chk_age_range CHECK (age >= 0 AND age <= 150),
  CONSTRAINT chk_email_format CHECK (email REGEXP '^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,}$'),
  CONSTRAINT chk_password_length CHECK (LENGTH(password) >= 8)
);
```

### 5.3 TypeScript验证函数生成

```typescript
interface User {
  id?: number;
  name: string;
  email: string;
  age: number;
  password: string;
}

// 字段级验证
function validateUserField(user: User): boolean {
  // 年龄验证
  if (user.age < 0 || user.age > 150) {
    throw new Error("年龄必须在0-150之间");
  }
  
  // 邮箱验证
  const emailRegex = /^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}$/;
  if (!emailRegex.test(user.email)) {
    throw new Error("邮箱格式不正确");
  }
  
  // 密码验证
  if (user.password.length < 8) {
    throw new Error("密码长度至少8位");
  }
  
  const passwordRegex = /^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)/;
  if (!passwordRegex.test(user.password)) {
    throw new Error("密码必须包含大小写字母和数字");
  }
  
  return true;
}

// 对象级验证
function validateUser(user: User): boolean {
  // 必填字段验证
  if (!user.name || !user.email || user.age === undefined) {
    throw new Error("姓名、邮箱和年龄为必填字段");
  }
  
  // 字段级验证
  validateUserField(user);
  
  return true;
}
```

## 6. 验证规则

```yaml
validation:
  required_fields:
    - constraints.name
    - constraints.field_level
    - constraints.object_level
  
  type_constraints:
    - field: "constraints.field_level[].target"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*\\.[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "constraints.field_level[].rules[].type"
      type: "string"
      allowed_values: ["min", "max", "pattern", "format", "unique", "required", "enum"]
  
  business_rules:
    - rule: "constraint targets must be valid field paths"
    - rule: "constraint rules must be compatible with field types"
    - rule: "cross-object constraints must reference valid objects"
```

## 7. 最佳实践

### 7.1 约束设计模式

```dsl
# 数据完整性模式
constraints "data_integrity_pattern" {
  field_level: [
    {
      target: "entity.id"
      rules: [
        { type: "unique", value: true },
        { type: "not_null", value: true }
      ]
    }
  ]
  
  object_level: [
    {
      target: "entity"
      rules: [
        { type: "required_fields", value: ["id", "created_at"] }
      ]
    }
  ]
}

# 业务规则模式
constraints "business_rule_pattern" {
  field_level: [
    {
      target: "order.amount"
      rules: [
        { type: "min", value: 0.01 },
        { type: "business_rule", value: "positive_amount" }
      ]
    }
  ]
  
  object_level: [
    {
      target: "order"
      rules: [
        { type: "business_rule", value: "valid_order_state" }
      ]
    }
  ]
}
```

## 8. 与主流标准的映射

| DSL元素 | JSON Schema | Protobuf | OpenAPI | Database |
|---------|-------------|----------|---------|----------|
| constraints | n/a | validate.rules | n/a | n/a |
| field_level | properties | field rules | properties | COLUMN |
| object_level | n/a | message rules | n/a | TABLE |
| cross_object | n/a | n/a | n/a | FOREIGN KEY |
| rules | validation | validate.rules | validation | CHECK |

## 9. 工程实践示例

```dsl
# 电商系统约束示例
constraints "product_constraints" {
  field_level: [
    {
      target: "product.id"
      rules: [
        { type: "unique", value: true },
        { type: "uuid_format", value: true }
      ]
    },
    {
      target: "product.name"
      rules: [
        { type: "not_empty", value: true },
        { type: "max_length", value: 200 }
      ]
    },
    {
      target: "product.price"
      rules: [
        { type: "min", value: 0.01 },
        { type: "precision", value: 2 }
      ]
    },
    {
      target: "product.category"
      rules: [
        { type: "enum", value: ["electronics", "clothing", "books", "food"] }
      ]
    }
  ]
  
  object_level: [
    {
      target: "product"
      rules: [
        { type: "required_fields", value: ["id", "name", "price", "category"] },
        { type: "business_rule", value: "price > cost_price" }
      ]
    }
  ]
}

constraints "order_constraints" {
  field_level: [
    {
      target: "order.id"
      rules: [
        { type: "unique", value: true },
        { type: "pattern", value: "^ORD-[0-9]{8}$" }
      ]
    },
    {
      target: "order.amount"
      rules: [
        { type: "min", value: 0.01 },
        { type: "precision", value: 2 }
      ]
    },
    {
      target: "order.status"
      rules: [
        { type: "enum", value: ["pending", "confirmed", "shipped", "delivered", "cancelled"] }
      ]
    }
  ]
  
  object_level: [
    {
      target: "order"
      rules: [
        { type: "required_fields", value: ["id", "customer_id", "amount", "status"] },
        { type: "business_rule", value: "amount > 0 AND status != 'cancelled'" }
      ]
    }
  ]
  
  cross_object: [
    {
      target: "order.customer_id"
      rules: [
        { type: "foreign_key", value: "customer.id" },
        { type: "business_rule", value: "customer.status = 'active'" }
      ]
    }
  ]
}
```

这个DSL设计为约束建模提供了完整的配置语言，支持从简单的字段验证到复杂的业务规则的各种需求，同时保持了良好的可扩展性和可维护性。
