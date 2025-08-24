# 复合类型建模DSL草案

## 1. 设计目标

- 用统一DSL描述由多个基本类型组合而成的复合类型结构
- 支持自动生成JSON Schema、Protobuf、OpenAPI、数据库字段定义等
- 支持权限、安全、审计、AI自动化等高级特性

## 2. 基本语法结构

```dsl
composite_type "Address" {
  fields: [
    {
      name: "country"
      type: "string"
      constraints: ["not_empty"]
      required: true
    },
    {
      name: "city"
      type: "string"
      required: true
    },
    {
      name: "zipcode"
      type: "string"
      constraints: ["regex:^[0-9]{5}$"]
      required: true
    },
    {
      name: "lines"
      type: "array<string>"
      min_items: 1
      max_items: 5
      required: true
    }
  ]
  validation: {
    business_rule: "address must have valid country and city"
    error_message: "地址必须有有效的国家和城市"
  }
}
```

## 3. 关键元素

- composite_type：复合类型声明
- fields：字段定义列表
- name：字段名称
- type：字段类型
- constraints：约束条件
- required：是否必填
- validation：验证规则

## 4. 高级用法

### 4.1 嵌套复合类型

```dsl
composite_type "Person" {
  fields: [
    {
      name: "name"
      type: "string"
      constraints: ["not_empty", "max_length:100"]
      required: true
    },
    {
      name: "age"
      type: "integer"
      constraints: ["min:0", "max:150"]
      required: true
    },
    {
      name: "address"
      type: "Address"
      required: true
    }
  ]
}
```

### 4.2 条件字段与依赖关系

```dsl
composite_type "Order" {
  fields: [
    {
      name: "order_id"
      type: "string"
      constraints: ["unique"]
      required: true
    },
    {
      name: "payment_method"
      type: "enum"
      values: ["credit_card", "bank_transfer", "cash"]
      required: true
    },
    {
      name: "credit_card_info"
      type: "CreditCardInfo"
      required: false
      condition: "payment_method == 'credit_card'"
    }
  ]
}
```

## 5. 代码生成模板

### 5.1 JSON Schema生成

```json
{
  "type": "object",
  "title": "Address",
  "properties": {
    "country": {
      "type": "string",
      "minLength": 1
    },
    "city": {
      "type": "string"
    },
    "zipcode": {
      "type": "string",
      "pattern": "^[0-9]{5}$"
    },
    "lines": {
      "type": "array",
      "items": {
        "type": "string"
      },
      "minItems": 1,
      "maxItems": 5
    }
  },
  "required": ["country", "city", "zipcode", "lines"]
}
```

### 5.2 TypeScript类型生成

```typescript
interface Address {
  country: string;
  city: string;
  zipcode: string;
  lines: string[];
}

function validateAddress(address: Address): boolean {
  if (!address.country || address.country.trim() === '') {
    throw new Error("国家不能为空");
  }
  
  if (!/^[0-9]{5}$/.test(address.zipcode)) {
    throw new Error("邮政编码格式不正确");
  }
  
  return true;
}
```

## 6. 验证规则

```yaml
validation:
  required_fields:
    - composite_type.name
    - composite_type.fields
  
  type_constraints:
    - field: "composite_type.fields[].name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "composite_type.fields[].type"
      type: "string"
      allowed_values: ["string", "integer", "float", "boolean", "timestamp", "enum", "array", "object"]
  
  business_rules:
    - rule: "field names must be unique within composite type"
    - rule: "required fields must have valid types"
```

## 7. 最佳实践

### 7.1 复合类型设计模式

```dsl
# 实体模式
composite_type "entity_pattern" {
  fields: [
    {
      name: "id"
      type: "string"
      constraints: ["unique", "uuid_format"]
      required: true
    },
    {
      name: "created_at"
      type: "timestamp"
      default: "now"
      required: true
    }
  ]
}

# 值对象模式
composite_type "value_object_pattern" {
  fields: [
    {
      name: "value"
      type: "string"
      constraints: ["not_empty", "valid_format"]
      required: true
    }
  ]
}
```

## 8. 与主流标准的映射

| DSL元素 | JSON Schema | Protobuf | OpenAPI | Database |
|---------|-------------|----------|---------|----------|
| composite_type | type: object | message | type: object | TABLE |
| fields | properties | fields | properties | COLUMNS |
| required | required | required | required | NOT NULL |
| constraints | n/a | validate.rules | n/a | CHECK |

## 9. 工程实践示例

```dsl
# 电商系统复合类型示例
composite_type "Product" {
  fields: [
    {
      name: "id"
      type: "string"
      constraints: ["unique", "uuid_format"]
      required: true
    },
    {
      name: "name"
      type: "string"
      constraints: ["not_empty", "max_length:200"]
      required: true
    },
    {
      name: "price"
      type: "decimal"
      precision: 10
      scale: 2
      constraints: ["min:0"]
      required: true
    },
    {
      name: "category"
      type: "enum"
      values: ["electronics", "clothing", "books", "food"]
      required: true
    }
  ]
  validation: {
    business_rule: "product must have valid name and price"
    error_message: "产品必须有有效的名称和价格"
  }
}
```

这个DSL设计为复合类型建模提供了完整的配置语言，支持从简单的数据结构到复杂的业务实体的各种需求，同时保持了良好的可扩展性和可维护性。
