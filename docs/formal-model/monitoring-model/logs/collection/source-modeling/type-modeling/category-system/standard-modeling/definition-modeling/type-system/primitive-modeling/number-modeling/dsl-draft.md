# 数值类型建模DSL草案

## 1. 设计目标

- 用统一DSL描述整数、浮点数、定点数、货币、百分比等数值类型
- 支持精度、范围、单位、约束等要素
- 支持自动生成JSON Schema、Protobuf、OpenAPI、数据库字段定义等

## 2. 基本语法结构

```dsl
number_type "amount" {
  kind: "decimal"
  precision: 18
  scale: 2
  unit: "CNY"
  range: {
    min: 0
    max: 100000000
  }
  default: 0.00
  required: true
}

number_type "quantity" {
  kind: "integer"
  range: {
    min: 1
    max: 999999
  }
  unit: "piece"
  default: 1
}

number_type "percentage" {
  kind: "float"
  precision: 5
  scale: 2
  unit: "%"
  range: {
    min: 0.00
    max: 100.00
  }
  default: 0.00
}
```

## 3. 关键元素

- number_type：数值类型声明
- kind：数值类型（integer/float/decimal/currency/percentage）
- precision/scale：精度和小数位数
- unit：计量单位
- range：取值范围
- default：默认值
- required：是否必填

## 4. 高级用法

### 4.1 货币类型与汇率转换

```dsl
number_type "price" {
  kind: "currency"
  precision: 18
  scale: 2
  unit: "CNY"
  exchange_rate: {
    USD: 0.14
    EUR: 0.13
    JPY: 20.5
  }
  range: {
    min: 0.01
    max: 999999.99
  }
  format: "currency"
  locale: "zh-CN"
}
```

### 4.2 约束与验证规则

```dsl
number_type "age" {
  kind: "integer"
  range: {
    min: 0
    max: 150
  }
  unit: "years"
  constraints: [
    "must_be_positive",
    "reasonable_age_range"
  ]
  validation: {
    business_rule: "age >= 18 for adult users"
    error_message: "年龄必须大于等于18岁"
  }
}
```

## 5. 代码生成模板

### 5.1 JSON Schema生成

```json
{
  "type": "number",
  "title": "amount",
  "description": "金额字段",
  "minimum": 0,
  "maximum": 100000000,
  "multipleOf": 0.01,
  "default": 0.00,
  "format": "currency",
  "unit": "CNY"
}
```

### 5.2 数据库字段定义生成

```sql
-- MySQL
CREATE TABLE products (
  id INT PRIMARY KEY AUTO_INCREMENT,
  price DECIMAL(18,2) NOT NULL DEFAULT 0.00 CHECK (price >= 0),
  quantity INT NOT NULL DEFAULT 1 CHECK (quantity > 0),
  discount_rate DECIMAL(5,2) DEFAULT 0.00 CHECK (discount_rate >= 0 AND discount_rate <= 100)
);
```

## 6. 验证规则

```yaml
validation:
  required_fields:
    - number_type.name
    - number_type.kind
    - number_type.precision
  
  type_constraints:
    - field: "number_type.kind"
      allowed_values: ["integer", "float", "decimal", "currency", "percentage"]
    - field: "number_type.precision"
      type: "integer"
      range: [1, 38]
    - field: "number_type.scale"
      type: "integer"
      range: [0, 18]
  
  business_rules:
    - rule: "scale must be less than or equal to precision"
    - rule: "min value must be less than max value"
    - rule: "default value must be within range"
```

## 7. 最佳实践

### 7.1 数值类型设计模式

```dsl
# 货币类型模式
number_type "currency_pattern" {
  kind: "currency"
  precision: 18
  scale: 2
  unit: "CNY"
  range: {
    min: 0.01
    max: 999999999.99
  }
  format: "currency"
  validation: {
    positive_only: true
    reasonable_range: true
  }
}

# 百分比类型模式
number_type "percentage_pattern" {
  kind: "percentage"
  precision: 5
  scale: 2
  unit: "%"
  range: {
    min: 0.00
    max: 100.00
  }
  format: "percentage"
  validation: {
    within_100_percent: true
  }
}
```

## 8. 与主流标准的映射

| DSL元素 | JSON Schema | Protobuf | OpenAPI | Database |
|---------|-------------|----------|---------|----------|
| number_type | type: number | double/float/int32/int64 | type: number | DECIMAL/INT/FLOAT |
| precision/scale | multipleOf | n/a | multipleOf | precision/scale |
| range | minimum/maximum | validate.rules | minimum/maximum | CHECK |
| unit | format | string field | format: currency | COMMENT |

## 9. 工程实践示例

```dsl
# 电商系统数值类型示例
number_type "product_price" {
  kind: "currency"
  precision: 18
  scale: 2
  unit: "CNY"
  range: {
    min: 0.01
    max: 999999.99
  }
  format: "currency"
  validation: {
    positive_only: true
    reasonable_price: true
  }
}

number_type "order_quantity" {
  kind: "integer"
  range: {
    min: 1
    max: 999999
  }
  unit: "piece"
  default: 1
  validation: {
    positive_only: true
    stock_available: true
  }
}

number_type "discount_percentage" {
  kind: "percentage"
  precision: 5
  scale: 2
  unit: "%"
  range: {
    min: 0.00
    max: 100.00
  }
  default: 0.00
  format: "percentage"
  validation: {
    within_100_percent: true
  }
}
```

这个DSL设计为数值类型建模提供了完整的配置语言，支持从简单的整数到复杂的货币计算的各种需求，同时保持了良好的可扩展性和可维护性。
