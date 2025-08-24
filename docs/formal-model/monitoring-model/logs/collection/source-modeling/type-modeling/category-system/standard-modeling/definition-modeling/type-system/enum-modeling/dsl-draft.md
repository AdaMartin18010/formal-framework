# 枚举建模DSL草案

## 1. 设计目标

- 用统一DSL描述离散取值集合的稳定标识、显示文本、元数据等要素
- 支持自动生成JSON Schema、Protobuf、OpenAPI、数据库枚举等
- 支持权限、安全、审计、AI自动化等高级特性

## 2. 基本语法结构

```dsl
enum "CountryCode" {
  values: ["CN", "US", "JP", "DE", "FR", "GB"]
  metadata: {
    CN: { label: "中国", flag: "🇨🇳", phone_code: "+86" },
    US: { label: "美国", flag: "🇺🇸", phone_code: "+1" },
    JP: { label: "日本", flag: "🇯🇵", phone_code: "+81" }
  }
  default: "CN"
  required: true
}

enum "OrderStatus" {
  values: ["pending", "confirmed", "shipped", "delivered", "cancelled"]
  metadata: {
    pending: { label: "待处理", color: "#ffa500" },
    confirmed: { label: "已确认", color: "#0000ff" },
    shipped: { label: "已发货", color: "#ff00ff" },
    delivered: { label: "已送达", color: "#00ff00" },
    cancelled: { label: "已取消", color: "#ff0000" }
  }
  default: "pending"
  state_machine: {
    transitions: [
      { from: "pending", to: ["confirmed", "cancelled"] },
      { from: "confirmed", to: ["shipped", "cancelled"] },
      { from: "shipped", to: ["delivered"] }
    ]
  }
}
```

## 3. 关键元素

- enum：枚举声明
- values：枚举值列表
- metadata：枚举值元数据
- label：显示标签
- default：默认值
- state_machine：状态机定义

## 4. 高级用法

### 4.1 国际化与本地化

```dsl
enum "Language" {
  values: ["zh-CN", "en-US", "ja-JP"]
  metadata: {
    "zh-CN": { label: "简体中文", flag: "🇨🇳", currency: "CNY" },
    "en-US": { label: "English", flag: "🇺🇸", currency: "USD" },
    "ja-JP": { label: "日本語", flag: "🇯🇵", currency: "JPY" }
  }
  default: "zh-CN"
  i18n: {
    supported_locales: ["zh-CN", "en-US", "ja-JP"],
    fallback_locale: "en-US"
  }
}
```

### 4.2 业务规则与约束

```dsl
enum "ProductCategory" {
  values: ["electronics", "clothing", "books", "food"]
  metadata: {
    electronics: { label: "电子产品", tax_rate: 0.13, max_discount: 0.20 },
    clothing: { label: "服装", tax_rate: 0.10, max_discount: 0.50 },
    books: { label: "图书", tax_rate: 0.05, max_discount: 0.30 },
    food: { label: "食品", tax_rate: 0.08, max_discount: 0.15 }
  }
  business_rules: {
    tax_calculation: "category.tax_rate * price",
    discount_validation: "discount <= category.max_discount"
  }
}
```

## 5. 代码生成模板

### 5.1 JSON Schema生成

```json
{
  "type": "string",
  "title": "CountryCode",
  "description": "国家代码",
  "enum": ["CN", "US", "JP", "DE", "FR", "GB"],
  "default": "CN",
  "metadata": {
    "CN": { "label": "中国", "flag": "🇨🇳", "phone_code": "+86" },
    "US": { "label": "美国", "flag": "🇺🇸", "phone_code": "+1" }
  }
}
```

### 5.2 数据库枚举生成

```sql
-- PostgreSQL
CREATE TYPE order_status AS ENUM ('pending', 'confirmed', 'shipped', 'delivered', 'cancelled');

CREATE TABLE orders (
  id SERIAL PRIMARY KEY,
  status order_status NOT NULL DEFAULT 'pending',
  country_code VARCHAR(2) NOT NULL DEFAULT 'CN'
);

-- MySQL
CREATE TABLE orders (
  id INT PRIMARY KEY AUTO_INCREMENT,
  status ENUM('pending', 'confirmed', 'shipped', 'delivered', 'cancelled') NOT NULL DEFAULT 'pending',
  country_code ENUM('CN', 'US', 'JP', 'DE', 'FR', 'GB') NOT NULL DEFAULT 'CN'
);
```

### 5.3 TypeScript类型生成

```typescript
// 基础枚举类型
type CountryCode = 'CN' | 'US' | 'JP' | 'DE' | 'FR' | 'GB';

type OrderStatus = 'pending' | 'confirmed' | 'shipped' | 'delivered' | 'cancelled';

// 枚举元数据
interface CountryMetadata {
  label: string;
  flag: string;
  phone_code: string;
}

// 枚举配置
const COUNTRY_METADATA: Record<CountryCode, CountryMetadata> = {
  CN: { label: "中国", flag: "🇨🇳", phone_code: "+86" },
  US: { label: "美国", flag: "🇺🇸", phone_code: "+1" },
  JP: { label: "日本", flag: "🇯🇵", phone_code: "+81" }
};

// 验证函数
function getCountryLabel(code: CountryCode): string {
  return COUNTRY_METADATA[code].label;
}

function isValidStatusTransition(from: OrderStatus, to: OrderStatus): boolean {
  const transitions = {
    pending: ['confirmed', 'cancelled'],
    confirmed: ['shipped', 'cancelled'],
    shipped: ['delivered']
  };
  return transitions[from]?.includes(to) || false;
}
```

## 6. 验证规则

```yaml
validation:
  required_fields:
    - enum.name
    - enum.values
  
  type_constraints:
    - field: "enum.name"
      type: "string"
      pattern: "^[A-Z][a-zA-Z0-9_]*$"
    - field: "enum.values"
      type: "array"
      min_items: 1
    - field: "enum.values[]"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
  
  business_rules:
    - rule: "enum values must be unique"
    - rule: "enum names must follow PascalCase convention"
    - rule: "metadata keys must match enum values"
```

## 7. 最佳实践

### 7.1 枚举设计模式

```dsl
# 状态枚举模式
enum "status_pattern" {
  values: ["active", "inactive", "pending", "completed"]
  metadata: {
    active: { label: "激活", color: "#00ff00" },
    inactive: { label: "非激活", color: "#ff0000" },
    pending: { label: "待处理", color: "#ffa500" },
    completed: { label: "已完成", color: "#0000ff" }
  }
  state_machine: {
    transitions: [
      { from: "pending", to: ["active", "inactive"] },
      { from: "active", to: ["inactive", "completed"] },
      { from: "inactive", to: ["active"] }
    ]
  }
}

# 权限枚举模式
enum "permission_pattern" {
  values: ["read", "write", "delete", "admin"]
  metadata: {
    read: { label: "读取", level: 1 },
    write: { label: "写入", level: 2 },
    delete: { label: "删除", level: 3 },
    admin: { label: "管理", level: 4 }
  }
  hierarchy: {
    read: 1,
    write: 2,
    delete: 3,
    admin: 4
  }
}
```

## 8. 与主流标准的映射

| DSL元素 | JSON Schema | Protobuf | OpenAPI | Database |
|---------|-------------|----------|---------|----------|
| enum | enum | enum | enum | ENUM |
| values | enum values | enum values | enum values | enum values |
| metadata | n/a | n/a | n/a | n/a |
| default | default | default | default | DEFAULT |
| state_machine | n/a | n/a | n/a | n/a |

## 9. 工程实践示例

```dsl
# 电商系统枚举示例
enum "ProductStatus" {
  values: ["draft", "active", "inactive", "discontinued"]
  metadata: {
    draft: { label: "草稿", color: "#808080" },
    active: { label: "上架", color: "#00ff00" },
    inactive: { label: "下架", color: "#ffa500" },
    discontinued: { label: "停售", color: "#ff0000" }
  }
  default: "draft"
  state_machine: {
    transitions: [
      { from: "draft", to: ["active"] },
      { from: "active", to: ["inactive", "discontinued"] },
      { from: "inactive", to: ["active", "discontinued"] }
    ]
  }
}

enum "PaymentStatus" {
  values: ["pending", "processing", "completed", "failed", "refunded"]
  metadata: {
    pending: { label: "待支付", color: "#ffa500" },
    processing: { label: "处理中", color: "#0000ff" },
    completed: { label: "已完成", color: "#00ff00" },
    failed: { label: "失败", color: "#ff0000" },
    refunded: { label: "已退款", color: "#800080" }
  }
  default: "pending"
  state_machine: {
    transitions: [
      { from: "pending", to: ["processing", "failed"] },
      { from: "processing", to: ["completed", "failed"] },
      { from: "completed", to: ["refunded"] },
      { from: "failed", to: ["pending"] }
    ]
  }
}
```

这个DSL设计为枚举建模提供了完整的配置语言，支持从简单的值集合到复杂的状态机和业务规则的各种需求，同时保持了良好的可扩展性和可维护性。
