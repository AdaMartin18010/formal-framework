# 时间戳类型建模DSL草案

## 1. 设计目标

- 用统一DSL描述时间戳字段的时区、精度、格式、约束等要素
- 支持自动生成JSON Schema、Protobuf、OpenAPI、数据库字段定义等
- 支持权限、安全、审计、AI自动化等高级特性

## 2. 基本语法结构

```dsl
timestamp_type "created_at" {
  timezone: "+08:00"
  precision: "milliseconds"
  format: "ISO8601"
  constraints: [
    "not_future",
    "after_epoch"
  ]
  default: "now"
  required: true
}

timestamp_type "updated_at" {
  timezone: "UTC"
  precision: "milliseconds"
  format: "ISO8601"
  constraints: [
    "not_future",
    "after_created_at"
  ]
  auto_update: true
  default: "now"
}

timestamp_type "expiry_date" {
  timezone: "+08:00"
  precision: "seconds"
  format: "ISO8601"
  constraints: [
    "future_only",
    "reasonable_future"
  ]
  validation: {
    business_rule: "expiry date must be in the future"
    error_message: "过期时间必须在未来"
  }
}
```

## 3. 关键元素

- timestamp_type：时间戳类型声明
- timezone：时区设置
- precision：时间精度（seconds/milliseconds/microseconds/nanoseconds）
- format：时间格式
- constraints：约束条件列表
- default：默认值
- auto_update：是否自动更新
- validation：验证规则

## 4. 高级用法

### 4.1 时区处理与转换

```dsl
timestamp_type "global_event_time" {
  timezone: "UTC"
  precision: "milliseconds"
  format: "ISO8601"
  timezone_conversion: {
    display_timezone: "+08:00"
    conversion_rules: [
      { from: "UTC", to: "+08:00", offset: "+8h" },
      { from: "UTC", to: "-05:00", offset: "-5h" }
    ]
  }
  constraints: [
    "not_future",
    "after_epoch"
  ]
  validation: {
    business_rule: "event time must be in UTC"
    error_message: "事件时间必须是UTC时间"
  }
}
```

### 4.2 时间范围与业务规则

```dsl
timestamp_type "business_hours" {
  timezone: "+08:00"
  precision: "minutes"
  format: "HH:mm"
  business_rules: {
    start_time: "09:00"
    end_time: "18:00"
    working_days: ["monday", "tuesday", "wednesday", "thursday", "friday"]
    holidays: "holiday_calendar"
  }
  constraints: [
    "within_business_hours",
    "working_days_only"
  ]
  validation: {
    business_rule: "operations must be within business hours"
    error_message: "操作必须在营业时间内"
  }
}
```

### 4.3 时间计算与相对时间

```dsl
timestamp_type "relative_time" {
  timezone: "+08:00"
  precision: "seconds"
  format: "ISO8601"
  relative_calculation: {
    base_field: "created_at"
    offset: "+30d"
    operation: "add"
  }
  constraints: [
    "after_base_time",
    "reasonable_offset"
  ]
  validation: {
    business_rule: "relative time must be calculated from base time"
    error_message: "相对时间必须从基准时间计算"
  }
}
```

## 5. 代码生成模板

### 5.1 JSON Schema生成

```json
{
  "type": "string",
  "title": "created_at",
  "description": "创建时间",
  "format": "date-time",
  "timezone": "+08:00",
  "precision": "milliseconds",
  "default": "now",
  "constraints": ["not_future", "after_epoch"],
  "validation": {
    "business_rule": "creation time cannot be in the future",
    "error_message": "创建时间不能在未来"
  }
}
```

### 5.2 数据库字段定义生成

```sql
-- MySQL
CREATE TABLE events (
  id INT PRIMARY KEY AUTO_INCREMENT,
  created_at TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP(3),
  updated_at TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP(3) ON UPDATE CURRENT_TIMESTAMP(3),
  expiry_date TIMESTAMP(3) NOT NULL,
  
  -- 约束检查
  CONSTRAINT chk_created_not_future CHECK (created_at <= NOW()),
  CONSTRAINT chk_updated_after_created CHECK (updated_at >= created_at),
  CONSTRAINT chk_expiry_future CHECK (expiry_date > NOW())
);
```

### 5.3 TypeScript类型生成

```typescript
interface Event {
  id: number;
  created_at: string; // ISO8601 format
  updated_at: string; // ISO8601 format
  expiry_date: string; // ISO8601 format
}

// 时间验证函数
function validateEventTimes(event: Event): boolean {
  const now = new Date();
  const created = new Date(event.created_at);
  const updated = new Date(event.updated_at);
  const expiry = new Date(event.expiry_date);
  
  // 创建时间不能在未来
  if (created > now) {
    throw new Error("创建时间不能在未来");
  }
  
  // 更新时间必须在创建时间之后
  if (updated < created) {
    throw new Error("更新时间必须在创建时间之后");
  }
  
  // 过期时间必须在未来
  if (expiry <= now) {
    throw new Error("过期时间必须在未来");
  }
  
  return true;
}
```

## 6. 验证规则

```yaml
validation:
  required_fields:
    - timestamp_type.name
    - timestamp_type.timezone
    - timestamp_type.precision
    - timestamp_type.format
  
  type_constraints:
    - field: "timestamp_type.timezone"
      pattern: "^[+-][0-9]{2}:[0-9]{2}$|^UTC$"
    - field: "timestamp_type.precision"
      allowed_values: ["seconds", "milliseconds", "microseconds", "nanoseconds"]
    - field: "timestamp_type.format"
      allowed_values: ["ISO8601", "RFC3339", "Unix", "Custom"]
  
  business_rules:
    - rule: "timezone must be valid format"
    - rule: "precision must be supported by target platform"
    - rule: "format must be parseable by target system"
```

## 7. 最佳实践

### 7.1 时间戳类型设计模式

```dsl
# 创建时间模式
timestamp_type "creation_time_pattern" {
  timezone: "UTC"
  precision: "milliseconds"
  format: "ISO8601"
  default: "now"
  constraints: [
    "not_future",
    "after_epoch"
  ]
  validation: {
    business_rule: "creation time cannot be in the future"
    error_message: "创建时间不能在未来"
  }
}

# 更新时间模式
timestamp_type "update_time_pattern" {
  timezone: "UTC"
  precision: "milliseconds"
  format: "ISO8601"
  auto_update: true
  default: "now"
  constraints: [
    "not_future",
    "after_created_at"
  ]
  validation: {
    business_rule: "update time must be after creation time"
    error_message: "更新时间必须在创建时间之后"
  }
}

# 过期时间模式
timestamp_type "expiry_time_pattern" {
  timezone: "UTC"
  precision: "seconds"
  format: "ISO8601"
  constraints: [
    "future_only",
    "reasonable_future"
  ]
  validation: {
    business_rule: "expiry time must be in the future"
    error_message: "过期时间必须在未来"
  }
}
```

## 8. 与主流标准的映射

| DSL元素 | JSON Schema | Protobuf | OpenAPI | Database |
|---------|-------------|----------|---------|----------|
| timestamp_type | type: string, format: date-time | google.protobuf.Timestamp | type: string, format: date-time | TIMESTAMP |
| timezone | n/a | n/a | n/a | TIMEZONE |
| precision | n/a | n/a | n/a | precision |
| format | format | n/a | format | n/a |
| constraints | n/a | validate.rules | n/a | CHECK |

## 9. 工程实践示例

```dsl
# 用户系统时间戳示例
timestamp_type "user_created_at" {
  timezone: "UTC"
  precision: "milliseconds"
  format: "ISO8601"
  default: "now"
  constraints: [
    "not_future",
    "after_epoch"
  ]
  validation: {
    business_rule: "user creation time cannot be in the future"
    error_message: "用户创建时间不能在未来"
  }
}

timestamp_type "user_last_login" {
  timezone: "UTC"
  precision: "milliseconds"
  format: "ISO8601"
  auto_update: true
  constraints: [
    "not_future",
    "after_created_at"
  ]
  validation: {
    business_rule: "last login time must be after user creation"
    error_message: "最后登录时间必须在用户创建之后"
  }
}

timestamp_type "user_password_expiry" {
  timezone: "UTC"
  precision: "seconds"
  format: "ISO8601"
  relative_calculation: {
    base_field: "password_changed_at"
    offset: "+90d"
    operation: "add"
  }
  constraints: [
    "future_only",
    "reasonable_future"
  ]
  validation: {
    business_rule: "password expiry must be 90 days after password change"
    error_message: "密码过期时间必须在密码修改后90天"
  }
}
```

这个DSL设计为时间戳类型建模提供了完整的配置语言，支持从简单的时间记录到复杂的时区处理和业务规则的各种需求，同时保持了良好的可扩展性和可维护性。
