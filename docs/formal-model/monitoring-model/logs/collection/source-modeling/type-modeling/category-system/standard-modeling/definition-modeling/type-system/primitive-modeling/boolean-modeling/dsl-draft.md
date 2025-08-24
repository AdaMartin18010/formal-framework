# 布尔类型建模DSL草案

## 1. 设计目标

- 用统一DSL描述布尔型字段的业务语义、约束、状态关系等要素
- 支持自动生成JSON Schema、Protobuf、OpenAPI、数据库字段定义等
- 支持权限、安全、审计、AI自动化等高级特性

## 2. 基本语法结构

```dsl
boolean_type "is_active" {
  default: true
  semantics: "资源是否处于激活状态"
  constraints: [
    "immutable_when_archived"
  ]
  validation: {
    business_rule: "active resources cannot be deleted"
    error_message: "激活状态的资源不能删除"
  }
}

boolean_type "is_deleted" {
  default: false
  semantics: "软删除标记"
  constraints: [
    "cannot_be_true_when_active"
  ]
  validation: {
    business_rule: "deleted resources cannot be active"
    error_message: "已删除的资源不能处于激活状态"
  }
}

boolean_type "is_verified" {
  default: false
  semantics: "用户是否已验证"
  constraints: [
    "requires_verification_process"
  ]
  validation: {
    business_rule: "verification requires email confirmation"
    error_message: "验证需要邮箱确认"
  }
}
```

## 3. 关键元素

- boolean_type：布尔类型声明
- default：默认值
- semantics：业务语义描述
- constraints：约束条件列表
- validation：验证规则
- business_rule：业务规则
- error_message：错误信息

## 4. 高级用法

### 4.1 状态机关系建模

```dsl
boolean_type "is_approved" {
  default: false
  semantics: "审批状态"
  state_machine: {
    states: ["pending", "approved", "rejected"]
    transitions: [
      { from: "pending", to: "approved", condition: "approver_action" },
      { from: "pending", to: "rejected", condition: "rejector_action" }
    ]
  }
  constraints: [
    "requires_approver_permission",
    "cannot_change_after_finalized"
  ]
  validation: {
    business_rule: "approval requires valid approver"
    error_message: "审批需要有效的审批人"
  }
}
```

### 4.2 权限控制建模

```dsl
boolean_type "is_admin" {
  default: false
  semantics: "管理员权限"
  permissions: {
    read: ["admin", "super_admin"]
    write: ["super_admin"]
    audit: true
  }
  constraints: [
    "requires_super_admin_approval",
    "cannot_be_self_assigned"
  ]
  validation: {
    business_rule: "admin assignment requires super admin approval"
    error_message: "管理员分配需要超级管理员审批"
  }
}
```

### 4.3 业务逻辑约束

```dsl
boolean_type "is_premium" {
  default: false
  semantics: "高级会员状态"
  dependencies: {
    subscription_active: true,
    payment_verified: true
  }
  constraints: [
    "requires_active_subscription",
    "requires_verified_payment"
  ]
  validation: {
    business_rule: "premium status requires active subscription and verified payment"
    error_message: "高级会员状态需要有效的订阅和已验证的支付"
  }
}
```

## 5. 代码生成模板

### 5.1 JSON Schema生成

```json
{
  "type": "boolean",
  "title": "is_active",
  "description": "资源是否处于激活状态",
  "default": true,
  "semantics": "资源是否处于激活状态",
  "constraints": ["immutable_when_archived"],
  "validation": {
    "business_rule": "active resources cannot be deleted",
    "error_message": "激活状态的资源不能删除"
  }
}
```

### 5.2 数据库字段定义生成

```sql
-- MySQL
CREATE TABLE resources (
  id INT PRIMARY KEY AUTO_INCREMENT,
  is_active BOOLEAN NOT NULL DEFAULT TRUE,
  is_deleted BOOLEAN NOT NULL DEFAULT FALSE,
  is_verified BOOLEAN NOT NULL DEFAULT FALSE,
  
  -- 约束检查
  CONSTRAINT chk_active_deleted CHECK (NOT (is_active = TRUE AND is_deleted = TRUE)),
  CONSTRAINT chk_verification_required CHECK (is_verified = TRUE OR status = 'pending')
);
```

### 5.3 TypeScript类型生成

```typescript
interface Resource {
  id: number;
  is_active: boolean;
  is_deleted: boolean;
  is_verified: boolean;
}

// 验证函数
function validateResource(resource: Resource): boolean {
  // 激活和删除不能同时为true
  if (resource.is_active && resource.is_deleted) {
    throw new Error("激活状态的资源不能删除");
  }
  
  // 验证状态检查
  if (!resource.is_verified && resource.status !== 'pending') {
    throw new Error("验证需要邮箱确认");
  }
  
  return true;
}
```

## 6. 验证规则

```yaml
validation:
  required_fields:
    - boolean_type.name
    - boolean_type.default
    - boolean_type.semantics
  
  type_constraints:
    - field: "boolean_type.default"
      type: "boolean"
    - field: "boolean_type.semantics"
      type: "string"
      min_length: 1
  
  business_rules:
    - rule: "boolean fields must have clear semantics"
    - rule: "constraints must be valid business rules"
    - rule: "validation rules must be consistent with constraints"
```

## 7. 最佳实践

### 7.1 布尔类型设计模式

```dsl
# 状态标记模式
boolean_type "status_flag_pattern" {
  default: false
  semantics: "状态标记"
  constraints: [
    "clear_business_meaning",
    "immutable_when_finalized"
  ]
  validation: {
    business_rule: "status flags must have clear business meaning"
    error_message: "状态标记必须有明确的业务含义"
  }
}

# 权限控制模式
boolean_type "permission_pattern" {
  default: false
  semantics: "权限控制"
  permissions: {
    read: ["admin"]
    write: ["super_admin"]
    audit: true
  }
  constraints: [
    "requires_approval",
    "audit_trail_required"
  ]
  validation: {
    business_rule: "permission changes require approval and audit"
    error_message: "权限变更需要审批和审计"
  }
}
```

## 8. 与主流标准的映射

| DSL元素 | JSON Schema | Protobuf | OpenAPI | Database |
|---------|-------------|----------|---------|----------|
| boolean_type | type: boolean | bool | type: boolean | BOOLEAN |
| default | default | default | default | DEFAULT |
| semantics | description | comment | description | COMMENT |
| constraints | n/a | validate.rules | n/a | CHECK |
| validation | n/a | validate.rules | n/a | TRIGGER |

## 9. 工程实践示例

```dsl
# 用户系统布尔字段示例
boolean_type "user_is_active" {
  default: true
  semantics: "用户是否激活"
  constraints: [
    "cannot_be_false_when_verified",
    "requires_email_confirmation"
  ]
  validation: {
    business_rule: "active users must have confirmed email"
    error_message: "激活用户必须有确认的邮箱"
  }
}

boolean_type "user_is_verified" {
  default: false
  semantics: "用户是否已验证"
  constraints: [
    "requires_verification_process",
    "cannot_be_true_without_email"
  ]
  validation: {
    business_rule: "verification requires email and process completion"
    error_message: "验证需要邮箱和流程完成"
  }
}

boolean_type "user_is_admin" {
  default: false
  semantics: "用户是否管理员"
  permissions: {
    read: ["admin", "super_admin"]
    write: ["super_admin"]
    audit: true
  }
  constraints: [
    "requires_super_admin_approval",
    "cannot_be_self_assigned"
  ]
  validation: {
    business_rule: "admin assignment requires super admin approval"
    error_message: "管理员分配需要超级管理员审批"
  }
}
```

这个DSL设计为布尔类型建模提供了完整的配置语言，支持从简单的状态标记到复杂的权限控制的各种需求，同时保持了良好的可扩展性和可维护性。
