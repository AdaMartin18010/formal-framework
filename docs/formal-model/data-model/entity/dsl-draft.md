# 实体建模DSL设计

## 设计目标

实体建模DSL旨在提供声明式语言定义复杂的数据实体配置，支持多种实体类型、属性定义、行为建模、生命周期管理，并与主流ORM框架无缝集成。

## 基本语法

### 核心结构

```dsl
entity_model "user_management" {
  description: "用户管理实体模型"
  version: "1.0.0"
  
  namespace: "user"
  labels: {
    domain: "user_management"
    environment: "production"
  }
  
  entities: [
    {
      name: "User"
      description: "用户实体"
      table: "users"
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
        }
      ]
    }
  ]
}
```

### 基础实体

```dsl
entity "User" {
  description: "用户实体"
  
  table: "users"
  
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
    }
  ]
  
  validations: [
    {
      name: "email_format"
      field: "email"
      rule: "email"
      message: "邮箱格式不正确"
    },
    {
      name: "phone_format"
      field: "phone"
      rule: "phone"
      message: "电话号码格式不正确"
    },
    {
      name: "username_length"
      field: "username"
      rule: "min_length:3,max_length:50"
      message: "用户名长度必须在3-50个字符之间"
    }
  ]
  
  behaviors: [
    {
      name: "password_hashing"
      type: "before_save"
      action: "hash_password"
      condition: "password_changed"
    },
    {
      name: "audit_logging"
      type: "after_save"
      action: "log_changes"
    }
  ]
}
```

### 关联实体

```dsl
entity "Order" {
  description: "订单实体"
  
  table: "orders"
  
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
      foreign_key: "users.id"
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
  
  relationships: [
    {
      name: "user"
      type: "belongs_to"
      entity: "User"
      foreign_key: "user_id"
    },
    {
      name: "items"
      type: "has_many"
      entity: "OrderItem"
      foreign_key: "order_id"
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
      name: "idx_order_number"
      fields: ["order_number"]
      type: "unique"
    }
  ]
  
  computed_fields: [
    {
      name: "item_count"
      type: "integer"
      expression: "SELECT COUNT(*) FROM order_items WHERE order_id = id"
    },
    {
      name: "is_paid"
      type: "boolean"
      expression: "payment_status = 'paid'"
    }
  ]
  
  behaviors: [
    {
      name: "order_number_generation"
      type: "before_create"
      action: "generate_order_number"
    },
    {
      name: "total_calculation"
      type: "after_save"
      action: "recalculate_total"
      condition: "items_changed"
    }
  ]
}
```

### 继承实体

```dsl
entity "Person" {
  description: "人员基类"
  
  abstract: true
  
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
  
  computed_fields: [
    {
      name: "full_name"
      type: "string"
      expression: "CONCAT(first_name, ' ', last_name)"
    }
  ]
}

entity "Customer" {
  description: "客户实体"
  
  extends: "Person"
  
  table: "customers"
  
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
  
  relationships: [
    {
      name: "orders"
      type: "has_many"
      entity: "Order"
      foreign_key: "customer_id"
    }
  ]
  
  behaviors: [
    {
      name: "membership_upgrade"
      type: "after_save"
      action: "check_membership_upgrade"
      condition: "total_spent_changed"
    }
  ]
}

entity "Employee" {
  description: "员工实体"
  
  extends: "Person"
  
  table: "employees"
  
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
  
  behaviors: [
    {
      name: "employee_id_generation"
      type: "before_create"
      action: "generate_employee_id"
    }
  ]
}
```

## 高级用法

### 聚合根实体

```dsl
entity "Order" {
  description: "订单聚合根"
  
  aggregate_root: true
  
  fields: [
    {
      name: "id"
      type: "uuid"
      primary_key: true
      auto_generate: true
    },
    {
      name: "customer_id"
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
      values: ["draft", "confirmed", "processing", "shipped", "delivered", "cancelled"]
      default: "draft"
      not_null: true
    },
    {
      name: "total_amount"
      type: "decimal"
      precision: 10
      scale: 2
      not_null: true
      default: 0.00
    }
  ]
  
  value_objects: [
    {
      name: "ShippingAddress"
      fields: [
        {
          name: "street"
          type: "string"
          length: 100
          not_null: true
        },
        {
          name: "city"
          type: "string"
          length: 50
          not_null: true
        },
        {
          name: "state"
          type: "string"
          length: 50
          not_null: true
        },
        {
          name: "zip_code"
          type: "string"
          length: 10
          not_null: true
        },
        {
          name: "country"
          type: "string"
          length: 50
          not_null: true
        }
      ]
    }
  ]
  
  entities: [
    {
      name: "OrderItem"
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
          auto_generate: true
        },
        {
          name: "product_id"
          type: "uuid"
          not_null: true
        },
        {
          name: "quantity"
          type: "integer"
          not_null: true
          min: 1
        },
        {
          name: "unit_price"
          type: "decimal"
          precision: 10
          scale: 2
          not_null: true
        },
        {
          name: "total_price"
          type: "decimal"
          precision: 10
          scale: 2
          not_null: true
        }
      ]
    }
  ]
  
  business_rules: [
    {
      name: "minimum_order_amount"
      condition: "total_amount >= 10.00"
      message: "订单金额必须大于等于10元"
    },
    {
      name: "order_status_transition"
      condition: "valid_status_transition"
      message: "订单状态转换无效"
    }
  ]
  
  domain_events: [
    {
      name: "OrderCreated"
      properties: ["order_id", "customer_id", "total_amount"]
    },
    {
      name: "OrderConfirmed"
      properties: ["order_id", "confirmed_at"]
    },
    {
      name: "OrderShipped"
      properties: ["order_id", "tracking_number", "shipped_at"]
    }
  ]
}
```

### 事件溯源实体

```dsl
entity "Product" {
  description: "商品实体（事件溯源）"
  
  event_sourced: true
  
  fields: [
    {
      name: "id"
      type: "uuid"
      primary_key: true
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
      name: "stock_quantity"
      type: "integer"
      not_null: true
      default: 0
    },
    {
      name: "is_active"
      type: "boolean"
      default: true
      not_null: true
    }
  ]
  
  events: [
    {
      name: "ProductCreated"
      properties: ["id", "name", "description", "price", "stock_quantity"]
    },
    {
      name: "ProductUpdated"
      properties: ["id", "name", "description", "price"]
    },
    {
      name: "StockAdjusted"
      properties: ["id", "quantity_change", "reason"]
    },
    {
      name: "ProductDeactivated"
      properties: ["id", "deactivated_at"]
    }
  ]
  
  event_handlers: [
    {
      event: "ProductCreated"
      handler: "apply_product_created"
    },
    {
      event: "ProductUpdated"
      handler: "apply_product_updated"
    },
    {
      event: "StockAdjusted"
      handler: "apply_stock_adjusted"
    },
    {
      event: "ProductDeactivated"
      handler: "apply_product_deactivated"
    }
  ]
  
  commands: [
    {
      name: "CreateProduct"
      properties: ["name", "description", "price", "stock_quantity"]
      handler: "handle_create_product"
    },
    {
      name: "UpdateProduct"
      properties: ["id", "name", "description", "price"]
      handler: "handle_update_product"
    },
    {
      name: "AdjustStock"
      properties: ["id", "quantity_change", "reason"]
      handler: "handle_adjust_stock"
    },
    {
      name: "DeactivateProduct"
      properties: ["id"]
      handler: "handle_deactivate_product"
    }
  ]
}
```

## 代码生成模板

### TypeScript实体类

```typescript
// 生成的TypeScript实体类
import { Entity, PrimaryKey, Property, Index, Unique, Enum, Validation } from '@mikro-orm/core';
import { v4 as uuidv4 } from 'uuid';

@Entity({ tableName: 'users' })
@Index({ name: 'idx_user_email', properties: ['email'] })
@Index({ name: 'idx_user_status', properties: ['status'] })
export class User {
  @PrimaryKey({ type: 'uuid' })
  id: string = uuidv4();

  @Property({ type: 'string', length: 50 })
  @Unique({ name: 'idx_user_username' })
  @Validation({ rule: 'minLength:3,maxLength:50', message: '用户名长度必须在3-50个字符之间' })
  username!: string;

  @Property({ type: 'string', length: 100 })
  @Unique({ name: 'idx_user_email' })
  @Validation({ rule: 'email', message: '邮箱格式不正确' })
  email!: string;

  @Property({ type: 'string', length: 255 })
  passwordHash!: string;

  @Property({ type: 'string', length: 50, nullable: true })
  firstName?: string;

  @Property({ type: 'string', length: 50, nullable: true })
  lastName?: string;

  @Property({ type: 'string', length: 20, nullable: true })
  @Validation({ rule: 'phone', message: '电话号码格式不正确' })
  phone?: string;

  @Enum({ items: () => UserStatus })
  status: UserStatus = UserStatus.ACTIVE;

  @Property({ type: 'datetime' })
  createdAt: Date = new Date();

  @Property({ type: 'datetime', onUpdate: () => new Date() })
  updatedAt: Date = new Date();

  // 关联
  @OneToMany(() => Order, order => order.user)
  orders = new Collection<Order>(this);

  // 计算属性
  get fullName(): string {
    return `${this.firstName || ''} ${this.lastName || ''}`.trim();
  }

  // 业务方法
  async hashPassword(password: string): Promise<void> {
    this.passwordHash = await bcrypt.hash(password, 10);
  }

  async verifyPassword(password: string): Promise<boolean> {
    return bcrypt.compare(password, this.passwordHash);
  }

  isActive(): boolean {
    return this.status === UserStatus.ACTIVE;
  }
}

export enum UserStatus {
  ACTIVE = 'active',
  INACTIVE = 'inactive',
  SUSPENDED = 'suspended'
}
```

### Java实体类

```java
// 生成的Java实体类
import javax.persistence.*;
import javax.validation.constraints.*;
import java.time.LocalDateTime;
import java.util.UUID;

@Entity
@Table(name = "users")
@Index(name = "idx_user_email", columnList = "email")
@Index(name = "idx_user_status", columnList = "status")
public class User {
    
    @Id
    @GeneratedValue(strategy = GenerationType.AUTO)
    @Column(columnDefinition = "uuid")
    private UUID id;
    
    @Column(length = 50, unique = true, nullable = false)
    @Size(min = 3, max = 50, message = "用户名长度必须在3-50个字符之间")
    private String username;
    
    @Column(length = 100, unique = true, nullable = false)
    @Email(message = "邮箱格式不正确")
    private String email;
    
    @Column(length = 255, nullable = false)
    private String passwordHash;
    
    @Column(length = 50)
    private String firstName;
    
    @Column(length = 50)
    private String lastName;
    
    @Column(length = 20)
    @Pattern(regexp = "^\\+?[1-9]\\d{1,14}$", message = "电话号码格式不正确")
    private String phone;
    
    @Enumerated(EnumType.STRING)
    @Column(nullable = false)
    private UserStatus status = UserStatus.ACTIVE;
    
    @Column(nullable = false)
    private LocalDateTime createdAt = LocalDateTime.now();
    
    @Column(nullable = false)
    private LocalDateTime updatedAt = LocalDateTime.now();
    
    @OneToMany(mappedBy = "user", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    private List<Order> orders = new ArrayList<>();
    
    // 计算属性
    public String getFullName() {
        return String.format("%s %s", 
            firstName != null ? firstName : "", 
            lastName != null ? lastName : "").trim();
    }
    
    // 业务方法
    public void hashPassword(String password) {
        this.passwordHash = BCrypt.hashpw(password, BCrypt.gensalt());
    }
    
    public boolean verifyPassword(String password) {
        return BCrypt.checkpw(password, this.passwordHash);
    }
    
    public boolean isActive() {
        return UserStatus.ACTIVE.equals(this.status);
    }
    
    @PreUpdate
    public void preUpdate() {
        this.updatedAt = LocalDateTime.now();
    }
    
    // Getters and Setters
    // ... (省略标准的getter和setter方法)
}

public enum UserStatus {
    ACTIVE, INACTIVE, SUSPENDED
}
```

## 验证规则

### 语法验证

```dsl
validation_rules "entity_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "table", "fields"]
      message: "必须包含描述、表名和字段"
    },
    {
      rule: "valid_field_type"
      allowed_types: ["string", "integer", "decimal", "boolean", "date", "timestamp", "uuid", "json", "enum"]
      message: "字段类型必须是支持的类型"
    },
    {
      rule: "valid_relationship_type"
      allowed_types: ["belongs_to", "has_one", "has_many", "many_to_many"]
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
      condition: "referenced entities exist"
      message: "引用的实体必须存在"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "entity_performance" {
  constraints: [
    {
      metric: "field_count"
      threshold: 50
      action: "warn"
    },
    {
      metric: "index_count"
      threshold: 10
      action: "error"
    },
    {
      metric: "relationship_depth"
      threshold: 5
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "field_optimization"
      enabled: true
      target_efficiency: 0.95
    },
    {
      strategy: "index_optimization"
      enabled: true
      target_coverage: 0.9
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "entity_patterns" {
  patterns: [
    {
      name: "audit_trail"
      description: "审计追踪模式"
      implementation: {
        strategy: "audit_fields"
        fields: ["created_at", "updated_at", "created_by", "updated_by"]
        tracking: "automatic"
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
      name: "god_entity"
      description: "上帝实体"
      symptoms: ["too_many_fields", "too_many_responsibilities"]
      solution: "split_entity"
    },
    {
      name: "anemic_entity"
      description: "贫血实体"
      symptoms: ["no_business_logic", "data_only"]
      solution: "add_behavior"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "entity_monitoring" {
  metrics: [
    {
      name: "entity_instance_count"
      type: "gauge"
      labels: ["entity_name", "status"]
    },
    {
      name: "entity_operation_duration"
      type: "histogram"
      labels: ["entity_name", "operation"]
      buckets: [0.1, 0.5, 1, 5, 10, 30]
    },
    {
      name: "entity_validation_errors"
      type: "counter"
      labels: ["entity_name", "field_name", "rule"]
    }
  ]
  
  alerts: [
    {
      name: "entity_validation_failure"
      condition: "entity_validation_errors > 0"
      severity: "warning"
      action: "review_validation_rules"
    },
    {
      name: "entity_performance_degradation"
      condition: "entity_operation_duration > 5s"
      severity: "warning"
      action: "optimize_entity"
    }
  ]
}
```

## 主流标准映射

### ORM集成

```dsl
orm_integration "typeorm_integration" {
  framework: "typeorm"
  version: "0.3.0"
  
  decorators: [
    {
      name: "Entity"
      properties: ["tableName"]
    },
    {
      name: "PrimaryKey"
      properties: ["type", "generationStrategy"]
    },
    {
      name: "Property"
      properties: ["type", "length", "nullable", "unique"]
    },
    {
      name: "Index"
      properties: ["name", "properties"]
    }
  ]
  
  validations: [
    {
      name: "IsEmail"
      message: "邮箱格式不正确"
    },
    {
      name: "Length"
      properties: ["min", "max"]
      message: "长度不符合要求"
    },
    {
      name: "IsNotEmpty"
      message: "字段不能为空"
    }
  ]
  
  relationships: [
    {
      name: "OneToMany"
      properties: ["target", "mappedBy"]
    },
    {
      name: "ManyToOne"
      properties: ["target", "inverseSide"]
    },
    {
      name: "OneToOne"
      properties: ["target", "mappedBy"]
    }
  ]
}
```

## 工程实践示例

### 电商实体模型

```dsl
ecommerce_entity_model "complete_ecommerce" {
  description: "完整电商实体模型"
  
  namespace: "ecommerce"
  
  entities: [
    {
      name: "Customer"
      description: "客户实体"
      table: "customers"
      aggregate_root: true
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
          auto_generate: true
        },
        {
          name: "customer_number"
          type: "string"
          length: 20
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
      name: "Product"
      description: "商品实体"
      table: "products"
      aggregate_root: true
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
          auto_generate: true
        },
        {
          name: "sku"
          type: "string"
          length: 50
          unique: true
          not_null: true
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
          not_null: true
          default: 0
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
      name: "Order"
      description: "订单实体"
      table: "orders"
      aggregate_root: true
      fields: [
        {
          name: "id"
          type: "uuid"
          primary_key: true
          auto_generate: true
        },
        {
          name: "customer_id"
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
          values: ["draft", "confirmed", "processing", "shipped", "delivered", "cancelled"]
          default: "draft"
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
          name: "payment_status"
          type: "enum"
          values: ["pending", "paid", "failed", "refunded"]
          default: "pending"
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
      name: "customer_orders"
      from: "Customer"
      to: "Order"
      type: "one_to_many"
      foreign_key: "customer_id"
    },
    {
      name: "product_category"
      from: "Product"
      to: "Category"
      type: "many_to_one"
      foreign_key: "category_id"
    },
    {
      name: "order_items"
      from: "Order"
      to: "OrderItem"
      type: "one_to_many"
      foreign_key: "order_id"
    }
  ]
  
  business_rules: [
    {
      name: "minimum_order_amount"
      entity: "Order"
      condition: "total_amount >= 10.00"
      message: "订单金额必须大于等于10元"
    },
    {
      name: "stock_availability"
      entity: "Product"
      condition: "stock_quantity >= 0"
      message: "库存不能为负数"
    },
    {
      name: "customer_email_unique"
      entity: "Customer"
      condition: "email is unique"
      message: "邮箱地址必须唯一"
    }
  ]
  
  domain_events: [
    {
      name: "CustomerRegistered"
      entity: "Customer"
      properties: ["customer_id", "email", "membership_level"]
    },
    {
      name: "OrderCreated"
      entity: "Order"
      properties: ["order_id", "customer_id", "total_amount"]
    },
    {
      name: "ProductStockAdjusted"
      entity: "Product"
      properties: ["product_id", "quantity_change", "new_stock"]
    }
  ]
  
  audit: {
    enabled: true
    entities: ["Customer", "Product", "Order"]
    fields: ["id", "created_at", "updated_at"]
    retention: "1y"
  }
  
  monitoring: {
    metrics: [
      "entity_instance_count",
      "entity_operation_duration",
      "business_rule_violations",
      "domain_event_count"
    ]
    alerting: {
      on_business_rule_violation: {
        threshold: 1
        severity: "warning"
        notification: "slack"
      }
      on_entity_performance_degradation: {
        threshold: "5s"
        severity: "warning"
        notification: "pagerduty"
      }
    }
  }
}
```

这个DSL设计提供了完整的实体建模能力，支持多种实体类型、属性定义、行为建模、生命周期管理，并能够与主流ORM框架无缝集成。
