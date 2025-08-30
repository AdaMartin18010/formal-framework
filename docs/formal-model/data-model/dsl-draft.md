# 数据模型DSL设计 (Data Model DSL Design)

## 概述

数据模型DSL设计提供了用于定义和管理数据模型的领域特定语言。该DSL支持实体定义、关系建模、约束规范、索引设计等数据建模的核心功能。

## 设计目标

### 1. 简洁性

- 使用直观的语法表达复杂的数据模型
- 减少样板代码，提高开发效率
- 支持声明式和命令式两种风格

### 2. 表达能力

- 支持复杂的数据类型和关系
- 提供丰富的约束和验证规则
- 支持继承、组合、聚合等高级特性

### 3. 可扩展性

- 支持自定义类型和验证器
- 提供插件机制扩展功能
- 支持版本管理和演进

### 4. 工具支持

- 提供IDE支持和语法高亮
- 支持代码生成和反向工程
- 提供可视化和文档生成

## 语法设计

### 1. 基础语法

```yaml
# 数据模型DSL基础语法
basic_syntax:
  description: "数据模型DSL的基础语法结构"
  
  syntax_rules:
    - name: "模型定义"
      syntax: "model <model_name> { ... }"
      description: "定义数据模型"
      
    - name: "实体定义"
      syntax: "entity <entity_name> { ... }"
      description: "定义数据实体"
      
    - name: "属性定义"
      syntax: "<type> <property_name> [constraints]"
      description: "定义实体属性"
      
    - name: "关系定义"
      syntax: "relation <relation_name> to <target_entity> [constraints]"
      description: "定义实体关系"
      
    - name: "索引定义"
      syntax: "index <index_name> on <properties> [options]"
      description: "定义数据索引"
```

### 2. 数据类型

```yaml
# 数据类型定义
data_types:
  description: "DSL支持的数据类型"
  
  primitive_types:
    - name: "String"
      description: "字符串类型"
      examples:
        - "String name"
        - "String email(max_length: 255)"
        - "String phone(pattern: '^\\+?[1-9]\\d{1,14}$')"
        
    - name: "Integer"
      description: "整数类型"
      examples:
        - "Integer age"
        - "Integer id(auto_increment: true)"
        - "Integer count(min: 0, max: 1000)"
        
    - name: "Decimal"
      description: "小数类型"
      examples:
        - "Decimal price(precision: 10, scale: 2)"
        - "Decimal amount(min: 0.0)"
        
    - name: "Boolean"
      description: "布尔类型"
      examples:
        - "Boolean active"
        - "Boolean verified(default: false)"
        
    - name: "Date"
      description: "日期类型"
      examples:
        - "Date birth_date"
        - "Date created_at(auto: true)"
        
    - name: "DateTime"
      description: "日期时间类型"
      examples:
        - "DateTime last_login"
        - "DateTime updated_at(auto: true)"
        
    - name: "UUID"
      description: "UUID类型"
      examples:
        - "UUID id(generate: true)"
        - "UUID session_id"
        
  complex_types:
    - name: "Array"
      description: "数组类型"
      examples:
        - "Array<String> tags"
        - "Array<Integer> scores"
        
    - name: "Map"
      description: "映射类型"
      examples:
        - "Map<String, String> metadata"
        - "Map<String, Object> properties"
        
    - name: "Object"
      description: "对象类型"
      examples:
        - "Object address"
        - "Object contact_info"
        
    - name: "Enum"
      description: "枚举类型"
      examples:
        - "Enum Status(ACTIVE, INACTIVE, SUSPENDED)"
        - "Enum UserType(ADMIN, USER, GUEST)"
```

### 3. 约束定义

```yaml
# 约束定义
constraints:
  description: "数据约束和验证规则"
  
  validation_constraints:
    - name: "not_null"
      description: "非空约束"
      syntax: "not_null"
      example: "String name(not_null: true)"
      
    - name: "unique"
      description: "唯一性约束"
      syntax: "unique"
      example: "String email(unique: true)"
      
    - name: "min_length"
      description: "最小长度"
      syntax: "min_length: <value>"
      example: "String password(min_length: 8)"
      
    - name: "max_length"
      description: "最大长度"
      syntax: "max_length: <value>"
      example: "String description(max_length: 1000)"
      
    - name: "pattern"
      description: "正则表达式模式"
      syntax: "pattern: '<regex>'"
      example: "String phone(pattern: '^\\+?[1-9]\\d{1,14}$')"
      
    - name: "min"
      description: "最小值"
      syntax: "min: <value>"
      example: "Integer age(min: 0)"
      
    - name: "max"
      description: "最大值"
      syntax: "max: <value>"
      example: "Integer score(max: 100)"
      
    - name: "email"
      description: "邮箱格式"
      syntax: "email"
      example: "String email(email: true)"
      
    - name: "url"
      description: "URL格式"
      syntax: "url"
      example: "String website(url: true)"
      
  business_constraints:
    - name: "custom_validator"
      description: "自定义验证器"
      syntax: "validator: '<validator_name>'"
      example: "String code(validator: 'validateProductCode')"
      
    - name: "conditional"
      description: "条件约束"
      syntax: "conditional: '<condition>'"
      example: "String company_name(conditional: 'user_type == BUSINESS')"
      
    - name: "depends_on"
      description: "依赖约束"
      syntax: "depends_on: '<property>'"
      example: "String department(depends_on: 'company_id')"
```

## 实体建模

### 1. 基础实体

```yaml
# 基础实体示例
basic_entity_example:
  description: "基础实体定义示例"
  
  user_entity: |
    entity User {
      UUID id(generate: true, primary_key: true)
      String username(not_null: true, unique: true, min_length: 3, max_length: 50)
      String email(not_null: true, unique: true, email: true)
      String password(not_null: true, min_length: 8)
      String first_name(not_null: true, max_length: 100)
      String last_name(not_null: true, max_length: 100)
      Date birth_date
      Enum Gender(MALE, FEMALE, OTHER)
      Boolean active(default: true)
      DateTime created_at(auto: true)
      DateTime updated_at(auto: true)
      
      // 索引定义
      index idx_username on username
      index idx_email on email
      index idx_created_at on created_at
      
      // 验证规则
      validator validateAge {
        if (birth_date != null && age < 13) {
          error "User must be at least 13 years old"
        }
      }
    }
    
  product_entity: |
    entity Product {
      UUID id(generate: true, primary_key: true)
      String name(not_null: true, max_length: 200)
      String sku(not_null: true, unique: true, pattern: '^[A-Z0-9]{8,12}$')
      String description(max_length: 2000)
      Decimal price(not_null: true, min: 0.0, precision: 10, scale: 2)
      Integer stock_quantity(not_null: true, min: 0, default: 0)
      Enum Status(ACTIVE, INACTIVE, DISCONTINUED)
      Array<String> categories
      Map<String, Object> attributes
      DateTime created_at(auto: true)
      DateTime updated_at(auto: true)
      
      // 索引定义
      index idx_sku on sku
      index idx_name on name
      index idx_status on status
      index idx_categories on categories
      
      // 业务规则
      validator validateStock {
        if (stock_quantity < 0) {
          error "Stock quantity cannot be negative"
        }
      }
      
      validator validatePrice {
        if (price <= 0) {
          error "Price must be greater than zero"
        }
      }
    }
```

### 2. 关系建模

```yaml
# 关系建模示例
relationship_modeling:
  description: "实体关系建模示例"
  
  one_to_one: |
    entity User {
      UUID id(generate: true, primary_key: true)
      String username(not_null: true, unique: true)
      String email(not_null: true, unique: true)
      
      // 一对一关系
      relation profile to UserProfile(one_to_one)
    }
    
    entity UserProfile {
      UUID id(generate: true, primary_key: true)
      String avatar_url
      String bio(max_length: 500)
      String location(max_length: 100)
      Date join_date(auto: true)
      
      // 一对一关系
      relation user to User(one_to_one)
    }
    
  one_to_many: |
    entity User {
      UUID id(generate: true, primary_key: true)
      String username(not_null: true, unique: true)
      String email(not_null: true, unique: true)
      
      // 一对多关系
      relation orders to Order(one_to_many)
      relation posts to Post(one_to_many)
    }
    
    entity Order {
      UUID id(generate: true, primary_key: true)
      Decimal total_amount(not_null: true, min: 0.0)
      Enum Status(PENDING, CONFIRMED, SHIPPED, DELIVERED, CANCELLED)
      DateTime created_at(auto: true)
      
      // 多对一关系
      relation user to User(many_to_one)
      relation items to OrderItem(one_to_many)
    }
    
  many_to_many: |
    entity User {
      UUID id(generate: true, primary_key: true)
      String username(not_null: true, unique: true)
      String email(not_null: true, unique: true)
      
      // 多对多关系
      relation roles to Role(many_to_many)
      relation groups to Group(many_to_many)
    }
    
    entity Role {
      UUID id(generate: true, primary_key: true)
      String name(not_null: true, unique: true)
      String description(max_length: 200)
      
      // 多对多关系
      relation users to User(many_to_many)
      relation permissions to Permission(many_to_many)
    }
    
    entity UserRole {
      UUID id(generate: true, primary_key: true)
      DateTime assigned_at(auto: true)
      String assigned_by(not_null: true)
      
      // 关联实体
      relation user to User(many_to_one)
      relation role to Role(many_to_one)
    }
```

### 3. 继承建模

```yaml
# 继承建模示例
inheritance_modeling:
  description: "实体继承建模示例"
  
  single_table_inheritance: |
    entity Person {
      UUID id(generate: true, primary_key: true)
      String name(not_null: true, max_length: 100)
      String email(not_null: true, unique: true)
      Date birth_date
      Enum Type(EMPLOYEE, CUSTOMER, SUPPLIER)
      
      // 继承字段
      String employee_id(conditional: 'type == EMPLOYEE')
      String department(conditional: 'type == EMPLOYEE')
      Decimal salary(conditional: 'type == EMPLOYEE')
      
      String customer_id(conditional: 'type == CUSTOMER')
      String membership_level(conditional: 'type == CUSTOMER')
      
      String supplier_id(conditional: 'type == SUPPLIER')
      String company_name(conditional: 'type == SUPPLIER')
      String contact_person(conditional: 'type == SUPPLIER')
    }
    
  table_per_class: |
    entity Person {
      UUID id(generate: true, primary_key: true)
      String name(not_null: true, max_length: 100)
      String email(not_null: true, unique: true)
      Date birth_date
    }
    
    entity Employee extends Person {
      String employee_id(not_null: true, unique: true)
      String department(not_null: true)
      Decimal salary(not_null: true, min: 0.0)
      Date hire_date(not_null: true)
    }
    
    entity Customer extends Person {
      String customer_id(not_null: true, unique: true)
      String membership_level(default: 'BRONZE')
      DateTime last_purchase
      Decimal total_spent(default: 0.0)
    }
    
    entity Supplier extends Person {
      String supplier_id(not_null: true, unique: true)
      String company_name(not_null: true)
      String contact_person(not_null: true)
      String phone(not_null: true)
      String address(not_null: true)
    }
```

## 高级特性

### 1. 聚合根

```yaml
# 聚合根示例
aggregate_root_example:
  description: "聚合根实体示例"
  
  order_aggregate: |
    aggregate Order {
      UUID id(generate: true, primary_key: true)
      UUID customer_id(not_null: true)
      Enum Status(PENDING, CONFIRMED, SHIPPED, DELIVERED, CANCELLED)
      Decimal total_amount(not_null: true, min: 0.0)
      DateTime created_at(auto: true)
      DateTime updated_at(auto: true)
      
      // 聚合内的实体
      entity OrderItem {
        UUID id(generate: true, primary_key: true)
        UUID product_id(not_null: true)
        String product_name(not_null: true)
        Integer quantity(not_null: true, min: 1)
        Decimal unit_price(not_null: true, min: 0.0)
        Decimal total_price(not_null: true, min: 0.0)
      }
      
      entity OrderPayment {
        UUID id(generate: true, primary_key: true)
        String payment_method(not_null: true)
        String transaction_id(not_null: true, unique: true)
        Decimal amount(not_null: true, min: 0.0)
        Enum Status(PENDING, COMPLETED, FAILED, REFUNDED)
        DateTime processed_at
      }
      
      entity OrderShipment {
        UUID id(generate: true, primary_key: true)
        String tracking_number
        String carrier(not_null: true)
        String service_level(not_null: true)
        DateTime shipped_at
        DateTime delivered_at
        String delivery_address(not_null: true)
      }
      
      // 业务规则
      invariant totalAmountConsistency {
        total_amount == sum(items.total_price)
      }
      
      invariant paymentAmountConsistency {
        sum(payments.amount) <= total_amount
      }
      
      // 业务方法
      method addItem(product_id: UUID, quantity: Integer) {
        // 添加订单项的逻辑
      }
      
      method processPayment(payment_method: String, amount: Decimal) {
        // 处理支付的逻辑
      }
      
      method ship(tracking_number: String, carrier: String) {
        // 发货的逻辑
      }
    }
```

### 2. 事件溯源

```yaml
# 事件溯源示例
event_sourcing_example:
  description: "事件溯源实体示例"
  
  user_events: |
    entity User {
      UUID id(generate: true, primary_key: true)
      String username(not_null: true, unique: true)
      String email(not_null: true, unique: true)
      Boolean active(default: true)
      Integer version(not_null: true, default: 0)
      
      // 事件定义
      event UserCreated {
        UUID user_id
        String username
        String email
        DateTime created_at
      }
      
      event UserUpdated {
        UUID user_id
        Map<String, Object> changes
        DateTime updated_at
      }
      
      event UserDeactivated {
        UUID user_id
        String reason
        DateTime deactivated_at
      }
      
      event UserReactivated {
        UUID user_id
        DateTime reactivated_at
      }
      
      // 事件处理器
      handler onUserCreated(event: UserCreated) {
        this.id = event.user_id
        this.username = event.username
        this.email = event.email
        this.version = 1
      }
      
      handler onUserUpdated(event: UserUpdated) {
        // 应用变更
        event.changes.forEach { key, value ->
          this[key] = value
        }
        this.version++
      }
      
      handler onUserDeactivated(event: UserDeactivated) {
        this.active = false
        this.version++
      }
      
      handler onUserReactivated(event: UserReactivated) {
        this.active = true
        this.version++
      }
    }
```

### 3. 值对象

```yaml
# 值对象示例
value_object_example:
  description: "值对象定义示例"
  
  address_value_object: |
    value_object Address {
      String street(not_null: true, max_length: 200)
      String city(not_null: true, max_length: 100)
      String state(not_null: true, max_length: 50)
      String country(not_null: true, max_length: 50)
      String postal_code(not_null: true, max_length: 20)
      
      // 验证规则
      validator validatePostalCode {
        if (country == 'US' && !postal_code.matches('^\\d{5}(-\\d{4})?$')) {
          error "Invalid US postal code format"
        }
        if (country == 'CA' && !postal_code.matches('^[A-Za-z]\\d[A-Za-z] \\d[A-Za-z]\\d$')) {
          error "Invalid Canadian postal code format"
        }
      }
      
      // 业务方法
      method format() {
        return "${street}, ${city}, ${state} ${postal_code}, ${country}"
      }
      
      method isDomestic() {
        return country == 'US'
      }
    }
    
  money_value_object: |
    value_object Money {
      Decimal amount(not_null: true, min: 0.0, precision: 10, scale: 2)
      String currency(not_null: true, pattern: '^[A-Z]{3}$')
      
      // 验证规则
      validator validateCurrency {
        if (!['USD', 'EUR', 'GBP', 'JPY', 'CAD'].contains(currency)) {
          error "Unsupported currency: ${currency}"
        }
      }
      
      // 业务方法
      method add(other: Money) {
        if (this.currency != other.currency) {
          error "Cannot add money with different currencies"
        }
        return Money(amount: this.amount + other.amount, currency: this.currency)
      }
      
      method multiply(factor: Decimal) {
        return Money(amount: this.amount * factor, currency: this.currency)
      }
      
      method format() {
        return "${currency} ${amount}"
      }
    }
```

## 代码生成

### 1. 目标语言支持

```yaml
# 代码生成目标
code_generation_targets:
  description: "支持的代码生成目标语言"
  
  languages:
    - name: "Java"
      description: "Java代码生成"
      features:
        - "JPA实体类"
        - "Spring Boot配置"
        - "验证注解"
        - "业务逻辑"
      example: |
        @Entity
        @Table(name = "users")
        public class User {
            #foreach($field in $fields)
            @${field.annotation}
            private ${field.type} ${field.name};
            #end
            
            // Constructors
            public ${className}() {}
            
            // Getters and Setters
            #foreach($field in $fields)
            public ${field.type} get${field.capitalizedName}() {
                return ${field.name};
            }
            
            public void set${field.capitalizedName}(${field.type} ${field.name}) {
                this.${field.name} = ${field.name};
            }
            #end
        }
        
    - name: "TypeScript"
      description: "TypeScript代码生成"
      features:
        - "接口定义"
        - "类型定义"
        - "验证装饰器"
        - "API客户端"
      example: |
        export interface User {
            id: string;
            username: string;
            email: string;
            firstName: string;
            lastName: string;
            birthDate?: Date;
            gender?: Gender;
            active: boolean;
            createdAt: Date;
            updatedAt: Date;
        }
        
    - name: "Python"
      description: "Python代码生成"
      features:
        - "SQLAlchemy模型"
        - "Pydantic模型"
        - "验证规则"
        - "API模型"
      example: |
        from sqlalchemy import Column, String, Boolean, DateTime, UUID
        from sqlalchemy.ext.declarative import declarative_base
        
        Base = declarative_base()
        
        class User(Base):
            __tablename__ = 'users'
            
            id = Column(UUID, primary_key=True)
            username = Column(String(50), unique=True, nullable=False)
            email = Column(String, unique=True, nullable=False)
            active = Column(Boolean, default=True)
            
    - name: "SQL"
      description: "SQL DDL生成"
      features:
        - "表定义"
        - "索引定义"
        - "约束定义"
        - "视图定义"
      example: |
        CREATE TABLE users (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            username VARCHAR(50) NOT NULL UNIQUE,
            email VARCHAR(255) NOT NULL UNIQUE,
            first_name VARCHAR(100) NOT NULL,
            last_name VARCHAR(100) NOT NULL,
            birth_date DATE,
            gender VARCHAR(10) CHECK (gender IN ('MALE', 'FEMALE', 'OTHER')),
            active BOOLEAN DEFAULT TRUE,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        );
        
        CREATE INDEX idx_users_username ON users(username);
        CREATE INDEX idx_users_email ON users(email);
        CREATE INDEX idx_users_created_at ON users(created_at);
```

### 2. 模板引擎

```yaml
# 模板引擎配置
template_engine_config:
  description: "代码生成模板引擎配置"
  
  velocity_templates:
    - name: "java_entity_template"
      description: "Java实体类模板"
      template: |
        package ${package};
        
        import javax.persistence.*;
        import javax.validation.constraints.*;
        import java.time.LocalDateTime;
        import java.util.UUID;
        
        @Entity
        @Table(name = "${tableName}")
        public class ${className} {
            #foreach($field in $fields)
            @${field.annotation}
            private ${field.type} ${field.name};
            #end
            
            // Constructors
            public ${className}() {}
            
            // Getters and Setters
            #foreach($field in $fields)
            public ${field.type} get${field.capitalizedName}() {
                return ${field.name};
            }
            
            public void set${field.capitalizedName}(${field.type} ${field.name}) {
                this.${field.name} = ${field.name};
            }
            #end
        }
        
    - name: "typescript_interface_template"
      description: "TypeScript接口模板"
      template: |
        export interface ${className} {
            #foreach($field in $fields)
            ${field.name}${field.optional}: ${field.type};
            #end
        }
        
        export interface Create${className}Request {
            #foreach($field in $createFields)
            ${field.name}${field.optional}: ${field.type};
            #end
        }
        
        export interface Update${className}Request {
            #foreach($field in $updateFields)
            ${field.name}?: ${field.type};
            #end
        }
        
    - name: "sql_ddl_template"
      description: "SQL DDL模板"
      template: |
        CREATE TABLE ${tableName} (
            #foreach($field in $fields)
            ${field.name} ${field.sqlType}${field.constraints}#if($foreach.hasNext),#end
            #end
        );
        
        #foreach($index in $indexes)
        CREATE INDEX ${index.name} ON ${tableName}(${index.columns});
        #end
```

## 工具支持

### 1. IDE支持

```yaml
# IDE支持配置
ide_support:
  description: "IDE支持和插件配置"
  
  features:
    - name: "语法高亮"
      description: "DSL语法高亮支持"
      implementation:
        - "TextMate语法"
        - "Language Server Protocol"
        - "自定义语法高亮"
        
    - name: "自动补全"
      description: "智能代码补全"
      implementation:
        - "上下文感知补全"
        - "实体属性补全"
        - "关系补全"
        - "约束补全"
        
    - name: "错误检查"
      description: "实时错误检查"
      implementation:
        - "语法错误检查"
        - "语义错误检查"
        - "约束冲突检查"
        - "循环依赖检查"
        
    - name: "重构支持"
      description: "代码重构功能"
      implementation:
        - "重命名重构"
        - "提取方法"
        - "移动实体"
        - "内联展开"
        
    - name: "可视化"
      description: "数据模型可视化"
      implementation:
        - "ER图生成"
        - "关系图显示"
        - "继承层次图"
        - "依赖关系图"
```

### 2. 调试支持

```yaml
# 调试支持配置
debug_support:
  description: "调试和测试支持"
  
  features:
    - name: "模型验证"
      description: "数据模型验证"
      tools:
        - "语法验证器"
        - "语义验证器"
        - "约束验证器"
        - "循环检测器"
        
    - name: "代码生成测试"
      description: "代码生成测试"
      tools:
        - "模板测试"
        - "输出验证"
        - "编译测试"
        - "集成测试"
        
    - name: "性能分析"
      description: "性能分析工具"
      tools:
        - "模型复杂度分析"
        - "查询性能分析"
        - "索引优化建议"
        - "内存使用分析"
        
    - name: "文档生成"
      description: "文档自动生成"
      tools:
        - "API文档生成"
        - "数据字典生成"
        - "ER图生成"
        - "关系图生成"
```

## 最佳实践

### 1. 命名规范

```yaml
# 命名规范
naming_conventions:
  description: "DSL命名规范和约定"
  
  conventions:
    - name: "实体命名"
      rule: "使用PascalCase，单数形式"
      examples:
        - "User"
        - "Product"
        - "Order"
        - "UserProfile"
        
    - name: "属性命名"
      rule: "使用camelCase"
      examples:
        - "firstName"
        - "lastName"
        - "emailAddress"
        - "phoneNumber"
        
    - name: "关系命名"
      rule: "使用描述性名称，反映关系语义"
      examples:
        - "userOrders"
        - "productCategories"
        - "orderItems"
        - "userProfile"
        
    - name: "索引命名"
      rule: "使用idx_前缀，后跟表名和字段名"
      examples:
        - "idx_users_email"
        - "idx_products_category"
        - "idx_orders_created_at"
        
    - name: "约束命名"
      rule: "使用描述性名称，反映约束目的"
      examples:
        - "uk_users_email"
        - "ck_users_age_positive"
        - "fk_orders_user_id"
```

### 2. 设计原则

```yaml
# 设计原则
design_principles:
  description: "数据模型设计原则"
  
  principles:
    - name: "单一职责"
      description: "每个实体只负责一个业务概念"
      example: "User实体只管理用户基本信息，UserProfile管理用户详细信息"
      
    - name: "高内聚低耦合"
      description: "实体内部高度相关，实体间松耦合"
      example: "Order和OrderItem高内聚，Order和Product低耦合"
      
    - name: "数据完整性"
      description: "通过约束保证数据完整性"
      example: "使用外键约束、检查约束、唯一约束"
      
    - name: "性能考虑"
      description: "设计时考虑查询性能"
      example: "合理设计索引、避免过度规范化"
      
    - name: "可扩展性"
      description: "设计支持未来扩展"
      example: "使用版本字段、预留扩展字段"
      
    - name: "一致性"
      description: "保持命名和结构的一致性"
      example: "统一的命名规范、相似实体的相似结构"
```

## 应用案例

### 1. 电商系统

```yaml
# 电商系统数据模型
ecommerce_data_model:
  description: "电商系统的数据模型示例"
  
  model: |
    model ECommerce {
      entity User {
        UUID id(generate: true, primary_key: true)
        String username(not_null: true, unique: true, min_length: 3, max_length: 50)
        String email(not_null: true, unique: true, email: true)
        String password(not_null: true, min_length: 8)
        String firstName(not_null: true, max_length: 100)
        String lastName(not_null: true, max_length: 100)
        Enum Role(ADMIN, CUSTOMER, SELLER)
        Boolean active(default: true)
        DateTime createdAt(auto: true)
        DateTime updatedAt(auto: true)
        
        relation profile to UserProfile(one_to_one)
        relation orders to Order(one_to_many)
        relation addresses to Address(one_to_many)
        relation reviews to Review(one_to_many)
      }
      
      entity Product {
        UUID id(generate: true, primary_key: true)
        String name(not_null: true, max_length: 200)
        String sku(not_null: true, unique: true)
        String description(max_length: 2000)
        Decimal price(not_null: true, min: 0.0, precision: 10, scale: 2)
        Integer stockQuantity(not_null: true, min: 0, default: 0)
        Enum Status(ACTIVE, INACTIVE, DISCONTINUED)
        UUID sellerId(not_null: true)
        Array<String> categories
        Map<String, Object> attributes
        DateTime createdAt(auto: true)
        DateTime updatedAt(auto: true)
        
        relation seller to User(many_to_one)
        relation images to ProductImage(one_to_many)
        relation reviews to Review(one_to_many)
        relation orderItems to OrderItem(one_to_many)
      }
      
      entity Order {
        UUID id(generate: true, primary_key: true)
        UUID customerId(not_null: true)
        Enum Status(PENDING, CONFIRMED, SHIPPED, DELIVERED, CANCELLED)
        Decimal totalAmount(not_null: true, min: 0.0, precision: 10, scale: 2)
        String shippingAddress(not_null: true)
        String billingAddress(not_null: true)
        DateTime createdAt(auto: true)
        DateTime updatedAt(auto: true)
        
        relation customer to User(many_to_one)
        relation items to OrderItem(one_to_many)
        relation payments to Payment(one_to_many)
        relation shipments to Shipment(one_to_many)
      }
      
      entity OrderItem {
        UUID id(generate: true, primary_key: true)
        UUID orderId(not_null: true)
        UUID productId(not_null: true)
        String productName(not_null: true)
        Integer quantity(not_null: true, min: 1)
        Decimal unitPrice(not_null: true, min: 0.0, precision: 10, scale: 2)
        Decimal totalPrice(not_null: true, min: 0.0, precision: 10, scale: 2)
        
        relation order to Order(many_to_one)
        relation product to Product(many_to_one)
      }
      
      // 索引定义
      index idx_users_email on User.email
      index idx_users_username on User.username
      index idx_products_sku on Product.sku
      index idx_products_seller on Product.sellerId
      index idx_orders_customer on Order.customerId
      index idx_orders_status on Order.status
      index idx_order_items_order on OrderItem.orderId
      index idx_order_items_product on OrderItem.productId
    }
```

### 2. 内容管理系统

```yaml
# 内容管理系统数据模型
cms_data_model:
  description: "内容管理系统的数据模型示例"
  
  model: |
    model CMS {
      entity User {
        UUID id(generate: true, primary_key: true)
        String username(not_null: true, unique: true)
        String email(not_null: true, unique: true, email: true)
        String password(not_null: true, min_length: 8)
        Enum Role(ADMIN, EDITOR, AUTHOR, VIEWER)
        Boolean active(default: true)
        DateTime createdAt(auto: true)
        DateTime updatedAt(auto: true)
        
        relation profile to UserProfile(one_to_one)
        relation articles to Article(one_to_many)
        relation comments to Comment(one_to_many)
      }
      
      entity Article {
        UUID id(generate: true, primary_key: true)
        String title(not_null: true, max_length: 200)
        String slug(not_null: true, unique: true, pattern: '^[a-z0-9-]+$')
        String content(not_null: true)
        String excerpt(max_length: 500)
        Enum Status(DRAFT, PUBLISHED, ARCHIVED)
        UUID authorId(not_null: true)
        Array<String> tags
        DateTime publishedAt
        DateTime createdAt(auto: true)
        DateTime updatedAt(auto: true)
        
        relation author to User(many_to_one)
        relation comments to Comment(one_to_many)
        relation categories to Category(many_to_many)
      }
      
      entity Category {
        UUID id(generate: true, primary_key: true)
        String name(not_null: true, max_length: 100)
        String slug(not_null: true, unique: true)
        String description(max_length: 500)
        UUID parentId
        Integer sortOrder(default: 0)
        DateTime createdAt(auto: true)
        DateTime updatedAt(auto: true)
        
        relation parent to Category(many_to_one)
        relation children to Category(one_to_many)
        relation articles to Article(many_to_many)
      }
      
      entity Comment {
        UUID id(generate: true, primary_key: true)
        UUID articleId(not_null: true)
        UUID authorId(not_null: true)
        String content(not_null: true, max_length: 1000)
        UUID parentId
        Boolean approved(default: false)
        DateTime createdAt(auto: true)
        DateTime updatedAt(auto: true)
        
        relation article to Article(many_to_one)
        relation author to User(many_to_one)
        relation parent to Comment(many_to_one)
        relation replies to Comment(one_to_many)
      }
      
      // 索引定义
      index idx_articles_slug on Article.slug
      index idx_articles_author on Article.authorId
      index idx_articles_status on Article.status
      index idx_articles_published on Article.publishedAt
      index idx_categories_slug on Category.slug
      index idx_categories_parent on Category.parentId
      index idx_comments_article on Comment.articleId
      index idx_comments_author on Comment.authorId
      index idx_comments_parent on Comment.parentId
    }
```

## 相关概念

- [数据建模理论](theory.md)
- [实体建模](entity/theory.md)
- [查询建模](query/theory.md)
- [领域特定语言](../core-concepts/domain-specific-language.md)

## 参考文献

1. Fowler, M. (2010). "Domain-Specific Languages"
2. Evans, E. (2003). "Domain-Driven Design"
3. Vernon, V. (2013). "Implementing Domain-Driven Design"
4. ANTLR Documentation (2023). "ANTLR 4 Documentation"
5. Xtext Documentation (2023). "Xtext Documentation"
