# 数据模型DSL草案（完整版）

## 1. 设计目标

- 用统一DSL描述实体、属性、关系、索引、迁移、约束、验证等数据要素，支持递归组合
- 支持自动生成SQL DDL、ORM模型、迁移脚本、API文档、测试用例等
- 支持权限、安全、审计、AI自动化、性能优化等高级特性
- 提供完整的类型系统、约束系统、关系系统支持

## 2. 基本语法结构

### 2.1 实体定义

```dsl
entity User {
  id: int primary key auto_increment
  name: string not null max_length(100)
  email: string unique not null pattern("^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$")
  age: int range(0, 150)
  created_at: datetime default now()
  updated_at: datetime default now() on_update(now())
  
  // 索引定义
  index idx_user_email on (email)
  index idx_user_name_email on (name, email)
  
  // 约束定义
  constraint chk_age_positive check (age >= 0)
  constraint chk_email_format check (email regexp '^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$')
  
  // 权限定义
  permission read: "authenticated"
  permission write: "owner"
  permission delete: "admin"
  
  // 审计定义
  audit: true
  audit_fields: ["email", "age"]
}

entity Post {
  id: int primary key auto_increment
  title: string not null max_length(200)
  content: text not null
  author_id: int references User(id) on_delete(cascade)
  status: enum("draft", "published", "archived") default("draft")
  published_at: datetime nullable
  created_at: datetime default now()
  updated_at: datetime default now() on_update(now())
  
  // 关系定义
  belongs_to User as author
  has_many Comment as comments
  has_many Tag through PostTag as tags
  
  // 索引定义
  index idx_post_author on (author_id)
  index idx_post_status on (status)
  index idx_post_published on (published_at) where (status = 'published')
  
  // 全文搜索索引
  fulltext idx_post_content on (title, content)
  
  // 约束定义
  constraint chk_published_date check (status != 'published' or published_at is not null)
  
  // 权限定义
  permission read: "public"
  permission write: "author"
  permission delete: "author or admin"
  
  // 审计定义
  audit: true
  audit_fields: ["title", "content", "status"]
}
```

### 2.2 关系定义

```dsl
// 一对一关系
entity Profile {
  id: int primary key auto_increment
  user_id: int unique references User(id) on_delete(cascade)
  bio: text nullable
  avatar_url: string nullable
  website: string nullable pattern("^https?://.*")
  
  belongs_to User as user
}

// 一对多关系
entity Comment {
  id: int primary key auto_increment
  post_id: int references Post(id) on_delete(cascade)
  user_id: int references User(id) on_delete(cascade)
  content: text not null
  parent_id: int nullable references Comment(id) on_delete(cascade)
  created_at: datetime default now()
  
  belongs_to Post as post
  belongs_to User as author
  belongs_to Comment as parent
  has_many Comment as replies
}

// 多对多关系
entity Tag {
  id: int primary key auto_increment
  name: string unique not null max_length(50)
  description: text nullable
  color: string nullable pattern("^#[0-9A-Fa-f]{6}$")
  
  has_many Post through PostTag as posts
}

entity PostTag {
  post_id: int references Post(id) on_delete(cascade)
  tag_id: int references Tag(id) on_delete(cascade)
  
  primary key (post_id, tag_id)
}
```

### 2.3 枚举和类型定义

```dsl
// 枚举类型定义
enum UserStatus {
  active
  inactive
  suspended
  deleted
}

enum PostType {
  article
  news
  tutorial
  review
}

// 自定义类型定义
type Email {
  string pattern("^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$")
}

type Phone {
  string pattern("^\\+?[1-9]\\d{1,14}$")
}

type URL {
  string pattern("^https?://.*")
}

// 使用自定义类型
entity Contact {
  id: int primary key auto_increment
  email: Email unique not null
  phone: Phone nullable
  website: URL nullable
}
```

## 3. 高级特性

### 3.1 继承和抽象

```dsl
// 抽象基类
abstract entity BaseEntity {
  id: int primary key auto_increment
  created_at: datetime default now()
  updated_at: datetime default now() on_update(now())
  created_by: int references User(id)
  updated_by: int references User(id)
  
  audit: true
}

// 继承
entity Product extends BaseEntity {
  name: string not null max_length(200)
  description: text nullable
  price: decimal(10,2) not null range(0, 999999.99)
  category_id: int references Category(id)
  
  belongs_to Category as category
  has_many OrderItem as order_items
}

entity Category extends BaseEntity {
  name: string not null max_length(100) unique
  description: text nullable
  parent_id: int nullable references Category(id)
  
  belongs_to Category as parent
  has_many Category as children
  has_many Product as products
}
```

### 3.2 聚合和组合

```dsl
// 聚合关系
entity Order {
  id: int primary key auto_increment
  user_id: int references User(id)
  status: enum("pending", "confirmed", "shipped", "delivered", "cancelled") default("pending")
  total_amount: decimal(10,2) not null default(0)
  created_at: datetime default now()
  
  belongs_to User as user
  has_many OrderItem as items aggregate(sum, "total_amount")
  has_one ShippingAddress as shipping_address
  has_one Payment as payment
}

entity OrderItem {
  id: int primary key auto_increment
  order_id: int references Order(id) on_delete(cascade)
  product_id: int references Product(id)
  quantity: int not null range(1, 999)
  unit_price: decimal(10,2) not null
  total_price: decimal(10,2) not null computed(quantity * unit_price)
  
  belongs_to Order as order
  belongs_to Product as product
}

// 组合关系
entity ShippingAddress {
  id: int primary key auto_increment
  order_id: int unique references Order(id) on_delete(cascade)
  recipient_name: string not null max_length(100)
  street_address: string not null max_length(200)
  city: string not null max_length(100)
  state: string not null max_length(50)
  postal_code: string not null max_length(20)
  country: string not null max_length(50)
  
  belongs_to Order as order
}
```

### 3.3 数据验证和约束

```dsl
entity Product {
  id: int primary key auto_increment
  name: string not null max_length(200)
  sku: string unique not null pattern("^[A-Z0-9]{8,12}$")
  price: decimal(10,2) not null range(0, 999999.99)
  stock_quantity: int not null default(0) range(0, 999999)
  weight_kg: decimal(5,2) nullable range(0, 999.99)
  dimensions: json nullable // {length: 10, width: 5, height: 2}
  
  // 复杂约束
  constraint chk_price_positive check (price > 0)
  constraint chk_stock_non_negative check (stock_quantity >= 0)
  constraint chk_weight_positive check (weight_kg is null or weight_kg > 0)
  constraint chk_sku_format check (sku regexp '^[A-Z0-9]{8,12}$')
  
  // 条件约束
  constraint chk_digital_product check (
    (product_type = 'digital' and weight_kg is null) or 
    (product_type != 'digital' and weight_kg is not null)
  )
  
  // 业务规则
  business_rule "stock_alert" {
    condition: "stock_quantity <= reorder_point"
    action: "send_notification"
    message: "Product {name} is running low on stock"
  }
  
  business_rule "price_change_audit" {
    condition: "price_changed"
    action: "log_audit"
    fields: ["old_price", "new_price", "changed_by"]
  }
}
```

### 3.4 索引和性能优化

```dsl
entity Order {
  id: int primary key auto_increment
  user_id: int references User(id)
  order_number: string unique not null pattern("^ORD-\\d{8}-\\d{4}$")
  status: enum("pending", "confirmed", "shipped", "delivered", "cancelled")
  total_amount: decimal(10,2) not null
  created_at: datetime default now()
  updated_at: datetime default now() on_update(now())
  
  // 基础索引
  index idx_order_user on (user_id)
  index idx_order_status on (status)
  index idx_order_created on (created_at)
  
  // 复合索引
  index idx_order_user_status on (user_id, status)
  index idx_order_status_created on (status, created_at)
  
  // 部分索引
  index idx_order_active on (user_id, created_at) where (status in ('pending', 'confirmed'))
  
  // 唯一索引
  unique index idx_order_number on (order_number)
  
  // 全文搜索索引
  fulltext idx_order_search on (order_number, notes)
  
  // 空间索引（地理位置）
  spatial index idx_order_location on (delivery_location)
  
  // 函数索引
  index idx_order_date on (date(created_at))
  index idx_order_month on (year(created_at), month(created_at))
}
```

### 3.5 权限和安全

```dsl
entity User {
  id: int primary key auto_increment
  username: string unique not null max_length(50)
  email: string unique not null
  password_hash: string not null
  role: enum("user", "moderator", "admin") default("user")
  is_active: boolean default(true)
  last_login: datetime nullable
  created_at: datetime default now()
  
  // 权限定义
  permission read: "authenticated"
  permission write: "owner or admin"
  permission delete: "admin"
  
  // 字段级权限
  field_permission password_hash: "none"
  field_permission email: "owner or admin"
  field_permission role: "admin"
  
  // 行级权限
  row_permission: "id = current_user_id or role = 'admin'"
  
  // 审计配置
  audit: true
  audit_fields: ["username", "email", "role", "is_active"]
  audit_exclude: ["password_hash"]
  
  // 数据脱敏
  mask email: "partial" // 显示前3位和后2位
  mask phone: "full" // 完全隐藏
}
```

### 3.6 数据迁移和版本控制

```dsl
// 迁移定义
migration "create_users_table" {
  version: "001"
  description: "Create users table with basic fields"
  
  up: """
    CREATE TABLE users (
      id INT PRIMARY KEY AUTO_INCREMENT,
      username VARCHAR(50) UNIQUE NOT NULL,
      email VARCHAR(255) UNIQUE NOT NULL,
      password_hash VARCHAR(255) NOT NULL,
      created_at DATETIME DEFAULT CURRENT_TIMESTAMP
    );
  """
  
  down: """
    DROP TABLE users;
  """
}

migration "add_user_profile" {
  version: "002"
  description: "Add profile fields to users table"
  
  up: """
    ALTER TABLE users 
    ADD COLUMN bio TEXT NULL,
    ADD COLUMN avatar_url VARCHAR(500) NULL,
    ADD COLUMN updated_at DATETIME DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP;
  """
  
  down: """
    ALTER TABLE users 
    DROP COLUMN bio,
    DROP COLUMN avatar_url,
    DROP COLUMN updated_at;
  """
}

// 数据填充
seed "default_users" {
  data: [
    {
      username: "admin",
      email: "admin@example.com",
      password_hash: "$2b$12$...",
      role: "admin"
    },
    {
      username: "demo",
      email: "demo@example.com", 
      password_hash: "$2b$12$...",
      role: "user"
    }
  ]
}
```

## 4. AI自动化和智能特性

### 4.1 自动字段生成

```dsl
entity Product {
  id: int primary key auto_increment
  name: string not null max_length(200)
  description: text nullable
  
  // AI自动生成字段
  ai_generated {
    seo_title: "generate_seo_title(name, description)"
    seo_description: "generate_seo_description(description)"
    tags: "extract_tags(name, description)"
    category_suggestion: "suggest_category(name, description)"
    price_suggestion: "suggest_price(category, features)"
  }
  
  // 自动计算字段
  computed {
    slug: "generate_slug(name)"
    search_vector: "to_tsvector('english', name || ' ' || coalesce(description, ''))"
    word_count: "array_length(regexp_split_to_array(description, '\\s+'), 1)"
  }
}
```

### 4.2 智能关系发现

```dsl
// AI自动发现关系
ai_discover_relationships {
  target: "Product"
  method: "semantic_analysis"
  confidence_threshold: 0.8
  
  // 自动发现的关系
  discovered_relations: [
    "Product -> Category (based on name similarity)",
    "Product -> Brand (based on name patterns)",
    "Product -> Supplier (based on historical data)"
  ]
}
```

### 4.3 性能优化建议

```dsl
// AI性能优化建议
ai_performance_optimization {
  target: "Order"
  
  suggestions: [
    "Add index on (user_id, status) for user order queries",
    "Add partial index on (status, created_at) where status in ('pending', 'confirmed')",
    "Consider partitioning by created_at for large datasets",
    "Add covering index on (user_id, status, created_at, total_amount)"
  ]
  
  auto_apply: false
  review_required: true
}
```

## 5. 与主流标准的映射

### 5.1 SQL DDL生成

```sql
-- 自动生成的SQL DDL
CREATE TABLE users (
  id INT PRIMARY KEY AUTO_INCREMENT,
  username VARCHAR(50) UNIQUE NOT NULL,
  email VARCHAR(255) UNIQUE NOT NULL,
  password_hash VARCHAR(255) NOT NULL,
  role ENUM('user', 'moderator', 'admin') DEFAULT 'user',
  is_active BOOLEAN DEFAULT TRUE,
  last_login DATETIME NULL,
  created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
  updated_at DATETIME DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  
  CONSTRAINT chk_email_format CHECK (email REGEXP '^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$')
);

CREATE INDEX idx_users_email ON users(email);
CREATE INDEX idx_users_role ON users(role);
CREATE INDEX idx_users_created ON users(created_at);
```

### 5.2 ORM模型生成

```python
# 自动生成的Python ORM模型
from sqlalchemy import Column, Integer, String, DateTime, Boolean, Enum
from sqlalchemy.ext.declarative import declarative_base

Base = declarative_base()

class User(Base):
    __tablename__ = 'users'
    
    id = Column(Integer, primary_key=True, autoincrement=True)
    username = Column(String(50), unique=True, nullable=False)
    email = Column(String(255), unique=True, nullable=False)
    password_hash = Column(String(255), nullable=False)
    role = Column(Enum('user', 'moderator', 'admin'), default='user')
    is_active = Column(Boolean, default=True)
    last_login = Column(DateTime, nullable=True)
    created_at = Column(DateTime, default=func.now())
    updated_at = Column(DateTime, default=func.now(), onupdate=func.now())
```

### 5.3 API文档生成

```yaml
# 自动生成的OpenAPI文档
openapi: 3.0.0
info:
  title: User API
  version: 1.0.0
paths:
  /users:
    get:
      summary: List users
      parameters:
        - name: page
          in: query
          schema:
            type: integer
            default: 1
        - name: limit
          in: query
          schema:
            type: integer
            default: 20
      responses:
        '200':
          description: List of users
          content:
            application/json:
              schema:
                type: array
                items:
                  $ref: '#/components/schemas/User'
    post:
      summary: Create user
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: '#/components/schemas/UserCreate'
      responses:
        '201':
          description: User created
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/User'

components:
  schemas:
    User:
      type: object
      properties:
        id:
          type: integer
        username:
          type: string
          maxLength: 50
        email:
          type: string
          format: email
        role:
          type: string
          enum: [user, moderator, admin]
        is_active:
          type: boolean
        created_at:
          type: string
          format: date-time
      required: [username, email]
```

## 6. 验证和测试

### 6.1 DSL验证器

```python
class DataModelDSLValidator:
    def validate_entity(self, entity):
        errors = []
        
        # 检查必需字段
        if not entity.get('name'):
            errors.append("Entity must have a name")
        
        # 检查字段定义
        for field in entity.get('fields', []):
            field_errors = self.validate_field(field)
            errors.extend(field_errors)
        
        # 检查约束
        for constraint in entity.get('constraints', []):
            constraint_errors = self.validate_constraint(constraint)
            errors.extend(constraint_errors)
        
        return errors
    
    def validate_field(self, field):
        errors = []
        
        if not field.get('name'):
            errors.append("Field must have a name")
        
        if not field.get('type'):
            errors.append("Field must have a type")
        
        # 检查类型特定约束
        field_type = field.get('type')
        if field_type == 'string':
            if 'max_length' in field and field['max_length'] <= 0:
                errors.append("String max_length must be positive")
        
        if field_type == 'int':
            if 'range' in field:
                min_val, max_val = field['range']
                if min_val >= max_val:
                    errors.append("Int range min must be less than max")
        
        return errors
```

### 6.2 测试用例生成

```python
# 自动生成的测试用例
import pytest
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker

class TestUserModel:
    def setup_method(self):
        self.engine = create_engine('sqlite:///:memory:')
        Base.metadata.create_all(self.engine)
        Session = sessionmaker(bind=self.engine)
        self.session = Session()
    
    def test_create_user(self):
        user = User(
            username='testuser',
            email='test@example.com',
            password_hash='hashed_password'
        )
        self.session.add(user)
        self.session.commit()
        
        assert user.id is not None
        assert user.username == 'testuser'
        assert user.email == 'test@example.com'
    
    def test_user_email_unique(self):
        user1 = User(username='user1', email='test@example.com', password_hash='hash1')
        user2 = User(username='user2', email='test@example.com', password_hash='hash2')
        
        self.session.add(user1)
        self.session.commit()
        
        with pytest.raises(Exception):  # 具体异常类型取决于数据库
            self.session.add(user2)
            self.session.commit()
    
    def test_user_role_default(self):
        user = User(username='testuser', email='test@example.com', password_hash='hash')
        assert user.role == 'user'
```

## 7. 工程实践示例

### 7.1 完整的电商数据模型

```dsl
// 电商系统完整数据模型
entity Customer {
  id: int primary key auto_increment
  email: string unique not null
  password_hash: string not null
  first_name: string not null max_length(50)
  last_name: string not null max_length(50)
  phone: string nullable pattern("^\\+?[1-9]\\d{1,14}$")
  date_of_birth: date nullable
  is_active: boolean default(true)
  created_at: datetime default now()
  updated_at: datetime default now() on_update(now())
  
  has_many Order as orders
  has_many Address as addresses
  has_many Review as reviews
  
  index idx_customer_email on (email)
  index idx_customer_active on (is_active, created_at)
  
  permission read: "authenticated"
  permission write: "owner"
  permission delete: "admin"
  
  audit: true
  audit_fields: ["email", "first_name", "last_name", "phone", "is_active"]
}

entity Product {
  id: int primary key auto_increment
  name: string not null max_length(200)
  description: text nullable
  sku: string unique not null pattern("^[A-Z0-9]{8,12}$")
  price: decimal(10,2) not null range(0, 999999.99)
  sale_price: decimal(10,2) nullable range(0, 999999.99)
  cost_price: decimal(10,2) nullable range(0, 999999.99)
  stock_quantity: int not null default(0) range(0, 999999)
  reorder_point: int not null default(10) range(0, 999999)
  category_id: int references Category(id)
  brand_id: int nullable references Brand(id)
  is_active: boolean default(true)
  created_at: datetime default now()
  updated_at: datetime default now() on_update(now())
  
  belongs_to Category as category
  belongs_to Brand as brand
  has_many OrderItem as order_items
  has_many ProductImage as images
  has_many ProductAttribute as attributes
  has_many Review as reviews
  
  index idx_product_sku on (sku)
  index idx_product_category on (category_id, is_active)
  index idx_product_brand on (brand_id, is_active)
  index idx_product_price on (price, is_active)
  index idx_product_stock on (stock_quantity, reorder_point)
  
  fulltext idx_product_search on (name, description)
  
  constraint chk_price_positive check (price > 0)
  constraint chk_sale_price_valid check (sale_price is null or sale_price <= price)
  constraint chk_stock_non_negative check (stock_quantity >= 0)
  
  business_rule "stock_alert" {
    condition: "stock_quantity <= reorder_point"
    action: "send_notification"
    message: "Product {name} is running low on stock"
  }
  
  permission read: "public"
  permission write: "admin"
  permission delete: "admin"
  
  audit: true
  audit_fields: ["name", "price", "sale_price", "stock_quantity", "is_active"]
}

entity Order {
  id: int primary key auto_increment
  order_number: string unique not null pattern("^ORD-\\d{8}-\\d{4}$")
  customer_id: int references Customer(id)
  status: enum("pending", "confirmed", "processing", "shipped", "delivered", "cancelled") default("pending")
  subtotal: decimal(10,2) not null default(0)
  tax_amount: decimal(10,2) not null default(0)
  shipping_amount: decimal(10,2) not null default(0)
  discount_amount: decimal(10,2) not null default(0)
  total_amount: decimal(10,2) not null default(0)
  payment_status: enum("pending", "paid", "failed", "refunded") default("pending")
  shipping_address_id: int references Address(id)
  billing_address_id: int references Address(id)
  notes: text nullable
  created_at: datetime default now()
  updated_at: datetime default now() on_update(now())
  
  belongs_to Customer as customer
  belongs_to Address as shipping_address
  belongs_to Address as billing_address
  has_many OrderItem as items
  has_one Payment as payment
  has_many OrderStatusHistory as status_history
  
  index idx_order_customer on (customer_id, created_at)
  index idx_order_status on (status, created_at)
  index idx_order_number on (order_number)
  index idx_order_payment on (payment_status, created_at)
  
  constraint chk_total_calculation check (total_amount = subtotal + tax_amount + shipping_amount - discount_amount)
  constraint chk_amounts_non_negative check (subtotal >= 0 and tax_amount >= 0 and shipping_amount >= 0 and discount_amount >= 0)
  
  business_rule "order_confirmation" {
    condition: "status = 'confirmed'"
    action: "send_confirmation_email"
    template: "order_confirmation"
  }
  
  business_rule "low_stock_check" {
    condition: "status = 'confirmed'"
    action: "check_stock_availability"
    on_failure: "cancel_order"
  }
  
  permission read: "owner or admin"
  permission write: "admin"
  permission delete: "admin"
  
  audit: true
  audit_fields: ["status", "total_amount", "payment_status", "notes"]
}
```

## 8. 总结

本DSL为数据建模提供了完整的形式化描述框架，支持：

- **完整的类型系统**：基础类型、自定义类型、枚举类型
- **丰富的关系系统**：一对一、一对多、多对多、继承、聚合、组合
- **强大的约束系统**：字段约束、表约束、业务规则
- **灵活的索引系统**：单列索引、复合索引、部分索引、全文索引、空间索引
- **完善的权限系统**：表级权限、字段级权限、行级权限
- **全面的审计系统**：字段审计、操作审计、变更追踪
- **智能的AI特性**：自动字段生成、关系发现、性能优化
- **标准的映射支持**：SQL DDL、ORM模型、API文档、测试用例

通过这个DSL，可以实现数据模型的统一描述、自动化生成、质量保证和持续演进，为软件工程提供强大的数据建模基础。
