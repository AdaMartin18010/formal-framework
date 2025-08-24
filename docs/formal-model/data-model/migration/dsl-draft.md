# 数据迁移建模DSL草案

## 1. 设计目标

- 用统一DSL描述数据迁移的版本管理、变更操作、回滚策略等要素
- 支持自动生成数据库迁移脚本、版本控制、部署工具等
- 支持权限、安全、审计、AI自动化等高级特性

## 2. 基本语法结构

```dsl
migration "create_users_table" {
  version: "001"
  description: "创建用户表"
  author: "system"
  timestamp: "2024-01-01T00:00:00Z"
  
  up: [
    {
      type: "create_table"
      table: "users"
      columns: [
        { name: "id", type: "INT", primary_key: true, auto_increment: true },
        { name: "username", type: "VARCHAR(50)", unique: true, not_null: true },
        { name: "email", type: "VARCHAR(255)", unique: true, not_null: true },
        { name: "password_hash", type: "VARCHAR(255)", not_null: true },
        { name: "created_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP" },
        { name: "updated_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP" }
      ]
    },
    {
      type: "create_index"
      table: "users"
      name: "idx_users_email"
      columns: ["email"]
    }
  ]
  
  down: [
    {
      type: "drop_table"
      table: "users"
    }
  ]
  
  dependencies: []
  rollback_strategy: "drop_table"
}
```

## 3. 关键元素

- migration：迁移声明
- version：版本号
- description：描述信息
- author：作者
- timestamp：时间戳
- up：升级操作
- down：回滚操作
- dependencies：依赖关系
- rollback_strategy：回滚策略

## 4. 高级用法

### 4.1 复杂表结构迁移

```dsl
migration "create_ecommerce_schema" {
  version: "002"
  description: "创建电商系统数据库结构"
  author: "system"
  timestamp: "2024-01-02T00:00:00Z"
  
  up: [
    {
      type: "create_table"
      table: "products"
      columns: [
        { name: "id", type: "INT", primary_key: true, auto_increment: true },
        { name: "name", type: "VARCHAR(200)", not_null: true },
        { name: "description", type: "TEXT" },
        { name: "price", type: "DECIMAL(10,2)", not_null: true },
        { name: "category_id", type: "INT", not_null: true },
        { name: "status", type: "ENUM('draft','active','inactive')", default: "draft" },
        { name: "created_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP" },
        { name: "updated_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP" }
      ]
    },
    {
      type: "create_table"
      table: "categories"
      columns: [
        { name: "id", type: "INT", primary_key: true, auto_increment: true },
        { name: "name", type: "VARCHAR(100)", not_null: true },
        { name: "parent_id", type: "INT" },
        { name: "created_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP" }
      ]
    },
    {
      type: "create_foreign_key"
      table: "products"
      name: "fk_products_category"
      columns: ["category_id"]
      references: { table: "categories", columns: ["id"] }
      on_delete: "RESTRICT"
      on_update: "CASCADE"
    },
    {
      type: "create_index"
      table: "products"
      name: "idx_products_category_status"
      columns: ["category_id", "status"]
    }
  ]
  
  down: [
    {
      type: "drop_foreign_key"
      table: "products"
      name: "fk_products_category"
    },
    {
      type: "drop_table"
      table: "products"
    },
    {
      type: "drop_table"
      table: "categories"
    }
  ]
  
  dependencies: ["001"]
  rollback_strategy: "transaction"
}
```

### 4.2 数据迁移操作

```dsl
migration "migrate_user_data" {
  version: "003"
  description: "迁移用户数据到新结构"
  author: "system"
  timestamp: "2024-01-03T00:00:00Z"
  
  up: [
    {
      type: "add_column"
      table: "users"
      column: { name: "phone", type: "VARCHAR(20)" }
    },
    {
      type: "add_column"
      table: "users"
      column: { name: "address", type: "TEXT" }
    },
    {
      type: "update_data"
      table: "users"
      set: { phone: "NULL", address: "NULL" }
      where: "phone IS NULL OR address IS NULL"
    },
    {
      type: "create_index"
      table: "users"
      name: "idx_users_phone"
      columns: ["phone"]
    }
  ]
  
  down: [
    {
      type: "drop_index"
      table: "users"
      name: "idx_users_phone"
    },
    {
      type: "drop_column"
      table: "users"
      column: "address"
    },
    {
      type: "drop_column"
      table: "users"
      column: "phone"
    }
  ]
  
  dependencies: ["002"]
  rollback_strategy: "transaction"
  data_migration: {
    backup_required: true
    validation_required: true
    batch_size: 1000
  }
}
```

### 4.3 分阶段迁移

```dsl
migration "large_table_migration" {
  version: "004"
  description: "大表分阶段迁移"
  author: "system"
  timestamp: "2024-01-04T00:00:00Z"
  
  up: [
    {
      type: "create_table"
      table: "orders_new"
      columns: [
        { name: "id", type: "BIGINT", primary_key: true, auto_increment: true },
        { name: "user_id", type: "INT", not_null: true },
        { name: "total_amount", type: "DECIMAL(12,2)", not_null: true },
        { name: "status", type: "ENUM('pending','confirmed','shipped','delivered','cancelled')", default: "pending" },
        { name: "created_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP" },
        { name: "updated_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP" }
      ]
    },
    {
      type: "create_index"
      table: "orders_new"
      name: "idx_orders_user_status"
      columns: ["user_id", "status"]
    },
    {
      type: "migrate_data_in_batches"
      source_table: "orders"
      target_table: "orders_new"
      batch_size: 10000
      where: "id > 0"
      columns_mapping: {
        "id": "id",
        "user_id": "user_id",
        "amount": "total_amount",
        "order_status": "status",
        "created_at": "created_at",
        "updated_at": "updated_at"
      }
    }
  ]
  
  down: [
    {
      type: "drop_table"
      table: "orders_new"
    }
  ]
  
  dependencies: ["003"]
  rollback_strategy: "drop_table"
  performance: {
    estimated_duration: "2h"
    maintenance_window_required: true
    downtime_minimal: true
  }
}
```

### 4.4 条件迁移

```dsl
migration "conditional_schema_update" {
  version: "005"
  description: "条件性架构更新"
  author: "system"
  timestamp: "2024-01-05T00:00:00Z"
  
  up: [
    {
      type: "conditional_operation"
      condition: "table_exists('old_products')"
      operations: [
        {
          type: "rename_table"
          old_name: "old_products"
          new_name: "products_backup"
        },
        {
          type: "create_table"
          table: "products"
          columns: [
            { name: "id", type: "INT", primary_key: true, auto_increment: true },
            { name: "name", type: "VARCHAR(200)", not_null: true },
            { name: "price", type: "DECIMAL(10,2)", not_null: true }
          ]
        },
        {
          type: "migrate_data"
          source_table: "products_backup"
          target_table: "products"
          columns_mapping: {
            "id": "id",
            "product_name": "name",
            "product_price": "price"
          }
        }
      ]
    }
  ]
  
  down: [
    {
      type: "conditional_operation"
      condition: "table_exists('products_backup')"
      operations: [
        {
          type: "drop_table"
          table: "products"
        },
        {
          type: "rename_table"
          old_name: "products_backup"
          new_name: "old_products"
        }
      ]
    }
  ]
  
  dependencies: ["004"]
  rollback_strategy: "conditional"
  validation: {
    pre_migration: [
      "check_table_exists('old_products')",
      "validate_data_integrity('old_products')"
    ]
    post_migration: [
      "check_table_exists('products')",
      "validate_data_count('products', 'products_backup')"
    ]
  }
}
```

## 5. 代码生成模板

### 5.1 SQL迁移脚本生成

```sql
-- Migration: 001_create_users_table
-- Version: 001
-- Description: 创建用户表
-- Author: system
-- Timestamp: 2024-01-01T00:00:00Z

-- UP Migration
CREATE TABLE users (
  id INT PRIMARY KEY AUTO_INCREMENT,
  username VARCHAR(50) UNIQUE NOT NULL,
  email VARCHAR(255) UNIQUE NOT NULL,
  password_hash VARCHAR(255) NOT NULL,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP
);

CREATE INDEX idx_users_email ON users(email);

-- DOWN Migration
-- DROP TABLE users;
```

### 5.2 版本控制脚本生成

```python
# migration_001_create_users_table.py
import sqlite3
from datetime import datetime

class Migration001CreateUsersTable:
    version = "001"
    description = "创建用户表"
    author = "system"
    timestamp = "2024-01-01T00:00:00Z"
    
    def up(self, connection):
        cursor = connection.cursor()
        
        # Create users table
        cursor.execute("""
            CREATE TABLE users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE NOT NULL,
                email TEXT UNIQUE NOT NULL,
                password_hash TEXT NOT NULL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)
        
        # Create index
        cursor.execute("""
            CREATE INDEX idx_users_email ON users(email)
        """)
        
        connection.commit()
    
    def down(self, connection):
        cursor = connection.cursor()
        
        # Drop index
        cursor.execute("DROP INDEX IF EXISTS idx_users_email")
        
        # Drop table
        cursor.execute("DROP TABLE IF EXISTS users")
        
        connection.commit()
```

### 5.3 部署脚本生成

```bash
#!/bin/bash
# deploy_migration_001.sh

MIGRATION_VERSION="001"
MIGRATION_NAME="create_users_table"
DATABASE_URL="mysql://user:pass@localhost/mydb"

echo "Starting migration $MIGRATION_VERSION: $MIGRATION_NAME"

# Backup database
echo "Creating backup..."
mysqldump -u user -p mydb > backup_${MIGRATION_VERSION}_$(date +%Y%m%d_%H%M%S).sql

# Check if migration already applied
if mysql -u user -p -e "SELECT 1 FROM migration_history WHERE version = '$MIGRATION_VERSION'" mydb 2>/dev/null; then
    echo "Migration $MIGRATION_VERSION already applied"
    exit 0
fi

# Apply migration
echo "Applying migration..."
mysql -u user -p mydb << EOF
START TRANSACTION;

-- Migration UP operations
CREATE TABLE users (
  id INT PRIMARY KEY AUTO_INCREMENT,
  username VARCHAR(50) UNIQUE NOT NULL,
  email VARCHAR(255) UNIQUE NOT NULL,
  password_hash VARCHAR(255) NOT NULL,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP
);

CREATE INDEX idx_users_email ON users(email);

-- Record migration
INSERT INTO migration_history (version, name, applied_at) 
VALUES ('$MIGRATION_VERSION', '$MIGRATION_NAME', NOW());

COMMIT;
EOF

if [ $? -eq 0 ]; then
    echo "Migration $MIGRATION_VERSION applied successfully"
else
    echo "Migration $MIGRATION_VERSION failed"
    exit 1
fi
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - migration.name
    - migration.version
    - migration.description
    - migration.up
    - migration.down
  
  type_constraints:
    - field: "migration.version"
      type: "string"
      pattern: "^[0-9]{3}$"
    - field: "migration.up"
      type: "array"
      min_items: 1
    - field: "migration.down"
      type: "array"
      min_items: 1
  
  business_rules:
    - rule: "migration version must be unique"
    - rule: "up and down operations must be reversible"
    - rule: "dependencies must reference valid migration versions"
```

### 6.2 迁移验证规则

```yaml
migration_validation:
  operation_consistency:
    - rule: "create_table operations must have corresponding drop_table in down"
    - rule: "add_column operations must have corresponding drop_column in down"
    - rule: "create_index operations must have corresponding drop_index in down"
  
  dependency_validation:
    - rule: "migration dependencies must be applied in correct order"
    - rule: "circular dependencies are not allowed"
    - rule: "all dependencies must exist"
  
  data_integrity:
    - rule: "data migrations must preserve referential integrity"
    - rule: "column type changes must be compatible"
    - rule: "not null constraints must be added after data migration"
```

## 7. 最佳实践

### 7.1 迁移设计模式

```dsl
# 表创建模式
migration "table_creation_pattern" {
  version: "001"
  description: "创建基础表结构"
  
  up: [
    {
      type: "create_table"
      table: "entity"
      columns: [
        { name: "id", type: "INT", primary_key: true, auto_increment: true },
        { name: "created_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP" },
        { name: "updated_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP" }
      ]
    }
  ]
  
  down: [
    {
      type: "drop_table"
      table: "entity"
    }
  ]
  
  rollback_strategy: "drop_table"
}

# 数据迁移模式
migration "data_migration_pattern" {
  version: "002"
  description: "数据迁移操作"
  
  up: [
    {
      type: "add_column"
      table: "entity"
      column: { name: "new_field", type: "VARCHAR(100)" }
    },
    {
      type: "update_data"
      table: "entity"
      set: { new_field: "default_value" }
      where: "new_field IS NULL"
    }
  ]
  
  down: [
    {
      type: "drop_column"
      table: "entity"
      column: "new_field"
    }
  ]
  
  rollback_strategy: "transaction"
  data_migration: {
    backup_required: true
    validation_required: true
  }
}
```

### 7.2 迁移命名规范

```dsl
# 推荐命名模式
migration "001_create_entity_table" {
  # 版本号_操作_对象
}

migration "002_add_field_to_entity" {
  # 版本号_操作_对象
}

migration "003_migrate_entity_data" {
  # 版本号_操作_对象
}
```

## 8. 与主流标准的映射

| DSL元素 | Flyway | Liquibase | Alembic | Rails |
|---------|--------|-----------|---------|-------|
| migration | migration | changeSet | revision | migration |
| version | version | id | revision | version |
| up | up | changes | upgrade | up |
| down | down | rollback | downgrade | down |
| dependencies | dependsOn | dependsOn | depends_on | dependencies |

## 9. 工程实践示例

```dsl
# 电商系统迁移示例
migration "001_create_ecommerce_schema" {
  version: "001"
  description: "创建电商系统基础架构"
  author: "system"
  timestamp: "2024-01-01T00:00:00Z"
  
  up: [
    {
      type: "create_table"
      table: "users"
      columns: [
        { name: "id", type: "INT", primary_key: true, auto_increment: true },
        { name: "username", type: "VARCHAR(50)", unique: true, not_null: true },
        { name: "email", type: "VARCHAR(255)", unique: true, not_null: true },
        { name: "password_hash", type: "VARCHAR(255)", not_null: true },
        { name: "created_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP" },
        { name: "updated_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP" }
      ]
    },
    {
      type: "create_table"
      table: "products"
      columns: [
        { name: "id", type: "INT", primary_key: true, auto_increment: true },
        { name: "name", type: "VARCHAR(200)", not_null: true },
        { name: "price", type: "DECIMAL(10,2)", not_null: true },
        { name: "category_id", type: "INT", not_null: true },
        { name: "created_at", type: "TIMESTAMP", default: "CURRENT_TIMESTAMP" }
      ]
    },
    {
      type: "create_foreign_key"
      table: "products"
      name: "fk_products_category"
      columns: ["category_id"]
      references: { table: "categories", columns: ["id"] }
    }
  ]
  
  down: [
    {
      type: "drop_foreign_key"
      table: "products"
      name: "fk_products_category"
    },
    {
      type: "drop_table"
      table: "products"
    },
    {
      type: "drop_table"
      table: "users"
    }
  ]
  
  dependencies: []
  rollback_strategy: "transaction"
}

migration "002_add_user_profile" {
  version: "002"
  description: "添加用户档案信息"
  author: "system"
  timestamp: "2024-01-02T00:00:00Z"
  
  up: [
    {
      type: "add_column"
      table: "users"
      column: { name: "phone", type: "VARCHAR(20)" }
    },
    {
      type: "add_column"
      table: "users"
      column: { name: "address", type: "TEXT" }
    },
    {
      type: "create_index"
      table: "users"
      name: "idx_users_phone"
      columns: ["phone"]
    }
  ]
  
  down: [
    {
      type: "drop_index"
      table: "users"
      name: "idx_users_phone"
    },
    {
      type: "drop_column"
      table: "users"
      column: "address"
    },
    {
      type: "drop_column"
      table: "users"
      column: "phone"
    }
  ]
  
  dependencies: ["001"]
  rollback_strategy: "transaction"
}
```

这个DSL设计为数据迁移建模提供了完整的配置语言，支持从简单的表创建到复杂的数据迁移的各种需求，同时保持了良好的可扩展性和可维护性。
