# 迁移建模DSL草案（递归扩展版）

## 1. 设计目标

- 用统一DSL描述数据库迁移操作、版本、依赖、回滚、批量迁移、数据填充等要素。
- 支持自动生成Flyway、Liquibase、Alembic等主流迁移脚本，适配多种数据库。
- 支持权限、安全、审计、AI自动化等高级特性。

## 2. 基本语法结构

```dsl
migration V20230601_add_user {
  up {
    create_table User {
      id: int primary key auto_increment
      name: string not null
      email: string unique
    }
    seed_data User [
      { name: "张三", email: "zhangsan@example.com" },
      { name: "李四", email: "lisi@example.com" }
    ]
  }
  down {
    drop_table User
  }
  author: "张三"
  date: "2023-06-01"
  description: "新增用户表并填充初始数据"
  permission: "db_admin"
  audit: true
}

migration V20230602_add_age_to_user {
  up {
    add_column User.age int
    update_data User set age = 18 where age is null
  }
  down {
    drop_column User.age
  }
  depends_on: ["V20230601_add_user"]
  author: "李四"
  date: "2023-06-02"
  description: "用户表新增年龄字段并补全数据"
}
```

## 3. 关键元素

- migration：迁移声明
- up/down：升级/回滚操作
- depends_on：依赖迁移
- batch：批量迁移单元
- seed_data/update_data：数据填充与批量更新
- author/date/description/permission/audit：元信息与安全

## 4. 高级用法与递归扩展

### 4.1 批量迁移与依赖管理

```dsl
batch 20240601_batch {
  migrations: [
    V20240601_add_user,
    V20240602_add_order,
    V20240603_add_index
  ]
  description: "六月第一批数据库结构变更"
  permission: "db_admin"
}
```

### 4.2 复杂依赖与回滚

```dsl
migration V20240604_add_foreign_key {
  up {
    add_foreign_key Order.product_id references Product(id)
  }
  down {
    drop_foreign_key Order.product_id
  }
  depends_on: ["V20240602_add_order", "V20240603_add_product"]
  description: "订单表增加产品外键约束"
}
```

### 4.3 数据填充与变更

```dsl
migration V20240605_seed_products {
  up {
    seed_data Product [
      { name: "商品A", price: 100 },
      { name: "商品B", price: 200 }
    ]
  }
  down {
    delete_data Product where name in ["商品A", "商品B"]
  }
  description: "批量填充商品数据"
}
```

### 4.4 权限与安全声明

```dsl
migration V20240606_sensitive_change {
  up {
    alter_column User.ssn string encrypted
  }
  down {
    alter_column User.ssn string
  }
  permission: "security_audit"
  audit: true
  description: "用户敏感信息加密"
}
```

### 4.5 AI自动化与智能迁移建议

```dsl
# 支持AI自动生成迁移脚本
ai_migration "为User表增加手机号字段，要求唯一且自动补全历史数据" {
  target: User
  field: phone
  unique: true
  auto_fill: "随机生成"
}
```

## 5. 与主流标准的映射

- 可自动转换为Flyway、Liquibase、Alembic等迁移脚本
- 支持与主流ORM、数据库工具集成
- 支持权限、安全、审计策略自动生成

## 6. 递归扩展建议

- 支持复杂依赖、批量迁移、数据填充、数据脱敏、权限与安全校验
- 支持AI自动生成与优化迁移脚本
- 支持多数据库、分布式迁移、变更影响分析
- 支持迁移回滚、变更追踪、自动补偿

## 7. 工程实践示例

```dsl
batch 20240610_big_update {
  migrations: [
    V20240610_add_table_a,
    V20240611_add_table_b,
    V20240612_add_relation_ab
  ]
  permission: "db_admin"
  audit: true
  description: "六月中旬大批量结构升级"
}
```

---
