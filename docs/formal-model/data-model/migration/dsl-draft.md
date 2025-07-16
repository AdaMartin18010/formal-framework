# 迁移建模DSL草案

## 1. 设计目标

- 用统一DSL描述数据库迁移操作、版本、依赖、回滚等要素。
- 支持自动生成Flyway、Liquibase、Alembic等主流迁移脚本。

## 2. 基本语法结构

```dsl
migration V20230601_add_user {
  up {
    create_table User {
      id: int primary key auto_increment
      name: string not null
      email: string unique
    }
  }
  down {
    drop_table User
  }
  author: "张三"
  date: "2023-06-01"
  description: "新增用户表"
}

migration V20230602_add_age_to_user {
  up {
    add_column User.age int
  }
  down {
    drop_column User.age
  }
  depends_on: ["V20230601_add_user"]
  author: "李四"
  date: "2023-06-02"
  description: "用户表新增年龄字段"
}
```

## 3. 关键元素

- migration：迁移声明
- up/down：升级/回滚操作
- depends_on：依赖迁移
- author/date/description：元信息

## 4. 常用迁移操作一览（表格）

| 操作类型      | 语法示例                        | 说明           |
|---------------|---------------------------------|----------------|
| 创建表        | create_table User { ... }        | 新建数据表     |
| 删除表        | drop_table User                  | 删除数据表     |
| 增加字段      | add_column User.age int          | 表新增字段     |
| 删除字段      | drop_column User.age             | 表删除字段     |
| 增加索引      | add_index idx_user_email on User(email) | 新建索引 |
| 删除索引      | drop_index idx_user_email        | 删除索引       |

## 5. 与主流标准的映射

- 可自动转换为Flyway、Liquibase、Alembic等迁移脚本
- 支持与主流ORM、数据库工具集成

## 6. 递归扩展建议

- 支持复杂依赖、批量迁移、数据填充
- 支持迁移脚本自动生成与回滚策略
