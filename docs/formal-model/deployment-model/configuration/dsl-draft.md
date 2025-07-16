# 配置建模DSL草案

## 1. 设计目标

- 用统一DSL描述环境变量、配置文件、密钥、动态加载等配置要素。
- 支持自动生成K8s ConfigMap/Secret、Spring Cloud Config等配置。

## 2. 基本语法结构

```dsl
config app_config {
  env: {
    APP_ENV: "production"
    LOG_LEVEL: "info"
  }
  file: "config.yaml"
  secrets: ["DB_PASSWORD"]
  dynamic: true
  environments: ["dev", "test", "prod"]
}

secret db_secret {
  key: "DB_PASSWORD"
  value: "s3cr3t"
  encrypted: true
}
```

## 3. 关键元素

- config/secret：配置与密钥声明
- env/file/secrets/dynamic/environments：环境变量、文件、密钥、动态、环境
- key/value/encrypted：密钥属性

## 4. 常用配置声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| config app_config { ... }                     | 配置声明       |
| env: { ... }                                 | 环境变量       |
| file: "config.yaml"                          | 配置文件       |
| secrets: ["DB_PASSWORD"]                     | 密钥依赖       |
| dynamic: true                                | 动态加载       |
| environments: ["dev", "prod"]                | 多环境         |
| secret db_secret { ... }                      | 密钥声明       |
| key/value/encrypted                           | 密钥属性       |

## 5. 与主流标准的映射

- 可自动转换为K8s ConfigMap/Secret、Spring Cloud Config等配置
- 支持与主流配置管理与密钥管理工具集成

## 6. 递归扩展建议

- 支持多层级、模板化、动态变更
- 支持配置依赖、变更追踪与安全审计
