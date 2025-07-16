# 版本建模DSL草案

## 1. 设计目标

- 用统一DSL描述版本号、变更记录、依赖、发布与回滚等要素。
- 支持自动生成Git标签、Docker镜像、Helm Chart等版本配置。

## 2. 基本语法结构

```dsl
version release_1_2_3 {
  number: "1.2.3"
  changelog: "修复若干bug"
  date: "2024-05-01"
  author: "张三"
  dependencies: ["libA@1.0.0", "libB@2.1.0"]
}

version snapshot_20240601 {
  number: "20240601.1234"
  changelog: "每日构建快照"
  dependencies: ["libA@1.0.0"]
}

release gray_release {
  base: "1.2.3"
  strategy: "canary"
  percent: 10
}
```

## 3. 关键元素

- version/release：版本与发布声明
- number/changelog/date/author/dependencies：版本号、变更、作者、依赖
- strategy/percent：发布策略

## 4. 常用版本声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| version release_1_2_3 { ... }                | 语义化版本声明 |
| number: "1.2.3"                              | 版本号         |
| changelog: "修复bug"                          | 变更记录       |
| dependencies: ["libA@1.0.0"]                 | 依赖声明       |
| release gray_release { ... }                  | 灰度发布声明   |
| strategy: "canary"                           | 发布策略       |

## 5. 与主流标准的映射

- 可自动转换为Git标签、Docker镜像、Helm Chart等配置
- 支持与主流CI/CD、包管理工具集成

## 6. 递归扩展建议

- 支持多环境版本、依赖冲突检测、自动回滚
- 支持变更审计、发布策略多样化
