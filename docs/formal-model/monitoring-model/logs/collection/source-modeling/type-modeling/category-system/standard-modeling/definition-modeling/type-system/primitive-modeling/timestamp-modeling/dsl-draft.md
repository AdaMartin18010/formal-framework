# 时间戳原语类型 DSL 草案

## 概念定义

- 目标：统一时间字段的时区、精度与合法区间。

## 语法示例

```yaml
timestamp:
  name: created_at
  timezone: "+08:00"
  precision: milliseconds
  constraints:
    - not_future: true
    - after: "1970-01-01T00:00:00Z"
```

## 最佳实践

- 统一UTC存储、本地化展示
- 指定时间精度，避免歧义
