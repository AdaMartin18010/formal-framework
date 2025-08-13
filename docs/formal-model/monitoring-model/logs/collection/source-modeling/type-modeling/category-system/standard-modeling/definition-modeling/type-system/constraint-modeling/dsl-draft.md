# 约束建模 DSL 草案

## 概念定义

- 目标：以声明式方式为类型定义校验约束（范围、长度、模式、唯一性等）。

## 语法示例

```yaml
constraints:
  - target: user.age
    rules:
      - min: 0
      - max: 150
  - target: user.email
    rules:
      - format: email
      - unique: true
  - target: order.items
    rules:
      - min_items: 1
```

## 最佳实践

- 将业务规则与数据模型分离
- 分层约束（字段级、对象级、跨对象）
- 为错误信息定义可本地化提示
