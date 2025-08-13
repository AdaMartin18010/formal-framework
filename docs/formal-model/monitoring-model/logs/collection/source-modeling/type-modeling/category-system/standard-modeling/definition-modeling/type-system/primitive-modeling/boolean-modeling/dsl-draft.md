# 布尔原语类型 DSL 草案

## 概念定义

- 目标：定义布尔型字段的业务语义与约束。

## 语法示例

```yaml
boolean:
  name: is_active
  default: true
  semantics: "资源是否处于激活态"
  constraints:
    - immutable_when: status in ["archived"]
```

## 最佳实践

- 明确默认值与状态机关系
- 避免三态布尔，必要时使用枚举
