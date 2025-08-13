# 复合类型建模 DSL 草案

## 概念定义

- 目标：定义由多个基本类型/枚举/约束组合而成的复合类型结构。

## 语法示例

```yaml
composite_type:
  name: "Address"
  fields:
    - name: country
      type: string
      constraints:
        - not_empty
    - name: city
      type: string
    - name: zipcode
      type: string
      constraints:
        - regex: "^[0-9]{5}$"
    - name: lines
      type: array<string>
      min_items: 1
```

## 最佳实践

- 明确字段可空性与默认值
- 复用基础类型与枚举
- 使用约束提升数据质量
