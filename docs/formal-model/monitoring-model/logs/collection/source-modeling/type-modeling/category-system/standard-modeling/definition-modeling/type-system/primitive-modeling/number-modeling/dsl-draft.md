# 数值原语类型 DSL 草案

## 概念定义

- 目标：定义整数/小数的精度、范围与计量单位。

## 语法示例

```yaml
number:
  name: amount
  kind: decimal
  precision: 18
  scale: 2
  unit: CNY
  constraints:
    - min: 0
    - max: 100000000
```

## 最佳实践

- 为财务金额指定精度与舍入规则
- 明确单位与换算
