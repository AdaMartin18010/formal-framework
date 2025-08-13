# 枚举建模 DSL 草案

## 概念定义

- 目标：以稳定、可扩展的方式定义离散取值集合。

## 语法示例

```yaml
enum:
  name: CountryCode
  values:
    - CN
    - US
    - JP
    - DE
  metadata:
    CN: { label: "中国" }
    US: { label: "美国" }
```

## 最佳实践

- 值使用稳定标识，显示文本置于元数据
- 通过版本与废弃标记管理演进
- 与国际化资源对齐
