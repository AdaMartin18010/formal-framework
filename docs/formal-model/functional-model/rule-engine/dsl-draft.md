# 规则引擎建模DSL草案

## 1. 设计目标

- 用统一DSL描述规则、条件、动作、优先级、规则集等要素。
- 支持自动生成Drools、Jess、DMN等规则引擎配置。

## 2. 基本语法结构

```dsl
rule DiscountRule {
  when order.amount > 1000
  then order.discount = 0.1
  priority: 10
}

rule VIPRule {
  when user.level == "VIP"
  then order.discount = 0.2
  priority: 20
}

ruleset OrderRules {
  include: [DiscountRule, VIPRule]
}
```

decision_table PriceTable {
  columns: [amount, level, discount]
  rows:
    - [>1000, "VIP", 0.25]
    - [>1000, "普通", 0.1]
    - [<=1000, "VIP", 0.2]
    - [<=1000, "普通", 0.0]
}

## 3. 关键元素

- rule：规则声明
- when/then：条件与动作
- priority：优先级
- ruleset：规则集
- decision_table：决策表

## 4. 常用规则声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| rule DiscountRule { ... }                     | 单条规则       |
| ruleset OrderRules { ... }                    | 规则集         |
| decision_table PriceTable { ... }             | 决策表         |
| priority: 10                                  | 优先级声明     |
| include: [RuleA, RuleB]                       | 规则集包含     |

## 5. 与主流标准的映射

- 可自动转换为Drools、Jess、DMN等规则引擎配置
- 支持与主流规则引擎集成

## 6. 递归扩展建议

- 支持复杂条件、嵌套规则、推理链
- 支持规则冲突检测与优化建议
