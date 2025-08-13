# 支付网关理论

## 概念定义

### 支付网关

支付网关是商户系统与多支付渠道（卡组织、钱包、银行）之间的中介层，提供收单、清算结算、风控合规、对账等能力。

### 核心概念

- 支付意图（Payment Intent）
- 支付方法（Payment Method）
- 风控规则（Risk Rules）
- 清算结算（Clearing & Settlement）

## 理论基础

### 形式化建模

```yaml
payment_gateway:
  intent:
    definition: "pi = (id, amount, currency, method, status, metadata)"
  risk:
    definition: "r = (rules, score, decision)"
  clearing:
    definition: "c = (cycle, fee, scheme, net, payable)"
```

### 公理化系统

```yaml
axioms:
  - name: 金额守恒
    rule: "auth_amount >= capture_amount >= refund_amount >= 0"
  - name: 风控先决
    rule: "risk.decision must be PASS before capture"
  - name: 对账平衡
    rule: "sum(payouts) + fees = net_receivable"
  - name: 合规模型
    rule: "kyc/aml checks must pass for high-risk profiles"
```

### 类型安全与配置示例

```yaml
# Stripe 风格配置（抽象）
merchant:
  id: m_123
  methods: ["card", "alipay", "wechat"]
  webhooks:
    - event: payment_intent.succeeded
      url: https://merchant.example.com/webhooks/stripe
risk:
  rules:
    - name: high_amount
      when: amount > 10000 && country in ["US", "EU"]
      action: MANUAL_REVIEW
    - name: velocity
      when: count(user_id, 10m) > 5
      action: DECLINE
clearing:
  cycle: D+1
  fee:
    scheme: interchange++
    value: 2.9% + $0.3
```

## 应用案例

### 案例1：多渠道路由与降级

```yaml
smart_routing:
  prefer: ["stripe", "adyen", "paypal"]
  rules:
    - when: issuer = "CN" && method = "card"
      route: adyen
    - when: method = "wallet"
      route: paypal
    - when: gateway.unavailable
      fallback: next
```

### 案例2：分账与结算

```yaml
split_settlement:
  order: o_123
  splits:
    - party: supplier
      amount: 70%
    - party: platform
      amount: 30%
  settlement: D+1
```

## 最佳实践

```yaml
best_practices:
  - name: PCI-DSS合规
    description: "使用令牌化与合规托管，减少卡数据暴露"
  - name: 分层风控
    description: "静态规则+机器学习+人工复核"
  - name: 幂等与重试
    description: "请求幂等键+幂等回调处理"
  - name: Webhook安全
    description: "签名校验、重放防护、重试策略"
  - name: 对账自动化
    description: "平台账与渠道账差异自动对齐与告警"
```

## 开源/平台映射

- Stripe, Adyen, PayPal, Braintree

## 相关链接

- 内部: `docs/industry-model/finance-architecture/theory.md`
- 外部: `https://stripe.com/docs`, `https://docs.adyen.com/`, `https://developer.paypal.com/`

## 总结

支付网关通过策略化路由、分层风控与自动化清结算，确保支付的安全、合规与高可用。形式化建模与公理化约束可显著提升可验证性与可运维性。
