# 客户关系管理（CRM）理论

## 概念定义

### CRM

客户关系管理是围绕客户全生命周期（线索→商机→合同→服务→回款）的数据与流程治理体系，目标是提升转化率、复购率与满意度。

### 核心概念

- 线索（Lead）: 尚未资格评估的潜在客户
- 商机（Opportunity）: 已确认有成交可能的销售机会
- 客户（Account/Contact）: 企业/个人客户档案
- 合同（Contract）: 与客户达成的具约束力协议
- 活动（Activity）: 拜访、电话、邮件等互动记录

## 理论基础

### 形式化建模

```yaml
crm:
  lead:
    definition: "l = (id, source, owner, score, status)"
  opportunity:
    definition: "o = (id, account, amount, stage, close_date, probability)"
  contract:
    definition: "c = (id, account, items, start, end, terms)"
```

### 公理化系统

```yaml
axioms:
  - name: "阶段有序性"
    rule: "stage transitions must follow DAG (qualification -> proposal -> negotiation -> won/lost)"
  - name: "概率单调性"
    rule: "probability(next_stage) >= probability(current)"
  - name: "审计可追溯"
    rule: "every stage change must be auditable"
```

### 类型定义（TypeScript）

```typescript
export interface Lead {
  id: string;
  source: string;
  ownerId: string;
  score: number; // 0-100
  status: 'new' | 'qualified' | 'disqualified';
}

export interface Opportunity {
  id: string;
  accountId: string;
  amount: number;
  stage: 'qualification' | 'proposal' | 'negotiation' | 'won' | 'lost';
  closeDate: string; // ISO
  probability: number; // 0-1
}

export interface Contract {
  id: string;
  accountId: string;
  items: Array<{ sku: string; qty: number; price: number }>;
  start: string;
  end: string;
  terms: string;
}
```

## 应用案例

### 案例1：销售漏斗建模

```yaml
sales_funnel:
  stages:
    - name: qualification
      entry_criteria: ["BANT完成", "线索评分>=60"]
    - name: proposal
      entry_criteria: ["需求确认", "预算初步匹配"]
    - name: negotiation
      entry_criteria: ["合同条款确认中"]
    - name: won
      entry_criteria: ["签署完成", "首付款到账"]
    - name: lost
      entry_criteria: ["无预算/无需求/竞品替代"]
```

### 案例2：预测营收报表

```yaml
forecast:
  horizon: 90d
  group_by: ["owner", "region"]
  formula: "sum(amount * probability)"
```

## 最佳实践

```yaml
best_practices:
  - name: 统一客户主数据
    description: "Account/Contact去重与主数据治理"
  - name: 资格与评分体系
    description: "MQL/SQL定义清晰，评分因子透明"
  - name: 合同条款模板
    description: "标准化条款与审批流"
  - name: 闭环数据
    description: "销售-交付-服务-回款全链路可追溯"
  - name: 隐私与合规
    description: "GDPR/CCPA合规，最小化数据持有"
```

## 开源项目映射

- Odoo, ERPNext, SuiteCRM

## 相关链接

- 内部: `docs/industry-model/enterprise-management-model/theory.md`
- 内部: `docs/industry-model/business-model/sales-model/theory.md`
- 外部: `https://www.odoo.com/`, `https://erpnext.com/`

## 总结

CRM以数据驱动与流程驱动协同，借助形式化建模与可审计约束实现可度量、可优化的增长引擎。
