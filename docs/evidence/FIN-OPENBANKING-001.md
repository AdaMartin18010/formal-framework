---
id: evidence:FIN-OPENBANKING-001
title: 英国开放银行API实施案例
version: V1.0
status: final
category: 应用
source: 英国开放银行标准
credibility: A
---

## 1. 基本信息

- **分类**：应用
- **来源**：英国开放银行标准
- **可信度**：A（权威行业标准）
- **版本**：Open Banking UK v3.1
- **发布日期**：2023-03-15

## 2. 摘要

英国开放银行是开放银行标准的典型实施案例，通过API开放银行数据和服务，实现了银行与第三方服务提供商之间的安全数据共享。
本案例展示了开放银行API的设计、实施、安全和合规要求，为金融行业的开放银行建设提供了重要的参考价值。

## 3. 对齐维度

### 3.1 术语对齐

- **Open Banking API** ↔ `L3_D01_交互标准模型.md` RESTfulAPI
- **Consent Management** ↔ `L3_D01_交互标准模型.md` 授权管理
- **PSD2 Compliance** ↔ `L3_D08_测试标准模型.md` 合规测试
- **Strong Customer Authentication** ↔ `L3_D01_交互标准模型.md` 强客户认证
- **Account Information Service** ↔ `L3_D02_数据标准模型.md` 账户信息服务

### 3.2 结构/接口对齐

- **开放银行接口** ↔ `L3_D01_交互标准模型.md` OpenBankingAPI
- **授权管理接口** ↔ `L3_D01_交互标准模型.md` ConsentManagementAPI
- **账户信息接口** ↔ `L3_D02_数据标准模型.md` AccountInformationAPI
- **支付发起接口** ↔ `L3_D01_交互标准模型.md` PaymentInitiationAPI

### 3.3 约束/不变式对齐

- **数据保护约束** ↔ `L3_D01_交互标准模型.md` DataProtectionConstraint
- **安全认证约束** ↔ `L3_D01_交互标准模型.md` SecurityAuthenticationConstraint
- **合规性约束** ↔ `L3_D08_测试标准模型.md` ComplianceConstraint
- **API一致性约束** ↔ `L3_D01_交互标准模型.md` APIConsistencyConstraint

### 3.4 度量/指标对齐

- **API可用性** ↔ `L3_D06_监控标准模型.md` APIAvailability
- **响应时间** ↔ `L3_D06_监控标准模型.md` ResponseTime
- **安全事件率** ↔ `L3_D06_监控标准模型.md` SecurityIncidentRate
- **合规检查通过率** ↔ `L3_D08_测试标准模型.md` ComplianceCheckPassRate

## 4. 映射

### 4.1 L2映射

- **L2_D01_交互元模型.md**：API接口、消息格式、协议标准
- **L2_D02_数据元模型.md**：账户数据、交易数据、客户数据
- **L2_D08_测试元模型.md**：合规测试、安全测试、功能测试
- **L2_D05_部署元模型.md**：API部署、配置管理、版本控制

### 4.2 L3映射

- **L3_D01_交互标准模型.md**：开放银行API标准、安全认证标准
- **L3_D02_数据标准模型.md**：账户数据标准、数据保护标准
- **L3_D08_测试标准模型.md**：合规测试标准、安全测试标准
- **L3_D05_部署标准模型.md**：API部署标准、配置管理标准

### 4.3 L4映射

- **L4_D91_FIN_行业索引与对标.md**：金融行业标准对标
- **industry-model/finance-architecture/README.md**：金融架构案例

## 5. 引用

### 5.1 原文链接

- **英国开放银行标准**：<https://standards.openbanking.org.uk/>
- **PSD2指令**：<https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32015L2366>
- **FCA监管指南**：<https://www.fca.org.uk/firms/psd2>

### 5.2 版本/日期

- **开放银行标准版本**：v3.1
- **文档版本**：2023-03-15
- **最后更新**：2023-12-01

### 5.3 其他参考

- **OBIE标准**：开放银行实施实体标准
- **FAPI标准**：金融级API安全标准
- **GDPR**：通用数据保护条例

## 6. 评审

### 6.1 评审人

- **技术评审**：开放银行技术专家
- **标准评审**：FCA监管专家
- **实践评审**：银行API工程师

### 6.2 结论

**通过** - 该案例完整展示了英国开放银行API的实施方案，与形式化框架的L3标准模型高度对齐，为金融行业的开放银行建设提供了重要的参考价值。

### 6.3 备注

- 案例涵盖了开放银行的核心功能，适合作为开放银行建设的参考实现
- 建议在实际应用中结合具体的监管要求进行定制化配置
- 需要关注数据保护和客户隐私保护要求
