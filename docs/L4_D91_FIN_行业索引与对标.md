---
id: L4_D91_FIN_IDX_V0.1
title: 金融行业索引与对标（FIN）
level: L4
domain: D91
model: FIN-INDEX
version: V0.1
status: draft
---

## 目录

## 1. 范围与对象

- 核心对象：Open Banking, PCI-DSS, Apache Fineract, Hyperledger Fabric, Quorum

## 2. 对标来源

- ISO 20022, PCI-DSS, Basel III（参考维度）
- Open Banking 标准、FAPI（金融级 API 安全）
- 央行与监管机构接口规范（本地化参考）

## 3. 术语对齐（中英）

| 中文 | English | 关联模型 |
| --- | --- | --- |
| 账户 | Account | L3_D02_数据标准模型 |
| 支付 | Payment | L3_D01_交互 + L3_D03_功能标准模型 |
| 清算 | Clearing | L3_D03_功能/工作流标准模型 |
| 结算 | Settlement | L3_D03_功能/工作流标准模型 |
| 账本 | Ledger | L3_D02_数据 + L3_D10_分布式模式 |
| 风控 | Risk Control | L3_D03_规则引擎/工作流 |
| 合规模块 | Compliance | L3_D08_测试/质量 + L3_D05_部署门禁 |

## 4. 标准/项目映射矩阵（模板）

见 `docs/TEMPLATE_映射矩阵.md`，本行业矩阵草案：

| 领域/能力 | 国际标准/项目 | 本框架模型(Lx_Dyy_Mzz) | 关键术语 | 证据条目 | 备注 |
| --- | --- | --- | --- | --- | --- |
| Open Banking API | OpenAPI/OBIE | L3_D01_交互标准模型 | Consent/Token/Scope | evidence:FIN-API-001 | 对账/审计 |
| 支付合规 | PCI-DSS | L3_D05_部署 + L3_D08_质量 | PAN/Tokenization/PCI Scope | evidence:FIN-PCI-001 | 扫描/审计 |
| 核心银行 | Fineract | L3_D02_数据 + L3_D03_功能 | Account/Loan/Posting | evidence:FIN-CORE-001 | 生产实例 |
| DLT | Hyperledger/Quorum | L3_D10_分布式模式 | Consensus/Privacy | evidence:FIN-DLT-001 | 金融侧链 |

## 5. 成熟案例与证据（模板）

- 请使用 `docs/TEMPLATE_证据条目.md` 填写 evidence:FIN-API-001, FIN-PCI-001 ...

## 6. 待补充

- 安全与合规模块细化、双语术语表、典型流程与 SLO 指标
