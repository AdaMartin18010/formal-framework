# 端到端示例：金融-OpenBanking API（L2→L3→行业→证据→校验）

## 1. 目标

- 以 Open Banking API 为例，从 L2/L3 到行业对标与证据，完成可追溯验证。

## 2. 相关文档

- L2：`L2_D01_交互元模型.md`、`L2_D02_数据元模型.md`
- L3：`L3_D01_交互标准模型.md`、`L3_D02_数据标准模型.md`
- 行业：`L4_D91_FIN_行业索引与对标.md`
- 证据：`EVIDENCE_FIN-API-001.md`、`EVIDENCE_FIN-PCI-001.md`、`EVIDENCE_FIN-CORE-001.md`
- 校验矩阵：`VERIFICATION_MATRIX.md`

## 3. 模型桥接

- L2 → L3：API/Contract/Entity 映射到 L3 标准字段与不变式（I1/I2，D1/D2/D3）
- L3 → 行业：API 安全（FAPI/OAuth2）、账户/支付领域模型、审计与合规门禁

## 4. 不变式与验证

- I1 版本兼容：schema diff 与兼容性用例
- I2 鉴权强制：未授权/过期/范围不足用例
- D2 外键完整：账户与交易关联完整性
- D3 迁移可逆：账本迁移脚本回滚验证

## 5. 工具与命令示例

- 契约测试（Postman/Newman）：`docs/samples/fin/openbanking.postman_collection.json`
- 启动本地 Mock API：
  - `cd docs/samples/fin && node mock-api.js`
  - 调用示例：`curl -H "Authorization: Bearer token" http://127.0.0.1:3000/accounts`
- 数据一致性：`docs/samples/fin/reconciliation.sql`

## 6. 预期结果与证据

- 更新 evidence: FIN-API-001 / FIN-PCI-001 / FIN-CORE-001（占位）

## 7. 扩展

- 将验证样例补充回 `L3_D01`/`L3_D02` 与 `VERIFICATION_MATRIX.md`
