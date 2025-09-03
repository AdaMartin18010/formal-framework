-- 对账：交易表与总账表金额一致性（占位）
SELECT t.account_id,
       SUM(t.amount) AS tx_sum,
       SUM(l.amount) AS ledger_sum
FROM transactions t
JOIN ledger_entries l ON l.tx_id = t.id
GROUP BY t.account_id
HAVING SUM(t.amount) <> SUM(l.amount);
