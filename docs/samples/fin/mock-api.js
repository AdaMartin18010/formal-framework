// Minimal mock OpenBanking API (placeholder)
const express = require('express');
const app = express();
app.use(express.json());

app.get('/accounts', (req, res) => {
  if (!req.headers.authorization) return res.status(401).json({ error: 'unauthorized' });
  res.json([{ id: 'acc-001', balance: 1000 }]);
});

app.post('/payments', (req, res) => {
  if (!req.headers.authorization) return res.status(401).json({ error: 'unauthorized' });
  res.status(201).json({ id: 'pay-001', status: 'created' });
});

const port = process.env.PORT || 3000;
app.listen(port, () => console.log(`Mock OB API listening on ${port}`));
