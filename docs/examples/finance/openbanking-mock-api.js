const express = require('express');
const cors = require('cors');
const jwt = require('jsonwebtoken');
const crypto = require('crypto');

const app = express();
const PORT = process.env.PORT || 3000;

// 中间件
app.use(cors());
app.use(express.json());

// 模拟数据
const mockData = {
  accounts: [
    {
      id: 'ACC001',
      accountNumber: '1234567890',
      accountType: 'CURRENT',
      currency: 'GBP',
      balance: 1500.50,
      availableBalance: 1500.50,
      status: 'ACTIVE',
      openingDate: '2020-01-15',
      lastUpdated: new Date().toISOString()
    },
    {
      id: 'ACC002',
      accountNumber: '0987654321',
      accountType: 'SAVINGS',
      currency: 'GBP',
      balance: 5000.00,
      availableBalance: 5000.00,
      status: 'ACTIVE',
      openingDate: '2019-06-20',
      lastUpdated: new Date().toISOString()
    }
  ],
  transactions: [
    {
      id: 'TXN001',
      accountId: 'ACC001',
      amount: -25.50,
      currency: 'GBP',
      description: 'Coffee Shop Purchase',
      transactionType: 'DEBIT',
      status: 'BOOKED',
      bookingDate: '2024-01-15',
      valueDate: '2024-01-15',
      merchantName: 'Coffee Shop',
      merchantCategoryCode: '5812'
    },
    {
      id: 'TXN002',
      accountId: 'ACC001',
      amount: 2000.00,
      currency: 'GBP',
      description: 'Salary Payment',
      transactionType: 'CREDIT',
      status: 'BOOKED',
      bookingDate: '2024-01-14',
      valueDate: '2024-01-14',
      merchantName: 'Employer Ltd',
      merchantCategoryCode: '6011'
    }
  ],
  payments: [
    {
      id: 'PAY001',
      accountId: 'ACC001',
      amount: 100.00,
      currency: 'GBP',
      status: 'ACCEPTED',
      createdAt: new Date().toISOString(),
      beneficiary: {
        name: 'John Doe',
        accountNumber: '1111222233',
        sortCode: '20-00-00'
      }
    }
  ]
};

// JWT密钥
const JWT_SECRET = 'your-secret-key';

// 认证中间件
const authenticateToken = (req, res, next) => {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];

  if (!token) {
    return res.status(401).json({ error: 'Access token required' });
  }

  jwt.verify(token, JWT_SECRET, (err, user) => {
    if (err) {
      return res.status(403).json({ error: 'Invalid token' });
    }
    req.user = user;
    next();
  });
};

// 健康检查端点
app.get('/health', (req, res) => {
  res.json({
    status: 'healthy',
    timestamp: new Date().toISOString(),
    version: '1.0.0'
  });
});

// OAuth2 令牌端点
app.post('/oauth/token', (req, res) => {
  const { grant_type, client_id, client_secret, scope } = req.body;

  // 简单的客户端验证
  if (client_id !== 'test-client' || client_secret !== 'test-secret') {
    return res.status(401).json({ error: 'Invalid client credentials' });
  }

  if (grant_type !== 'client_credentials') {
    return res.status(400).json({ error: 'Unsupported grant type' });
  }

  // 生成访问令牌
  const accessToken = jwt.sign(
    {
      client_id: client_id,
      scope: scope || 'accounts payments',
      iat: Math.floor(Date.now() / 1000),
      exp: Math.floor(Date.now() / 1000) + 3600 // 1小时过期
    },
    JWT_SECRET
  );

  res.json({
    access_token: accessToken,
    token_type: 'Bearer',
    expires_in: 3600,
    scope: scope || 'accounts payments'
  });
});

// 账户信息端点
app.get('/open-banking/v3.1/accounts', authenticateToken, (req, res) => {
  const { page, pageSize } = req.query;
  const pageNum = parseInt(page) || 1;
  const size = parseInt(pageSize) || 10;

  const startIndex = (pageNum - 1) * size;
  const endIndex = startIndex + size;
  const paginatedAccounts = mockData.accounts.slice(startIndex, endIndex);

  res.json({
    Data: {
      Account: paginatedAccounts
    },
    Links: {
      Self: `/open-banking/v3.1/accounts?page=${pageNum}&pageSize=${size}`,
      First: `/open-banking/v3.1/accounts?page=1&pageSize=${size}`,
      Last: `/open-banking/v3.1/accounts?page=${Math.ceil(mockData.accounts.length / size)}&pageSize=${size}`,
      Next: pageNum < Math.ceil(mockData.accounts.length / size) ? 
            `/open-banking/v3.1/accounts?page=${pageNum + 1}&pageSize=${size}` : null,
      Prev: pageNum > 1 ? 
            `/open-banking/v3.1/accounts?page=${pageNum - 1}&pageSize=${size}` : null
    },
    Meta: {
      TotalPages: Math.ceil(mockData.accounts.length / size),
      FirstAvailableDateTime: '2020-01-15T00:00:00Z',
      LastAvailableDateTime: new Date().toISOString()
    }
  });
});

// 特定账户信息
app.get('/open-banking/v3.1/accounts/:accountId', authenticateToken, (req, res) => {
  const { accountId } = req.params;
  const account = mockData.accounts.find(acc => acc.id === accountId);

  if (!account) {
    return res.status(404).json({ error: 'Account not found' });
  }

  res.json({
    Data: {
      Account: [account]
    },
    Links: {
      Self: `/open-banking/v3.1/accounts/${accountId}`
    },
    Meta: {
      TotalPages: 1,
      FirstAvailableDateTime: account.openingDate,
      LastAvailableDateTime: account.lastUpdated
    }
  });
});

// 账户余额
app.get('/open-banking/v3.1/accounts/:accountId/balances', authenticateToken, (req, res) => {
  const { accountId } = req.params;
  const account = mockData.accounts.find(acc => acc.id === accountId);

  if (!account) {
    return res.status(404).json({ error: 'Account not found' });
  }

  res.json({
    Data: {
      Balance: [{
        AccountId: account.id,
        Amount: {
          Amount: account.balance.toString(),
          Currency: account.currency
        },
        CreditDebitIndicator: account.balance >= 0 ? 'Credit' : 'Debit',
        Type: 'InterimAvailable',
        DateTime: account.lastUpdated
      }]
    },
    Links: {
      Self: `/open-banking/v3.1/accounts/${accountId}/balances`
    },
    Meta: {
      TotalPages: 1,
      FirstAvailableDateTime: account.openingDate,
      LastAvailableDateTime: account.lastUpdated
    }
  });
});

// 交易历史
app.get('/open-banking/v3.1/accounts/:accountId/transactions', authenticateToken, (req, res) => {
  const { accountId } = req.params;
  const { fromBookingDateTime, toBookingDateTime, page, pageSize } = req.query;
  
  let transactions = mockData.transactions.filter(txn => txn.accountId === accountId);

  // 时间过滤
  if (fromBookingDateTime) {
    transactions = transactions.filter(txn => txn.bookingDate >= fromBookingDateTime);
  }
  if (toBookingDateTime) {
    transactions = transactions.filter(txn => txn.bookingDate <= toBookingDateTime);
  }

  // 分页
  const pageNum = parseInt(page) || 1;
  const size = parseInt(pageSize) || 10;
  const startIndex = (pageNum - 1) * size;
  const endIndex = startIndex + size;
  const paginatedTransactions = transactions.slice(startIndex, endIndex);

  res.json({
    Data: {
      Transaction: paginatedTransactions
    },
    Links: {
      Self: `/open-banking/v3.1/accounts/${accountId}/transactions?page=${pageNum}&pageSize=${size}`,
      First: `/open-banking/v3.1/accounts/${accountId}/transactions?page=1&pageSize=${size}`,
      Last: `/open-banking/v3.1/accounts/${accountId}/transactions?page=${Math.ceil(transactions.length / size)}&pageSize=${size}`,
      Next: pageNum < Math.ceil(transactions.length / size) ? 
            `/open-banking/v3.1/accounts/${accountId}/transactions?page=${pageNum + 1}&pageSize=${size}` : null,
      Prev: pageNum > 1 ? 
            `/open-banking/v3.1/accounts/${accountId}/transactions?page=${pageNum - 1}&pageSize=${size}` : null
    },
    Meta: {
      TotalPages: Math.ceil(transactions.length / size),
      FirstAvailableDateTime: '2020-01-15T00:00:00Z',
      LastAvailableDateTime: new Date().toISOString()
    }
  });
});

// 支付提交
app.post('/open-banking/v3.1/payments', authenticateToken, (req, res) => {
  const { Data } = req.body;
  
  if (!Data || !Data.Initiation) {
    return res.status(400).json({ error: 'Invalid payment data' });
  }

  const paymentId = 'PAY' + crypto.randomBytes(4).toString('hex').toUpperCase();
  const newPayment = {
    id: paymentId,
    accountId: Data.Initiation.DebtorAccount.Identification,
    amount: parseFloat(Data.Initiation.InstructedAmount.Amount),
    currency: Data.Initiation.InstructedAmount.Currency,
    status: 'ACCEPTED',
    createdAt: new Date().toISOString(),
    beneficiary: {
      name: Data.Initiation.CreditorName,
      accountNumber: Data.Initiation.CreditorAccount.Identification,
      sortCode: Data.Initiation.CreditorAccount.SchemeName
    }
  };

  mockData.payments.push(newPayment);

  res.status(201).json({
    Data: {
      PaymentId: paymentId,
      Status: 'ACCEPTED',
      CreationDateTime: newPayment.createdAt
    },
    Links: {
      Self: `/open-banking/v3.1/payments/${paymentId}`
    },
    Meta: {
      TotalPages: 1
    }
  });
});

// 支付状态查询
app.get('/open-banking/v3.1/payments/:paymentId', authenticateToken, (req, res) => {
  const { paymentId } = req.params;
  const payment = mockData.payments.find(pay => pay.id === paymentId);

  if (!payment) {
    return res.status(404).json({ error: 'Payment not found' });
  }

  res.json({
    Data: {
      PaymentId: payment.id,
      Status: payment.status,
      CreationDateTime: payment.createdAt,
      Initiation: {
        InstructedAmount: {
          Amount: payment.amount.toString(),
          Currency: payment.currency
        },
        CreditorName: payment.beneficiary.name,
        CreditorAccount: {
          Identification: payment.beneficiary.accountNumber,
          SchemeName: payment.beneficiary.sortCode
        }
      }
    },
    Links: {
      Self: `/open-banking/v3.1/payments/${paymentId}`
    },
    Meta: {
      TotalPages: 1
    }
  });
});

// 错误处理中间件
app.use((err, req, res, next) => {
  console.error(err.stack);
  res.status(500).json({ error: 'Internal server error' });
});

// 启动服务器
app.listen(PORT, () => {
  console.log(`Open Banking Mock API 服务器运行在端口 ${PORT}`);
  console.log(`健康检查: http://localhost:${PORT}/health`);
  console.log(`获取令牌: POST http://localhost:${PORT}/oauth/token`);
  console.log(`账户信息: GET http://localhost:${PORT}/open-banking/v3.1/accounts`);
});

module.exports = app;
