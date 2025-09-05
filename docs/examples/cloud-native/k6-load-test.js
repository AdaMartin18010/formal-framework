import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate } from 'k6/metrics';

// 自定义指标
export let errorRate = new Rate('errors');

// 测试配置
export let options = {
  stages: [
    { duration: '2m', target: 100 }, // 2分钟内逐步增加到100个用户
    { duration: '5m', target: 100 }, // 保持100个用户5分钟
    { duration: '2m', target: 200 }, // 2分钟内增加到200个用户
    { duration: '5m', target: 200 }, // 保持200个用户5分钟
    { duration: '2m', target: 0 },   // 2分钟内逐步减少到0个用户
  ],
  thresholds: {
    http_req_duration: ['p(95)<500'], // 95%的请求响应时间小于500ms
    http_req_failed: ['rate<0.1'],    // 错误率小于10%
    errors: ['rate<0.1'],             // 自定义错误率小于10%
  },
};

// 测试数据
const testData = {
  users: [
    { id: 1, name: 'User1', email: 'user1@example.com' },
    { id: 2, name: 'User2', email: 'user2@example.com' },
    { id: 3, name: 'User3', email: 'user3@example.com' },
  ],
  products: [
    { id: 1, name: 'Product1', price: 100 },
    { id: 2, name: 'Product2', price: 200 },
    { id: 3, name: 'Product3', price: 300 },
  ],
};

// 主测试函数
export default function () {
  // 随机选择用户和产品
  const user = testData.users[Math.floor(Math.random() * testData.users.length)];
  const product = testData.products[Math.floor(Math.random() * testData.products.length)];
  
  // 测试场景1: 健康检查
  let response = http.get('http://demo-app-service/health');
  let success = check(response, {
    'health check status is 200': (r) => r.status === 200,
    'health check response time < 100ms': (r) => r.timings.duration < 100,
  });
  errorRate.add(!success);
  
  sleep(1);
  
  // 测试场景2: 获取用户信息
  response = http.get(`http://demo-app-service/api/users/${user.id}`);
  success = check(response, {
    'get user status is 200': (r) => r.status === 200,
    'get user response time < 200ms': (r) => r.timings.duration < 200,
    'get user returns user data': (r) => {
      const data = JSON.parse(r.body);
      return data.id === user.id && data.name === user.name;
    },
  });
  errorRate.add(!success);
  
  sleep(1);
  
  // 测试场景3: 创建订单
  const orderData = {
    userId: user.id,
    productId: product.id,
    quantity: Math.floor(Math.random() * 5) + 1,
    timestamp: new Date().toISOString(),
  };
  
  response = http.post('http://demo-app-service/api/orders', JSON.stringify(orderData), {
    headers: { 'Content-Type': 'application/json' },
  });
  success = check(response, {
    'create order status is 201': (r) => r.status === 201,
    'create order response time < 300ms': (r) => r.timings.duration < 300,
    'create order returns order id': (r) => {
      const data = JSON.parse(r.body);
      return data.id && data.id > 0;
    },
  });
  errorRate.add(!success);
  
  sleep(1);
  
  // 测试场景4: 获取订单列表
  response = http.get(`http://demo-app-service/api/users/${user.id}/orders`);
  success = check(response, {
    'get orders status is 200': (r) => r.status === 200,
    'get orders response time < 250ms': (r) => r.timings.duration < 250,
    'get orders returns array': (r) => {
      const data = JSON.parse(r.body);
      return Array.isArray(data.orders);
    },
  });
  errorRate.add(!success);
  
  sleep(1);
}

// 测试结束后的清理函数
export function teardown(data) {
  console.log('Load test completed');
  console.log('Final error rate:', errorRate.values);
}
