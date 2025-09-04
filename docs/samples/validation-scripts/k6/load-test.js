import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend, Counter } from 'k6/metrics';

// 自定义指标
const errorRate = new Rate('errors');
const responseTime = new Trend('response_time');
const requestCount = new Counter('request_count');
const successCount = new Counter('success_count');

// 测试配置
export const options = {
  stages: [
    // 预热阶段
    { duration: '2m', target: 10 },
    // 逐步增加负载
    { duration: '5m', target: 50 },
    // 保持负载
    { duration: '10m', target: 50 },
    // 峰值负载
    { duration: '5m', target: 100 },
    // 逐步减少负载
    { duration: '5m', target: 20 },
    // 冷却阶段
    { duration: '2m', target: 0 },
  ],
  thresholds: {
    // 性能阈值
    http_req_duration: ['p(95)<500', 'p(99)<1000'], // 95%请求<500ms, 99%请求<1000ms
    http_req_failed: ['rate<0.05'], // 错误率<5%
    errors: ['rate<0.05'], // 自定义错误率<5%
    response_time: ['p(95)<500', 'p(99)<1000'], // 自定义响应时间阈值
  },
};

// 测试数据
const testData = {
  baseUrl: __ENV.BASE_URL || 'http://localhost:8080',
  endpoints: [
    '/api/v1/health',
    '/api/v1/status',
    '/api/v1/metrics',
    '/api/v1/config',
  ],
  payloads: {
    user: {
      name: 'Test User',
      email: 'test@example.com',
      role: 'user',
    },
    config: {
      feature: 'load_testing',
      enabled: true,
      timeout: 5000,
    },
  },
};

// 随机用户数据生成器
function generateRandomUser() {
  const id = Math.floor(Math.random() * 10000);
  return {
    id: id,
    name: `User ${id}`,
    email: `user${id}@example.com`,
    role: Math.random() > 0.5 ? 'admin' : 'user',
    timestamp: new Date().toISOString(),
  };
}

// 随机配置数据生成器
function generateRandomConfig() {
  return {
    feature: `feature_${Math.floor(Math.random() * 100)}`,
    enabled: Math.random() > 0.3,
    timeout: Math.floor(Math.random() * 10000) + 1000,
    retries: Math.floor(Math.random() * 5) + 1,
  };
}

// 主要测试函数
export default function() {
  const startTime = Date.now();
  
  // 随机选择端点
  const endpoint = testData.endpoints[Math.floor(Math.random() * testData.endpoints.length)];
  const url = `${testData.baseUrl}${endpoint}`;
  
  // 设置请求头
  const headers = {
    'Content-Type': 'application/json',
    'User-Agent': 'K6-LoadTest/1.0',
    'X-Request-ID': `req_${Math.floor(Math.random() * 1000000)}`,
    'X-Test-Session': `session_${__VU}`,
  };
  
  // 根据端点类型选择请求方法
  let response;
  let requestData = null;
  
  if (endpoint.includes('/health') || endpoint.includes('/status')) {
    // GET请求
    response = http.get(url, { headers });
  } else if (endpoint.includes('/config')) {
    // POST请求
    requestData = generateRandomConfig();
    response = http.post(url, JSON.stringify(requestData), { headers });
  } else if (endpoint.includes('/metrics')) {
    // GET请求，带查询参数
    const params = {
      start: new Date(Date.now() - 3600000).toISOString(), // 1小时前
      end: new Date().toISOString(),
      resolution: '1m',
    };
    const queryString = Object.entries(params)
      .map(([key, value]) => `${key}=${encodeURIComponent(value)}`)
      .join('&');
    response = http.get(`${url}?${queryString}`, { headers });
  } else {
    // 默认GET请求
    response = http.get(url, { headers });
  }
  
  // 记录请求计数
  requestCount.add(1);
  
  // 计算响应时间
  const responseTimeMs = Date.now() - startTime;
  responseTime.add(responseTimeMs);
  
  // 检查响应
  const checks = check(response, {
    'status is 200': (r) => r.status === 200,
    'response time < 500ms': (r) => r.timings.duration < 500,
    'response has content': (r) => r.body.length > 0,
    'response is JSON': (r) => {
      try {
        JSON.parse(r.body);
        return true;
      } catch (e) {
        return false;
      }
    },
  });
  
  // 记录成功/失败
  if (checks) {
    successCount.add(1);
  } else {
    errorRate.add(1);
  }
  
  // 添加随机延迟模拟真实用户行为
  sleep(Math.random() * 2 + 1);
}

// 设置函数 - 在测试开始前执行
export function setup() {
  console.log('🚀 开始负载测试...');
  console.log(`📡 目标URL: ${testData.baseUrl}`);
  console.log(`🎯 测试端点: ${testData.endpoints.join(', ')}`);
  console.log(`⏱️  测试阶段: ${JSON.stringify(options.stages, null, 2)}`);
  
  // 验证目标系统可用性
  const healthCheck = http.get(`${testData.baseUrl}/api/v1/health`);
  if (healthCheck.status !== 200) {
    throw new Error(`目标系统不可用: ${healthCheck.status}`);
  }
  
  console.log('✅ 目标系统健康检查通过');
  return { startTime: new Date().toISOString() };
}

// 清理函数 - 在测试结束后执行
export function teardown(data) {
  console.log('🏁 负载测试完成');
  console.log(`⏰ 开始时间: ${data.startTime}`);
  console.log(`⏰ 结束时间: ${new Date().toISOString()}`);
  
  // 输出测试摘要
  console.log('\n📊 测试摘要:');
  console.log(`总请求数: ${requestCount.values.request_count}`);
  console.log(`成功请求数: ${successCount.values.success_count}`);
  console.log(`错误率: ${((1 - successCount.values.success_count / requestCount.values.request_count) * 100).toFixed(2)}%`);
}

// 处理函数 - 处理HTTP响应
export function handleSummary(data) {
  const summary = {
    'load-test-summary.json': JSON.stringify(data, null, 2),
    'load-test-summary.txt': `
负载测试结果摘要
================

测试配置:
- 目标URL: ${testData.baseUrl}
- 测试端点: ${testData.endpoints.join(', ')}
- 虚拟用户数: ${data.metrics.vus?.values?.max || 'N/A'}
- 测试持续时间: ${data.state.testRunDuration}ms

性能指标:
- 总请求数: ${data.metrics.http_reqs?.values?.count || 'N/A'}
- 平均响应时间: ${data.metrics.http_req_duration?.values?.avg?.toFixed(2) || 'N/A'}ms
- 95%响应时间: ${data.metrics.http_req_duration?.values?.['p(95)']?.toFixed(2) || 'N/A'}ms
- 99%响应时间: ${data.metrics.http_req_duration?.values?.['p(99)']?.toFixed(2) || 'N/A'}ms
- 错误率: ${((data.metrics.http_req_failed?.values?.rate || 0) * 100).toFixed(2)}%

自定义指标:
- 自定义错误率: ${((data.metrics.errors?.values?.rate || 0) * 100).toFixed(2)}%
- 自定义响应时间(95%): ${data.metrics.response_time?.values?.['p(95)']?.toFixed(2) || 'N/A'}ms

阈值检查:
${Object.entries(data.metrics)
  .filter(([key, metric]) => metric.thresholds)
  .map(([key, metric]) => `- ${key}: ${metric.thresholds.map(t => `${t.ok ? '✅' : '❌'} ${t.threshold}`).join(', ')}`)
  .join('\n')}

测试时间: ${new Date().toISOString()}
    `.trim(),
  };
  
  return summary;
}

// 自定义指标处理
export function handleError(error) {
  console.error('❌ 测试错误:', error);
  errorRate.add(1);
}

// 环境变量配置
export const env = {
  BASE_URL: __ENV.BASE_URL || 'http://localhost:8080',
  TEST_DURATION: __ENV.TEST_DURATION || '30m',
  VUS: __ENV.VUS || 50,
  RAMP_UP: __ENV.RAMP_UP || '5m',
  RAMP_DOWN: __ENV.RAMP_DOWN || '5m',
};

// 动态配置加载
if (__ENV.CONFIG_FILE) {
  try {
    const config = JSON.parse(__ENV.CONFIG_FILE);
    Object.assign(testData, config);
    console.log('📋 已加载配置文件:', config);
  } catch (e) {
    console.error('❌ 配置文件加载失败:', e);
  }
}

// 测试场景配置
export const scenarios = {
  // 基础负载测试
  'constant-load': {
    executor: 'constant-vus',
    vus: parseInt(env.VUS),
    duration: env.TEST_DURATION,
  },
  
  // 阶梯式负载测试
  'ramp-up-down': {
    executor: 'ramping-vus',
    startVUs: 0,
    stages: [
      { duration: env.RAMP_UP, target: parseInt(env.VUS) },
      { duration: '10m', target: parseInt(env.VUS) },
      { duration: env.RAMP_DOWN, target: 0 },
    ],
  },
  
  // 峰值负载测试
  'peak-load': {
    executor: 'ramping-vus',
    startVUs: 0,
    stages: [
      { duration: '2m', target: 10 },
      { duration: '5m', target: 100 },
      { duration: '2m', target: 200 },
      { duration: '5m', target: 200 },
      { duration: '2m', target: 0 },
    ],
  },
};

// 默认使用阶梯式负载测试
export const options = {
  scenarios: {
    'ramp-up-down': {
      executor: 'ramping-vus',
      startVUs: 0,
      stages: [
        { duration: '2m', target: 10 },
        { duration: '5m', target: 50 },
        { duration: '10m', target: 50 },
        { duration: '5m', target: 100 },
        { duration: '5m', target: 20 },
        { duration: '2m', target: 0 },
      ],
    },
  },
  thresholds: {
    http_req_duration: ['p(95)<500', 'p(99)<1000'],
    http_req_failed: ['rate<0.05'],
    errors: ['rate<0.05'],
    response_time: ['p(95)<500', 'p(99)<1000'],
  },
};
