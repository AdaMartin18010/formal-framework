# 测试框架

## 📋 概述

本目录包含了各种测试框架，用于自动化测试正式验证框架的各个组件和功能。

## 🧪 测试框架分类

### 1. k6性能测试

- [负载测试](k6/load-testing.js)
- [压力测试](k6/stress-testing.js)
- [峰值测试](k6/spike-testing.js)
- [容量测试](k6/volume-testing.js)

### 2. JMeter负载测试

- [HTTP测试](jmeter/http-testing.jmx)
- [数据库测试](jmeter/database-testing.jmx)
- [API测试](jmeter/api-testing.jmx)
- [Web测试](jmeter/web-testing.jmx)

### 3. 自定义测试框架

- [单元测试](custom/unit-testing.js)
- [集成测试](custom/integration-testing.js)
- [端到端测试](custom/e2e-testing.js)
- [回归测试](custom/regression-testing.js)

## 🚀 快速开始

### 安装测试工具

```bash
# 安装k6
npm install -g k6

# 安装JMeter
npm install -g jmeter

# 安装自定义测试框架
npm install @formal-framework/testing-framework
```

### 运行测试

```bash
# 运行k6测试
k6 run k6/load-testing.js

# 运行JMeter测试
jmeter -n -t jmeter/http-testing.jmx

# 运行自定义测试
npm test
```

## 📊 测试类型

### 1. 性能测试

- **负载测试**：测试系统在正常负载下的性能
- **压力测试**：测试系统在极限负载下的性能
- **峰值测试**：测试系统在突发负载下的性能
- **容量测试**：测试系统的最大处理能力

### 2. 功能测试

- **单元测试**：测试单个组件的功能
- **集成测试**：测试组件间的集成
- **端到端测试**：测试完整的用户流程
- **回归测试**：测试修复后的功能

### 3. 安全测试

- **漏洞扫描**：扫描系统安全漏洞
- **渗透测试**：模拟攻击测试系统安全性
- **权限测试**：测试访问控制机制
- **数据保护测试**：测试数据保护措施

## 🔧 测试配置

### k6测试配置

```javascript
// k6测试配置示例
import http from 'k6/http';
import { check, sleep } from 'k6';

export const options = {
  stages: [
    { duration: '2m', target: 100 },   // 爬升到100用户
    { duration: '5m', target: 100 },   // 保持100用户5分钟
    { duration: '2m', target: 200 },   // 爬升到200用户
    { duration: '5m', target: 200 },   // 保持200用户5分钟
    { duration: '2m', target: 0 },     // 降到0用户
  ],
  thresholds: {
    http_req_duration: ['p(95)<500'], // 95%的请求必须在500ms内完成
    http_req_failed: ['rate<0.05'],   // 错误率必须小于5%
  },
};

export default function () {
  const response = http.get('https://api.example.com/health');
  check(response, {
    'status is 200': (r) => r.status === 200,
    'response time < 500ms': (r) => r.timings.duration < 500,
  });
  sleep(1);
}
```

### JMeter测试配置

```xml
<!-- JMeter测试配置示例 -->
<?xml version="1.0" encoding="UTF-8"?>
<jmeterTestPlan version="1.2">
  <hashTree>
    <TestPlan testname="Formal Framework Test Plan">
      <elementProp name="TestPlan.arguments" elementType="Arguments" guiclass="ArgumentsPanel">
        <collectionProp name="Arguments.arguments"/>
      </elementProp>
      <stringProp name="TestPlan.user_define_classpath"></stringProp>
      <boolProp name="TestPlan.functional_mode">false</boolProp>
      <boolProp name="TestPlan.serialize_threadgroups">false</boolProp>
    </TestPlan>
    <hashTree>
      <ThreadGroup testname="Thread Group">
        <stringProp name="ThreadGroup.num_threads">100</stringProp>
        <stringProp name="ThreadGroup.ramp_time">60</stringProp>
        <stringProp name="ThreadGroup.duration">300</stringProp>
        <stringProp name="ThreadGroup.delay"></stringProp>
        <boolProp name="ThreadGroup.scheduler">true</boolProp>
      </ThreadGroup>
    </hashTree>
  </hashTree>
</jmeterTestPlan>
```

### 自定义测试配置

```javascript
// 自定义测试配置示例
const testConfig = {
  // 测试环境配置
  environment: {
    baseUrl: 'https://api.example.com',
    timeout: 30000,
    retries: 3
  },
  
  // 测试数据配置
  testData: {
    users: 100,
    duration: 300,
    rampUp: 60
  },
  
  // 断言配置
  assertions: {
    responseTime: 500,
    errorRate: 0.05,
    throughput: 1000
  }
};

module.exports = testConfig;
```

## 📋 测试清单

### 性能测试清单

- [ ] 响应时间测试
- [ ] 吞吐量测试
- [ ] 并发用户测试
- [ ] 资源使用测试
- [ ] 内存泄漏测试
- [ ] CPU使用率测试
- [ ] 网络带宽测试
- [ ] 数据库性能测试

### 功能测试清单

- [ ] API接口测试
- [ ] 用户界面测试
- [ ] 业务流程测试
- [ ] 数据验证测试
- [ ] 错误处理测试
- [ ] 边界条件测试
- [ ] 兼容性测试
- [ ] 可访问性测试

### 安全测试清单

- [ ] 身份认证测试
- [ ] 授权控制测试
- [ ] 数据加密测试
- [ ] 输入验证测试
- [ ] SQL注入测试
- [ ] XSS攻击测试
- [ ] CSRF攻击测试
- [ ] 会话管理测试

## 📊 测试报告

### 性能测试报告

- **响应时间统计**：平均、中位数、P95、P99
- **吞吐量统计**：请求/秒、事务/秒
- **错误率统计**：错误率、错误类型
- **资源使用统计**：CPU、内存、网络

### 功能测试报告

- **测试用例统计**：总数、通过、失败、跳过
- **覆盖率统计**：代码覆盖率、分支覆盖率
- **缺陷统计**：严重、一般、轻微
- **回归测试统计**：回归率、修复率

### 安全测试报告

- **漏洞统计**：高危、中危、低危
- **安全评分**：总体评分、分类评分
- **合规性检查**：合规项、不合规项
- **修复建议**：修复优先级、修复方案

## 🔍 故障排除

### 常见问题

1. **测试超时**：检查网络连接和服务器响应
2. **内存不足**：调整测试参数和系统配置
3. **并发问题**：检查并发限制和资源竞争
4. **数据问题**：检查测试数据和数据一致性

### 调试技巧

1. **启用详细日志**：记录详细的测试过程
2. **分步测试**：将复杂测试分解为简单步骤
3. **使用监控工具**：实时监控系统状态
4. **分析测试结果**：深入分析测试结果和趋势

## 📚 学习资源

### 官方文档

- [k6文档](https://k6.io/docs/)
- [JMeter文档](https://jmeter.apache.org/usermanual/)
- [Jest文档](https://jestjs.io/docs/getting-started)
- [Mocha文档](https://mochajs.org/)

### 最佳实践

- [性能测试最佳实践](https://k6.io/docs/testing-guides/)
- [负载测试最佳实践](https://jmeter.apache.org/usermanual/best-practices.html)
- [自动化测试最佳实践](https://docs.cypress.io/guides/references/best-practices)
- [测试策略最佳实践](https://martinfowler.com/articles/practical-test-pyramid.html)

## 🔗 相关文档

- [工具链概览](../README.md)
- [验证脚本](../verification-scripts/README.md)
- [监控工具](../monitoring/README.md)
- [部署工具](../deployment/README.md)

---

*最后更新：2024-12-19*-
