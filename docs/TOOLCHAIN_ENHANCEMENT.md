# 工具链完善计划

## 📋 概述

本文档详细规划了正式验证框架工具链的完善工作，包括脚本可执行性验证、Docker化部署、CI/CD集成和自动化测试。

## 🎯 完善目标

1. **可执行性**：所有验证脚本100%可执行
2. **容器化**：完整的Docker化部署方案
3. **自动化**：CI/CD流水线集成
4. **可维护性**：工具链易于维护和扩展

## 🔧 工具链架构

### 整体架构图

```mermaid
graph TB
    A[开发环境] --> B[构建系统]
    B --> C[测试框架]
    C --> D[部署系统]
    D --> E[监控系统]
    E --> F[反馈系统]
    F --> A
```

### 工具分类

| 工具类别 | 工具名称 | 版本 | 用途 | 状态 |
|----------|----------|------|------|------|
| 构建工具 | Docker | 24.0+ | 容器化 | ✅ |
| 构建工具 | Docker Compose | 2.20+ | 多容器编排 | ✅ |
| 构建工具 | Make | 4.3+ | 构建自动化 | ✅ |
| 测试工具 | k6 | 0.47+ | 性能测试 | ✅ |
| 测试工具 | Jest | 29.0+ | 单元测试 | ✅ |
| 测试工具 | Pytest | 7.0+ | Python测试 | ✅ |
| 部署工具 | Kubernetes | 1.24+ | 容器编排 | ✅ |
| 部署工具 | Helm | 3.12+ | 包管理 | ✅ |
| 监控工具 | Prometheus | 2.45+ | 指标收集 | ✅ |
| 监控工具 | Grafana | 10.0+ | 可视化 | ✅ |
| 监控工具 | Jaeger | 1.47+ | 链路追踪 | ✅ |

## 🐳 Docker化方案

### 1. 基础镜像设计

#### 多阶段构建

```dockerfile
# 基础镜像
FROM node:18-alpine AS base
WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production

# 开发镜像
FROM base AS development
RUN npm ci
COPY . .
CMD ["npm", "run", "dev"]

# 测试镜像
FROM base AS testing
RUN npm ci
COPY . .
CMD ["npm", "test"]

# 生产镜像
FROM base AS production
COPY --from=base /app/node_modules ./node_modules
COPY . .
RUN npm run build
CMD ["npm", "start"]
```

#### 镜像优化

```dockerfile
# 安全优化
FROM node:18-alpine AS production
RUN addgroup -g 1001 -S nodejs
RUN adduser -S nextjs -u 1001
USER nextjs

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:3000/health || exit 1

# 多架构支持
FROM --platform=$BUILDPLATFORM node:18-alpine AS base
```

### 2. 服务编排

#### Docker Compose配置

```yaml
version: '3.8'

services:
  # 应用服务
  app:
    build:
      context: .
      target: production
    ports:
      - "3000:3000"
    environment:
      - NODE_ENV=production
      - DATABASE_URL=postgresql://user:pass@db:5432/app
    depends_on:
      - db
      - redis
    networks:
      - app-network

  # 数据库服务
  db:
    image: postgres:15-alpine
    environment:
      - POSTGRES_DB=app
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=pass
    volumes:
      - postgres_data:/var/lib/postgresql/data
    networks:
      - app-network

  # 缓存服务
  redis:
    image: redis:7-alpine
    volumes:
      - redis_data:/data
    networks:
      - app-network

  # 监控服务
  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml
    networks:
      - app-network

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3001:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana_data:/var/lib/grafana
    networks:
      - app-network

volumes:
  postgres_data:
  redis_data:
  grafana_data:

networks:
  app-network:
    driver: bridge
```

### 3. Kubernetes部署

#### 部署清单

```yaml
# 命名空间
apiVersion: v1
kind: Namespace
metadata:
  name: formal-framework

---
# 配置映射
apiVersion: v1
kind: ConfigMap
metadata:
  name: app-config
  namespace: formal-framework
data:
  NODE_ENV: "production"
  LOG_LEVEL: "info"

---
# 密钥
apiVersion: v1
kind: Secret
metadata:
  name: app-secrets
  namespace: formal-framework
type: Opaque
data:
  DATABASE_URL: <base64-encoded-url>
  JWT_SECRET: <base64-encoded-secret>

---
# 部署
apiVersion: apps/v1
kind: Deployment
metadata:
  name: formal-framework-app
  namespace: formal-framework
spec:
  replicas: 3
  selector:
    matchLabels:
      app: formal-framework-app
  template:
    metadata:
      labels:
        app: formal-framework-app
    spec:
      containers:
      - name: app
        image: formal-framework:latest
        ports:
        - containerPort: 3000
        env:
        - name: NODE_ENV
          valueFrom:
            configMapKeyRef:
              name: app-config
              key: NODE_ENV
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: app-secrets
              key: DATABASE_URL
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 3000
          initialDelaySeconds: 5
          periodSeconds: 5

---
# 服务
apiVersion: v1
kind: Service
metadata:
  name: formal-framework-service
  namespace: formal-framework
spec:
  selector:
    app: formal-framework-app
  ports:
  - port: 80
    targetPort: 3000
  type: ClusterIP

---
# 水平Pod自动扩缩容
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: formal-framework-hpa
  namespace: formal-framework
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: formal-framework-app
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

## 🧪 测试框架

### 1. 单元测试

#### JavaScript/Node.js测试

```javascript
// tests/unit/models/data-model.test.js
const { DataModel } = require('../../src/models/data-model');
const { ValidationError } = require('../../src/errors');

describe('DataModel', () => {
  let dataModel;

  beforeEach(() => {
    dataModel = new DataModel();
  });

  describe('validateEntity', () => {
    it('should validate valid entity', () => {
      const entity = {
        id: '123',
        name: 'Test Entity',
        type: 'user'
      };

      expect(() => dataModel.validateEntity(entity)).not.toThrow();
    });

    it('should throw ValidationError for invalid entity', () => {
      const entity = {
        id: '',
        name: 'Test Entity'
      };

      expect(() => dataModel.validateEntity(entity))
        .toThrow(ValidationError);
    });
  });

  describe('createRelationship', () => {
    it('should create valid relationship', () => {
      const source = { id: '1', type: 'user' };
      const target = { id: '2', type: 'order' };
      const relationship = dataModel.createRelationship(source, target, 'has');

      expect(relationship).toEqual({
        source: '1',
        target: '2',
        type: 'has',
        createdAt: expect.any(Date)
      });
    });
  });
});
```

#### Python测试

```python
# tests/unit/models/test_data_model.py
import pytest
from src.models.data_model import DataModel
from src.errors import ValidationError

class TestDataModel:
    def setup_method(self):
        self.data_model = DataModel()

    def test_validate_entity_valid(self):
        entity = {
            'id': '123',
            'name': 'Test Entity',
            'type': 'user'
        }
        
        result = self.data_model.validate_entity(entity)
        assert result is True

    def test_validate_entity_invalid(self):
        entity = {
            'id': '',
            'name': 'Test Entity'
        }
        
        with pytest.raises(ValidationError):
            self.data_model.validate_entity(entity)

    def test_create_relationship(self):
        source = {'id': '1', 'type': 'user'}
        target = {'id': '2', 'type': 'order'}
        
        relationship = self.data_model.create_relationship(
            source, target, 'has'
        )
        
        assert relationship['source'] == '1'
        assert relationship['target'] == '2'
        assert relationship['type'] == 'has'
        assert 'createdAt' in relationship
```

### 2. 集成测试

#### API集成测试

```javascript
// tests/integration/api.test.js
const request = require('supertest');
const app = require('../../src/app');
const { setupTestDatabase, cleanupTestDatabase } = require('../helpers/database');

describe('API Integration Tests', () => {
  beforeAll(async () => {
    await setupTestDatabase();
  });

  afterAll(async () => {
    await cleanupTestDatabase();
  });

  describe('POST /api/entities', () => {
    it('should create new entity', async () => {
      const entityData = {
        name: 'Test Entity',
        type: 'user',
        properties: {
          email: 'test@example.com',
          age: 25
        }
      };

      const response = await request(app)
        .post('/api/entities')
        .send(entityData)
        .expect(201);

      expect(response.body).toHaveProperty('id');
      expect(response.body.name).toBe(entityData.name);
    });

    it('should return 400 for invalid entity data', async () => {
      const invalidData = {
        name: '',
        type: 'invalid'
      };

      await request(app)
        .post('/api/entities')
        .send(invalidData)
        .expect(400);
    });
  });

  describe('GET /api/entities', () => {
    it('should return list of entities', async () => {
      const response = await request(app)
        .get('/api/entities')
        .expect(200);

      expect(Array.isArray(response.body)).toBe(true);
    });
  });
});
```

### 3. 性能测试

#### k6性能测试

```javascript
// tests/performance/load-test.js
import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate } from 'k6/metrics';

const errorRate = new Rate('errors');

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
    errors: ['rate<0.05'],            // 自定义错误率必须小于5%
  },
};

const BASE_URL = __ENV.BASE_URL || 'http://localhost:3000';

export default function () {
  // 健康检查
  const healthCheck = http.get(`${BASE_URL}/health`);
  check(healthCheck, {
    'health check status is 200': (r) => r.status === 200,
    'health check response time < 200ms': (r) => r.timings.duration < 200,
  });

  // API测试
  const payload = JSON.stringify({
    name: 'Test Entity',
    type: 'user',
    properties: {
      email: 'test@example.com',
      age: 25
    }
  });

  const params = {
    headers: {
      'Content-Type': 'application/json',
    },
  };

  // POST请求测试
  const createResponse = http.post(`${BASE_URL}/api/entities`, payload, params);
  check(createResponse, {
    'create entity status is 201': (r) => r.status === 201,
    'create entity response time < 300ms': (r) => r.timings.duration < 300,
  });

  errorRate.add(createResponse.status !== 201);

  // GET请求测试
  if (createResponse.status === 201) {
    const entityId = createResponse.json('id');
    const getResponse = http.get(`${BASE_URL}/api/entities/${entityId}`, params);
    
    check(getResponse, {
      'get entity status is 200': (r) => r.status === 200,
      'get entity response time < 200ms': (r) => r.timings.duration < 200,
    });

    errorRate.add(getResponse.status !== 200);
  }

  sleep(1);
}

export function setup() {
  console.log('Setting up performance test...');
}

export function teardown(data) {
  console.log('Cleaning up performance test...');
}
```

## 🔄 CI/CD流水线

### 1. GitHub Actions配置

#### 主流水线

```yaml
# .github/workflows/ci-cd.yml
name: CI/CD Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  NODE_VERSION: '18'
  PYTHON_VERSION: '3.11'
  DOCKER_REGISTRY: ghcr.io
  IMAGE_NAME: formal-framework

jobs:
  # 代码质量检查
  quality:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    
    - name: Setup Node.js
      uses: actions/setup-node@v3
      with:
        node-version: ${{ env.NODE_VERSION }}
        cache: 'npm'
    
    - name: Setup Python
      uses: actions/setup-python@v4
      with:
        python-version: ${{ env.PYTHON_VERSION }}
    
    - name: Install dependencies
      run: |
        npm ci
        pip install -r requirements.txt
    
    - name: Lint JavaScript
      run: npm run lint
    
    - name: Lint Python
      run: flake8 src/ tests/
    
    - name: Type check
      run: npm run type-check
    
    - name: Security audit
      run: |
        npm audit --audit-level moderate
        safety check

  # 单元测试
  unit-tests:
    runs-on: ubuntu-latest
    needs: quality
    services:
      postgres:
        image: postgres:15
        env:
          POSTGRES_PASSWORD: postgres
          POSTGRES_DB: test_db
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 5432:5432
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Setup Node.js
      uses: actions/setup-node@v3
      with:
        node-version: ${{ env.NODE_VERSION }}
        cache: 'npm'
    
    - name: Setup Python
      uses: actions/setup-python@v4
      with:
        python-version: ${{ env.PYTHON_VERSION }}
    
    - name: Install dependencies
      run: |
        npm ci
        pip install -r requirements.txt
    
    - name: Run JavaScript tests
      run: npm run test:unit
      env:
        DATABASE_URL: postgresql://postgres:postgres@localhost:5432/test_db
    
    - name: Run Python tests
      run: pytest tests/unit/ -v
      env:
        DATABASE_URL: postgresql://postgres:postgres@localhost:5432/test_db
    
    - name: Upload coverage reports
      uses: codecov/codecov-action@v3
      with:
        files: ./coverage/lcov.info,./coverage.xml

  # 集成测试
  integration-tests:
    runs-on: ubuntu-latest
    needs: unit-tests
    steps:
    - uses: actions/checkout@v3
    
    - name: Setup Node.js
      uses: actions/setup-node@v3
      with:
        node-version: ${{ env.NODE_VERSION }}
        cache: 'npm'
    
    - name: Install dependencies
      run: npm ci
    
    - name: Start services
      run: docker-compose -f docker-compose.test.yml up -d
    
    - name: Wait for services
      run: |
        timeout 60 bash -c 'until curl -f http://localhost:3000/health; do sleep 2; done'
    
    - name: Run integration tests
      run: npm run test:integration
    
    - name: Stop services
      run: docker-compose -f docker-compose.test.yml down

  # 性能测试
  performance-tests:
    runs-on: ubuntu-latest
    needs: integration-tests
    steps:
    - uses: actions/checkout@v3
    
    - name: Setup Node.js
      uses: actions/setup-node@v3
      with:
        node-version: ${{ env.NODE_VERSION }}
        cache: 'npm'
    
    - name: Install dependencies
      run: npm ci
    
    - name: Start services
      run: docker-compose -f docker-compose.test.yml up -d
    
    - name: Wait for services
      run: |
        timeout 60 bash -c 'until curl -f http://localhost:3000/health; do sleep 2; done'
    
    - name: Run performance tests
      run: |
        k6 run tests/performance/load-test.js --out json=performance-results.json
    
    - name: Upload performance results
      uses: actions/upload-artifact@v3
      with:
        name: performance-results
        path: performance-results.json

  # 构建镜像
  build:
    runs-on: ubuntu-latest
    needs: [quality, unit-tests, integration-tests]
    if: github.ref == 'refs/heads/main'
    steps:
    - uses: actions/checkout@v3
    
    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v2
    
    - name: Log in to Container Registry
      uses: docker/login-action@v2
      with:
        registry: ${{ env.DOCKER_REGISTRY }}
        username: ${{ github.actor }}
        password: ${{ secrets.GITHUB_TOKEN }}
    
    - name: Extract metadata
      id: meta
      uses: docker/metadata-action@v4
      with:
        images: ${{ env.DOCKER_REGISTRY }}/${{ github.repository }}/${{ env.IMAGE_NAME }}
        tags: |
          type=ref,event=branch
          type=ref,event=pr
          type=sha,prefix={{branch}}-
          type=raw,value=latest,enable={{is_default_branch}}
    
    - name: Build and push Docker image
      uses: docker/build-push-action@v4
      with:
        context: .
        platforms: linux/amd64,linux/arm64
        push: true
        tags: ${{ steps.meta.outputs.tags }}
        labels: ${{ steps.meta.outputs.labels }}
        cache-from: type=gha
        cache-to: type=gha,mode=max

  # 部署到测试环境
  deploy-staging:
    runs-on: ubuntu-latest
    needs: build
    if: github.ref == 'refs/heads/develop'
    environment: staging
    steps:
    - uses: actions/checkout@v3
    
    - name: Deploy to staging
      run: |
        echo "Deploying to staging environment..."
        # 部署逻辑
    
    - name: Run smoke tests
      run: |
        echo "Running smoke tests..."
        # 冒烟测试逻辑

  # 部署到生产环境
  deploy-production:
    runs-on: ubuntu-latest
    needs: build
    if: github.ref == 'refs/heads/main'
    environment: production
    steps:
    - uses: actions/checkout@v3
    
    - name: Deploy to production
      run: |
        echo "Deploying to production environment..."
        # 部署逻辑
    
    - name: Run health checks
      run: |
        echo "Running health checks..."
        # 健康检查逻辑
```

### 2. 构建脚本

#### Makefile

```makefile
# Makefile
.PHONY: help build test clean deploy

# 默认目标
help:
 @echo "Available targets:"
 @echo "  build     - Build the application"
 @echo "  test      - Run all tests"
 @echo "  clean     - Clean build artifacts"
 @echo "  deploy    - Deploy to target environment"

# 构建应用
build:
 @echo "Building application..."
 npm run build
 python -m build

# 运行测试
test: test-unit test-integration test-performance

test-unit:
 @echo "Running unit tests..."
 npm run test:unit
 pytest tests/unit/ -v

test-integration:
 @echo "Running integration tests..."
 npm run test:integration

test-performance:
 @echo "Running performance tests..."
 k6 run tests/performance/load-test.js

# 清理构建产物
clean:
 @echo "Cleaning build artifacts..."
 rm -rf dist/
 rm -rf build/
 rm -rf node_modules/
 rm -rf __pycache__/
 rm -rf .pytest_cache/

# 部署到目标环境
deploy: build
 @echo "Deploying to $(ENV) environment..."
 docker-compose -f docker-compose.$(ENV).yml up -d

# 开发环境
dev:
 @echo "Starting development environment..."
 docker-compose -f docker-compose.dev.yml up -d

# 生产环境
prod:
 @echo "Starting production environment..."
 docker-compose -f docker-compose.prod.yml up -d

# 停止服务
stop:
 @echo "Stopping services..."
 docker-compose down

# 查看日志
logs:
 docker-compose logs -f

# 健康检查
health:
 @echo "Checking service health..."
 curl -f http://localhost:3000/health || exit 1
```

## 📊 监控和告警

### 1. Prometheus配置

#### 指标收集

```yaml
# monitoring/prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "rules/*.yml"

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093

scrape_configs:
  - job_name: 'prometheus'
    static_configs:
      - targets: ['localhost:9090']

  - job_name: 'formal-framework'
    static_configs:
      - targets: ['app:3000']
    metrics_path: /metrics
    scrape_interval: 5s

  - job_name: 'node-exporter'
    static_configs:
      - targets: ['node-exporter:9100']

  - job_name: 'postgres-exporter'
    static_configs:
      - targets: ['postgres-exporter:9187']
```

### 2. 告警规则

#### 应用告警

```yaml
# monitoring/rules/app-alerts.yml
groups:
- name: formal-framework
  rules:
  - alert: HighErrorRate
    expr: rate(http_requests_total{status=~"5.."}[5m]) > 0.1
    for: 2m
    labels:
      severity: critical
    annotations:
      summary: "High error rate detected"
      description: "Error rate is {{ $value }} errors per second"

  - alert: HighResponseTime
    expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 1
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "High response time detected"
      description: "95th percentile response time is {{ $value }} seconds"

  - alert: ServiceDown
    expr: up{job="formal-framework"} == 0
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "Service is down"
      description: "Formal framework service is not responding"

  - alert: HighMemoryUsage
    expr: (node_memory_MemTotal_bytes - node_memory_MemAvailable_bytes) / node_memory_MemTotal_bytes > 0.9
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "High memory usage"
      description: "Memory usage is {{ $value | humanizePercentage }}"

  - alert: HighCPUUsage
    expr: 100 - (avg by(instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100) > 80
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "High CPU usage"
      description: "CPU usage is {{ $value }}%"
```

### 3. Grafana仪表板

#### 应用监控仪表板

```json
{
  "dashboard": {
    "title": "Formal Framework Monitoring",
    "panels": [
      {
        "title": "Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_requests_total[5m])",
            "legendFormat": "{{method}} {{route}}"
          }
        ]
      },
      {
        "title": "Response Time",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "P95 Response Time"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_requests_total{status=~\"5..\"}[5m])",
            "legendFormat": "Error Rate"
          }
        ]
      },
      {
        "title": "Active Connections",
        "type": "graph",
        "targets": [
          {
            "expr": "node_netstat_Tcp_CurrEstab",
            "legendFormat": "Active Connections"
          }
        ]
      }
    ]
  }
}
```

## 📋 实施检查清单

### 工具链完善

- [ ] Docker镜像构建和优化
- [ ] Docker Compose服务编排
- [ ] Kubernetes部署清单
- [ ] 单元测试框架
- [ ] 集成测试框架
- [ ] 性能测试框架
- [ ] CI/CD流水线
- [ ] 监控和告警系统

### 质量保证

- [ ] 代码覆盖率 > 90%
- [ ] 测试通过率 100%
- [ ] 性能指标达标
- [ ] 安全扫描通过
- [ ] 文档完整性检查

### 部署验证

- [ ] 开发环境部署
- [ ] 测试环境部署
- [ ] 生产环境部署
- [ ] 回滚机制验证
- [ ] 监控告警验证

## 📞 联系方式

- **工具链负责人**：[姓名] <[邮箱]>
- **DevOps工程师**：[邮箱]
- **问题反馈**：[GitHub Issues链接]

---

*最后更新：2024-12-19*
*版本：v1.0.0*
