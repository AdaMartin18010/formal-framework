# API参考文档

## 概述

本文档提供了正式验证框架的完整API参考，包括所有端点、请求/响应格式、认证方式和示例代码。

## 基础信息

### 基础URL

- **生产环境**: `https://api.formal-framework.com`
- **测试环境**: `https://test-api.formal-framework.com`
- **开发环境**: `http://localhost:8080`

### 认证方式

所有API请求都需要在请求头中包含认证令牌：

```text
Authorization: Bearer <your-token>
```

### 内容类型

- **请求**: `application/json`
- **响应**: `application/json`

### 状态码

- `200` - 成功
- `201` - 创建成功
- `400` - 请求错误
- `401` - 未授权
- `403` - 禁止访问
- `404` - 资源不存在
- `500` - 服务器错误

## 通用响应格式

### 成功响应

```json
{
  "status": "success",
  "data": {},
  "message": "操作成功",
  "timestamp": "2024-01-01T00:00:00Z",
  "request_id": "uuid"
}
```

### 错误响应

```json
{
  "status": "error",
  "error": {
    "code": "400",
    "name": "BadRequest",
    "message": "请求参数错误",
    "details": {
      "field": "email",
      "reason": "invalid_format"
    }
  },
  "timestamp": "2024-01-01T00:00:00Z",
  "request_id": "uuid"
}
```

## 认证API

### 用户登录

```http
POST /api/v1/auth/login
```

**请求体**:

```json
{
  "email": "user@example.com",
  "password": "password123"
}
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...",
    "expires_in": 3600,
    "user": {
      "id": "uuid",
      "email": "user@example.com",
      "name": "John Doe",
      "role": "user"
    }
  }
}
```

### 用户注册

```http
POST /api/v1/auth/register
```

**请求体**:

```json
{
  "name": "John Doe",
  "email": "user@example.com",
  "password": "password123",
  "confirm_password": "password123"
}
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "user": {
      "id": "uuid",
      "email": "user@example.com",
      "name": "John Doe",
      "role": "user",
      "created_at": "2024-01-01T00:00:00Z"
    }
  }
}
```

### 刷新令牌

```http
POST /api/v1/auth/refresh
```

**请求头**:

```text
Authorization: Bearer <refresh-token>
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "token": "new-access-token",
    "expires_in": 3600
  }
}
```

### 用户登出

```http
POST /api/v1/auth/logout
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**响应**:

```json
{
  "status": "success",
  "message": "登出成功"
}
```

## 用户管理API

### 获取用户信息

```http
GET /api/v1/users/{user_id}
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "id": "uuid",
    "name": "John Doe",
    "email": "user@example.com",
    "role": "user",
    "created_at": "2024-01-01T00:00:00Z",
    "updated_at": "2024-01-01T00:00:00Z"
  }
}
```

### 更新用户信息

```http
PUT /api/v1/users/{user_id}
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**请求体**:

```json
{
  "name": "John Smith",
  "email": "john.smith@example.com"
}
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "id": "uuid",
    "name": "John Smith",
    "email": "john.smith@example.com",
    "role": "user",
    "updated_at": "2024-01-01T00:00:00Z"
  }
}
```

### 删除用户

```http
DELETE /api/v1/users/{user_id}
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**响应**:

```json
{
  "status": "success",
  "message": "用户删除成功"
}
```

## 验证API

### 创建验证任务

```http
POST /api/v1/verifications
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**请求体**:

```json
{
  "name": "系统验证任务",
  "type": "invariant_check",
  "target_url": "http://localhost:8080",
  "parameters": {
    "timeout": 30,
    "retries": 3
  }
}
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "id": "uuid",
    "name": "系统验证任务",
    "type": "invariant_check",
    "status": "pending",
    "created_at": "2024-01-01T00:00:00Z"
  }
}
```

### 获取验证任务状态

```http
GET /api/v1/verifications/{verification_id}
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "id": "uuid",
    "name": "系统验证任务",
    "type": "invariant_check",
    "status": "completed",
    "result": {
      "passed": true,
      "checks": [
        {
          "name": "HTTP健康检查",
          "passed": true,
          "message": "服务健康状态正常"
        }
      ]
    },
    "created_at": "2024-01-01T00:00:00Z",
    "completed_at": "2024-01-01T00:01:00Z"
  }
}
```

### 获取验证任务列表

```http
GET /api/v1/verifications
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**查询参数**:

- `page` - 页码 (默认: 1)
- `limit` - 每页数量 (默认: 20)
- `status` - 状态过滤
- `type` - 类型过滤

**响应**:

```json
{
  "status": "success",
  "data": {
    "verifications": [
      {
        "id": "uuid",
        "name": "系统验证任务",
        "type": "invariant_check",
        "status": "completed",
        "created_at": "2024-01-01T00:00:00Z"
      }
    ],
    "pagination": {
      "page": 1,
      "limit": 20,
      "total": 100,
      "pages": 5
    }
  }
}
```

## 性能测试API

### 创建性能测试

```http
POST /api/v1/performance-tests
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**请求体**:

```json
{
  "name": "API性能测试",
  "target_url": "http://localhost:8080/api/v1/users",
  "method": "GET",
  "parameters": {
    "requests": 1000,
    "workers": 10,
    "duration": 60
  }
}
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "id": "uuid",
    "name": "API性能测试",
    "status": "running",
    "created_at": "2024-01-01T00:00:00Z"
  }
}
```

### 获取性能测试结果

```http
GET /api/v1/performance-tests/{test_id}/results
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "id": "uuid",
    "name": "API性能测试",
    "status": "completed",
    "results": {
      "total_requests": 1000,
      "successful_requests": 995,
      "failed_requests": 5,
      "avg_response_time": 0.25,
      "p95_response_time": 0.5,
      "p99_response_time": 1.0,
      "requests_per_second": 16.67,
      "error_rate": 0.005
    },
    "created_at": "2024-01-01T00:00:00Z",
    "completed_at": "2024-01-01T00:01:00Z"
  }
}
```

## 监控API

### 获取系统指标

```http
GET /api/v1/metrics/system
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "cpu_usage": 45.2,
    "memory_usage": 67.8,
    "disk_usage": 23.1,
    "network_io": {
      "bytes_sent": 1024000,
      "bytes_received": 2048000
    },
    "timestamp": "2024-01-01T00:00:00Z"
  }
}
```

### 获取应用指标

```http
GET /api/v1/metrics/application
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "requests_total": 10000,
    "requests_per_second": 16.67,
    "avg_response_time": 0.25,
    "error_rate": 0.005,
    "active_connections": 150,
    "timestamp": "2024-01-01T00:00:00Z"
  }
}
```

### 获取业务指标

```http
GET /api/v1/metrics/business
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "active_users": 1250,
    "new_registrations": 45,
    "total_verifications": 5000,
    "successful_verifications": 4950,
    "verification_success_rate": 0.99,
    "timestamp": "2024-01-01T00:00:00Z"
  }
}
```

## 数据一致性API

### 检查数据一致性

```http
POST /api/v1/consistency/check
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**请求体**:

```json
{
  "services": [
    "http://service1:8080",
    "http://service2:8080"
  ],
  "check_type": "account_balance"
}
```

**响应**:

```json
{
  "status": "success",
  "data": {
    "check_id": "uuid",
    "status": "completed",
    "result": {
      "consistent": true,
      "checks": [
        {
          "name": "账户余额一致性",
          "passed": true,
          "message": "所有服务的账户数据一致"
        }
      ]
    },
    "created_at": "2024-01-01T00:00:00Z"
  }
}
```

### 获取一致性检查历史

```http
GET /api/v1/consistency/history
```

**请求头**:

```text
Authorization: Bearer <access-token>
```

**查询参数**:

- `page` - 页码
- `limit` - 每页数量
- `start_date` - 开始日期
- `end_date` - 结束日期

**响应**:

```json
{
  "status": "success",
  "data": {
    "checks": [
      {
        "id": "uuid",
        "check_type": "account_balance",
        "status": "completed",
        "consistent": true,
        "created_at": "2024-01-01T00:00:00Z"
      }
    ],
    "pagination": {
      "page": 1,
      "limit": 20,
      "total": 100,
      "pages": 5
    }
  }
}
```

## 健康检查API

### 系统健康检查

```http
GET /health
```

**响应**:

```json
{
  "status": "healthy",
  "timestamp": "2024-01-01T00:00:00Z",
  "version": "1.0.0",
  "services": {
    "database": "healthy",
    "redis": "healthy",
    "external_api": "healthy"
  }
}
```

### 详细健康检查

```http
GET /health/detailed
```

**响应**:

```json
{
  "status": "healthy",
  "timestamp": "2024-01-01T00:00:00Z",
  "version": "1.0.0",
  "services": {
    "database": {
      "status": "healthy",
      "response_time": 5,
      "last_check": "2024-01-01T00:00:00Z"
    },
    "redis": {
      "status": "healthy",
      "response_time": 2,
      "last_check": "2024-01-01T00:00:00Z"
    },
    "external_api": {
      "status": "healthy",
      "response_time": 100,
      "last_check": "2024-01-01T00:00:00Z"
    }
  }
}
```

## 错误代码

### 认证错误

- `AUTH_001` - 无效的认证令牌
- `AUTH_002` - 令牌已过期
- `AUTH_003` - 权限不足
- `AUTH_004` - 用户不存在

### 验证错误

- `VERIFY_001` - 验证任务创建失败
- `VERIFY_002` - 目标服务不可达
- `VERIFY_003` - 验证超时
- `VERIFY_004` - 验证配置错误

### 性能测试错误

- `PERF_001` - 性能测试创建失败
- `PERF_002` - 测试参数无效
- `PERF_003` - 测试执行失败
- `PERF_004` - 结果生成失败

### 系统错误

- `SYS_001` - 内部服务器错误
- `SYS_002` - 服务不可用
- `SYS_003` - 数据库连接失败
- `SYS_004` - 外部服务调用失败

## 示例代码

### Python示例

```python
import requests
import json

class FormalFrameworkAPI:
    def __init__(self, base_url, token):
        self.base_url = base_url
        self.headers = {
            'Authorization': f'Bearer {token}',
            'Content-Type': 'application/json'
        }
    
    def create_verification(self, name, target_url, verification_type):
        """创建验证任务"""
        data = {
            'name': name,
            'type': verification_type,
            'target_url': target_url
        }
        
        response = requests.post(
            f'{self.base_url}/api/v1/verifications',
            headers=self.headers,
            json=data
        )
        
        return response.json()
    
    def get_verification_status(self, verification_id):
        """获取验证任务状态"""
        response = requests.get(
            f'{self.base_url}/api/v1/verifications/{verification_id}',
            headers=self.headers
        )
        
        return response.json()
    
    def run_performance_test(self, target_url, requests_count=1000):
        """运行性能测试"""
        data = {
            'name': 'API性能测试',
            'target_url': target_url,
            'method': 'GET',
            'parameters': {
                'requests': requests_count,
                'workers': 10
            }
        }
        
        response = requests.post(
            f'{self.base_url}/api/v1/performance-tests',
            headers=self.headers,
            json=data
        )
        
        return response.json()

# 使用示例
api = FormalFrameworkAPI('https://api.formal-framework.com', 'your-token')

# 创建验证任务
verification = api.create_verification(
    '系统健康检查',
    'http://localhost:8080',
    'invariant_check'
)

# 获取验证结果
result = api.get_verification_status(verification['data']['id'])
print(f"验证结果: {result['data']['result']['passed']}")
```

### JavaScript示例

```javascript
class FormalFrameworkAPI {
    constructor(baseUrl, token) {
        this.baseUrl = baseUrl;
        this.headers = {
            'Authorization': `Bearer ${token}`,
            'Content-Type': 'application/json'
        };
    }
    
    async createVerification(name, targetUrl, verificationType) {
        const data = {
            name: name,
            type: verificationType,
            target_url: targetUrl
        };
        
        const response = await fetch(`${this.baseUrl}/api/v1/verifications`, {
            method: 'POST',
            headers: this.headers,
            body: JSON.stringify(data)
        });
        
        return await response.json();
    }
    
    async getVerificationStatus(verificationId) {
        const response = await fetch(`${this.baseUrl}/api/v1/verifications/${verificationId}`, {
            headers: this.headers
        });
        
        return await response.json();
    }
    
    async runPerformanceTest(targetUrl, requestsCount = 1000) {
        const data = {
            name: 'API性能测试',
            target_url: targetUrl,
            method: 'GET',
            parameters: {
                requests: requestsCount,
                workers: 10
            }
        };
        
        const response = await fetch(`${this.baseUrl}/api/v1/performance-tests`, {
            method: 'POST',
            headers: this.headers,
            body: JSON.stringify(data)
        });
        
        return await response.json();
    }
}

// 使用示例
const api = new FormalFrameworkAPI('https://api.formal-framework.com', 'your-token');

// 创建验证任务
api.createVerification('系统健康检查', 'http://localhost:8080', 'invariant_check')
    .then(verification => {
        console.log('验证任务创建成功:', verification);
        
        // 获取验证结果
        return api.getVerificationStatus(verification.data.id);
    })
    .then(result => {
        console.log('验证结果:', result.data.result.passed);
    })
    .catch(error => {
        console.error('错误:', error);
    });
```

### cURL示例

```bash
# 用户登录
curl -X POST https://api.formal-framework.com/api/v1/auth/login \
  -H "Content-Type: application/json" \
  -d '{
    "email": "user@example.com",
    "password": "password123"
  }'

# 创建验证任务
curl -X POST https://api.formal-framework.com/api/v1/verifications \
  -H "Authorization: Bearer your-token" \
  -H "Content-Type: application/json" \
  -d '{
    "name": "系统验证任务",
    "type": "invariant_check",
    "target_url": "http://localhost:8080"
  }'

# 获取验证任务状态
curl -X GET https://api.formal-framework.com/api/v1/verifications/verification-id \
  -H "Authorization: Bearer your-token"

# 运行性能测试
curl -X POST https://api.formal-framework.com/api/v1/performance-tests \
  -H "Authorization: Bearer your-token" \
  -H "Content-Type: application/json" \
  -d '{
    "name": "API性能测试",
    "target_url": "http://localhost:8080/api/v1/users",
    "method": "GET",
    "parameters": {
      "requests": 1000,
      "workers": 10
    }
  }'

# 获取系统指标
curl -X GET https://api.formal-framework.com/api/v1/metrics/system \
  -H "Authorization: Bearer your-token"
```

## 速率限制

API请求受到速率限制：

- **认证用户**: 1000 请求/小时
- **匿名用户**: 100 请求/小时
- **管理员用户**: 10000 请求/小时

当超过速率限制时，API会返回 `429 Too Many Requests` 状态码。

## 版本控制

API使用URL路径进行版本控制：

- 当前版本: `v1`
- 版本格式: `/api/v{version}/`

## 更新日志

### v1.0.0 (2024-01-01)

- 初始版本发布
- 支持用户认证和管理
- 支持验证任务创建和查询
- 支持性能测试
- 支持监控指标查询
- 支持数据一致性检查

## 支持

如果您在使用API时遇到问题，请：

1. 查看本文档的错误代码部分
2. 检查请求格式和参数
3. 联系技术支持: <support@formal-framework.com>
4. 提交GitHub Issue: <https://github.com/formal-framework/formal-framework/issues>
