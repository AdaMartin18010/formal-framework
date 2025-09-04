# 验证脚本集合

本目录包含用于验证Formal Framework中各种不变式和约束的脚本和工具。

## 目录结构

```text
verification-scripts/
├── README.md                    # 本文档
├── tla+/                       # TLA+ 形式化验证脚本
├── z3/                         # Z3 定理证明器脚本
├── pytest/                     # Python 测试脚本
├── k6/                         # 性能测试脚本
├── contract-tests/             # 契约测试脚本
└── model-checkers/             # 模型检查器脚本
```

## 验证工具说明

### 1. TLA+ (Temporal Logic of Actions)

**用途**：形式化验证分布式系统的时序性质
**适用场景**：分布式一致性、并发安全性、死锁检测

**安装**：

```bash
# 下载 TLA+ Toolbox
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/TLAToolbox-1.8.0-linux.gtk.x86_64.zip
unzip TLAToolbox-1.8.0-linux.gtk.x86_64.zip

# 或使用 Docker
docker run -it --rm -v $(pwd):/workspace tlaplus/tlaplus
```

**使用示例**：

```tla
// 分布式一致性验证
EXTENDS Naturals, Sequences, TLC

VARIABLES nodes, values, committed

Init == 
    /\ nodes = {}
    /\ values = {}
    /\ committed = {}

Next == 
    \E node \in nodes:
        /\ values' = values \cup {node -> "value"}
        /\ committed' = committed \cup {node}
        /\ UNCHANGED <<nodes>>

Spec == Init /\ [][Next]_<<nodes, values, committed>>

// 不变式：所有节点最终都会提交
Consistency == \A node \in nodes: node \in committed
```

### 2. Z3 定理证明器

**用途**：自动定理证明、约束求解、模型检查
**适用场景**：数据完整性约束、业务规则验证、配置一致性

**安装**：

```bash
# Python 绑定
pip install z3-solver

# 命令行工具
# Ubuntu/Debian
sudo apt-get install z3

# macOS
brew install z3

# Windows
# 下载预编译二进制文件
```

**使用示例**：

```python
from z3 import *

def verify_data_constraints():
    """验证数据完整性约束"""
    s = Solver()
    
    # 定义变量
    x = Int('x')
    y = Int('y')
    z = Int('z')
    
    # 添加约束
    s.add(x > 0)
    s.add(y > 0)
    s.add(z == x + y)
    s.add(z <= 100)
    
    # 检查可满足性
    if s.check() == sat:
        model = s.model()
        print(f"x = {model[x]}")
        print(f"y = {model[y]}")
        print(f"z = {model[z]}")
        return True
    else:
        print("约束不可满足")
        return False

def verify_business_rules():
    """验证业务规则"""
    s = Solver()
    
    # 用户权限验证
    user_role = String('user_role')
    resource_access = String('resource_access')
    
    # 权限规则
    s.add(Or(user_role == "admin", user_role == "user"))
    s.add(Or(resource_access == "read", resource_access == "write"))
    
    # 普通用户不能写访问
    s.add(Implies(user_role == "user", resource_access == "read"))
    
    # 检查是否存在违反规则的情况
    s.add(user_role == "user")
    s.add(resource_access == "write")
    
    if s.check() == unsat:
        print("业务规则验证通过")
        return True
    else:
        print("业务规则验证失败")
        return False

if __name__ == "__main__":
    print("=== 数据约束验证 ===")
    verify_data_constraints()
    
    print("\n=== 业务规则验证 ===")
    verify_business_rules()
```

### 3. pytest 测试框架

**用途**：单元测试、集成测试、属性测试
**适用场景**：API验证、数据验证、业务逻辑验证

**安装**：

```bash
pip install pytest pytest-cov pytest-mock hypothesis
```

**使用示例**：

```python
import pytest
from hypothesis import given, strategies as st
import requests
import json

class TestAPIValidation:
    """API验证测试"""
    
    def test_endpoint_uniqueness(self):
        """测试端点唯一性约束"""
        endpoints = [
            {"id": "ep1", "path": "/api/v1/users", "method": "GET"},
            {"id": "ep2", "path": "/api/v1/users", "method": "POST"},
            {"id": "ep3", "path": "/api/v1/users", "method": "PUT"}
        ]
        
        # 检查路径唯一性
        paths = [ep["path"] for ep in endpoints]
        assert len(paths) == len(set(paths)), "路径必须唯一"
        
        # 检查ID唯一性
        ids = [ep["id"] for ep in endpoints]
        assert len(ids) == len(set(ids)), "ID必须唯一"
    
    @given(st.integers(min_value=1, max_value=100))
    def test_resource_constraints(self, value):
        """测试资源约束"""
        # 模拟资源验证
        assert value > 0, "资源值必须大于0"
        assert value <= 100, "资源值不能超过100"
    
    def test_contract_validation(self):
        """测试契约验证"""
        contract = {
            "version": "1.0.0",
            "parties": ["client", "server"],
            "terms": ["data_encryption", "audit_logging"],
            "validation": {
                "rules": ["encryption_required", "logging_required"]
            }
        }
        
        # 验证契约完整性
        assert "version" in contract, "契约必须有版本"
        assert "parties" in contract, "契约必须有参与方"
        assert "terms" in contract, "契约必须有条款"
        assert "validation" in contract, "契约必须有验证规则"
        
        # 验证验证规则
        assert len(contract["validation"]["rules"]) > 0, "验证规则不能为空"

class TestDataValidation:
    """数据验证测试"""
    
    def test_primary_key_uniqueness(self):
        """测试主键唯一性"""
        records = [
            {"id": 1, "name": "Alice"},
            {"id": 2, "name": "Bob"},
            {"id": 3, "name": "Charlie"}
        ]
        
        ids = [record["id"] for record in records]
        assert len(ids) == len(set(ids)), "主键必须唯一"
    
    def test_foreign_key_integrity(self):
        """测试外键完整性"""
        users = [{"id": 1, "name": "Alice"}, {"id": 2, "name": "Bob"}]
        orders = [
            {"id": 1, "user_id": 1, "amount": 100},
            {"id": 2, "user_id": 2, "amount": 200},
            {"id": 3, "user_id": 3, "amount": 300}  # 无效用户ID
        ]
        
        user_ids = {user["id"] for user in users}
        
        for order in orders:
            assert order["user_id"] in user_ids, f"订单 {order['id']} 引用了不存在的用户"
    
    @given(st.lists(st.integers(min_value=1, max_value=100), min_size=1, max_size=10))
    def test_data_type_constraints(self, values):
        """测试数据类型约束"""
        for value in values:
            assert isinstance(value, int), "值必须是整数"
            assert value > 0, "值必须大于0"
            assert value <= 100, "值不能超过100"

if __name__ == "__main__":
    pytest.main([__file__, "-v"])
```

### 4. k6 性能测试

**用途**：负载测试、压力测试、性能基准测试
**适用场景**：API性能验证、系统容量测试、SLA验证

**安装**：

```bash
# macOS
brew install k6

# Windows
choco install k6

# Linux
sudo gpg -k
sudo gpg --no-default-keyring --keyring /usr/share/keyrings/k6-archive-keyring.gpg --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys C5AD17C747E3415A3642D57D77C6C491D6AC1D69
echo "deb [signed-by=/usr/share/keyrings/k6-archive-keyring.gpg] https://dl.k6.io/deb stable main" | sudo tee /etc/apt/sources.list.d/k6.list
sudo apt-get update
sudo apt-get install k6

# Docker
docker pull grafana/k6
```

**使用示例**：

```javascript
import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate } from 'k6/metrics';

// 自定义指标
const errorRate = new Rate('errors');

// 测试配置
export const options = {
  stages: [
    { duration: '2m', target: 100 }, // 爬升到100用户
    { duration: '5m', target: 100 }, // 保持100用户5分钟
    { duration: '2m', target: 0 },   // 降到0用户
  ],
  thresholds: {
    http_req_duration: ['p(95)<500'], // 95%的请求必须在500ms内完成
    http_req_failed: ['rate<0.1'],    // 错误率必须小于10%
    errors: ['rate<0.1'],             // 自定义错误率必须小于10%
  },
};

// 测试数据
const BASE_URL = __ENV.BASE_URL || 'http://localhost:3000';

// 主测试函数
export default function () {
  // 健康检查
  const healthCheck = http.get(`${BASE_URL}/health`);
  check(healthCheck, {
    'health check status is 200': (r) => r.status === 200,
    'health check response time < 200ms': (r) => r.timings.duration < 200,
  });

  // API测试
  const payload = JSON.stringify({
    name: 'Test User',
    email: 'test@example.com',
    age: 25
  });

  const params = {
    headers: {
      'Content-Type': 'application/json',
      'Authorization': 'Bearer test-token'
    },
  };

  // POST请求测试
  const createResponse = http.post(`${BASE_URL}/api/users`, payload, params);
  check(createResponse, {
    'create user status is 201': (r) => r.status === 201,
    'create user response time < 300ms': (r) => r.timings.duration < 300,
    'create user has user id': (r) => r.json('id') !== undefined,
  });

  // 记录错误
  errorRate.add(createResponse.status !== 201);

  // GET请求测试
  if (createResponse.status === 201) {
    const userId = createResponse.json('id');
    const getUserResponse = http.get(`${BASE_URL}/api/users/${userId}`, params);
    
    check(getUserResponse, {
      'get user status is 200': (r) => r.status === 200,
      'get user response time < 200ms': (r) => r.timings.duration < 200,
      'get user returns correct data': (r) => r.json('name') === 'Test User',
    });

    errorRate.add(getUserResponse.status !== 200);
  }

  // 等待间隔
  sleep(1);
}

// 设置和清理函数
export function setup() {
  console.log('Setting up test environment...');
  // 可以在这里进行测试前的准备工作
}

export function teardown(data) {
  console.log('Cleaning up test environment...');
  // 可以在这里进行测试后的清理工作
}
```

## 运行验证脚本

### 1. 运行所有验证

```bash
# 创建虚拟环境
python -m venv venv
source venv/bin/activate  # Linux/macOS
# 或
venv\Scripts\activate     # Windows

# 安装依赖
pip install -r requirements.txt

# 运行所有验证
./run_all_verifications.sh
```

### 2. 运行特定验证

```bash
# TLA+ 验证
cd tla+/
tlc -config config.cfg model.tla

# Z3 验证
cd z3/
python verify_constraints.py

# pytest 验证
cd pytest/
pytest -v

# k6 性能测试
cd k6/
k6 run performance_test.js
```

## 验证结果解读

### 1. TLA+ 结果

- **SUCCESS**: 所有不变式都满足
- **FAILURE**: 发现违反不变式的情况
- **DEADLOCK**: 系统可能进入死锁状态

### 2. Z3 结果

- **sat**: 约束可满足，存在解
- **unsat**: 约束不可满足，无解
- **unknown**: 无法确定

### 3. pytest 结果

- **PASSED**: 测试通过
- **FAILED**: 测试失败
- **SKIPPED**: 测试跳过

### 4. k6 结果

- **阈值检查**: 性能指标是否满足SLA
- **错误率**: 系统错误率统计
- **响应时间**: 延迟分布统计

## 贡献指南

1. 创建新的验证脚本
2. 添加相应的测试用例
3. 更新README文档
4. 提交Pull Request

## 故障排除

### 常见问题

1. **TLA+ Toolbox启动失败**
   - 检查Java版本
   - 验证文件权限

2. **Z3安装失败**
   - 检查Python版本
   - 验证pip版本

3. **pytest导入错误**
   - 检查虚拟环境
   - 验证依赖安装

4. **k6性能测试失败**
   - 检查目标系统状态
   - 验证网络连接

### 获取帮助

- 查看工具官方文档
- 提交GitHub Issue
- 联系维护团队
