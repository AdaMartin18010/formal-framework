# 集成测试框架

## 概述

集成测试框架提供了完整的集成测试解决方案，用于测试系统组件间的交互和集成，确保系统整体功能的正确性。

## 集成测试类型

### 1. 组件集成测试

#### 服务间集成测试

```python
import pytest
import requests
from unittest.mock import patch, Mock
from typing import Dict, Any
import json
import time

class TestServiceIntegration:
    """服务集成测试"""
    
    def setup_method(self):
        """测试前准备"""
        self.base_url = "http://localhost:8080"
        self.api_client = APIClient(self.base_url)
        self.test_data = TestDataGenerator()
    
    def test_user_service_integration(self):
        """测试用户服务集成"""
        # 创建测试用户
        user_data = self.test_data.create_user_data()
        user = self.api_client.create_user(user_data)
        
        # 验证用户创建
        assert user.id is not None
        assert user.email == user_data["email"]
        
        # 测试用户查询
        retrieved_user = self.api_client.get_user(user.id)
        assert retrieved_user.id == user.id
        assert retrieved_user.email == user.email
        
        # 测试用户更新
        updated_data = {"name": "Updated Name"}
        updated_user = self.api_client.update_user(user.id, updated_data)
        assert updated_user.name == "Updated Name"
        
        # 测试用户删除
        result = self.api_client.delete_user(user.id)
        assert result.success == True
        
        # 验证用户已删除
        with pytest.raises(UserNotFoundError):
            self.api_client.get_user(user.id)
    
    def test_order_service_integration(self):
        """测试订单服务集成"""
        # 创建用户
        user = self.api_client.create_user(self.test_data.create_user_data())
        
        # 创建订单
        order_data = self.test_data.create_order_data(user_id=user.id)
        order = self.api_client.create_order(order_data)
        
        # 验证订单创建
        assert order.id is not None
        assert order.user_id == user.id
        
        # 测试订单状态更新
        updated_order = self.api_client.update_order_status(order.id, "processing")
        assert updated_order.status == "processing"
        
        # 测试订单完成
        completed_order = self.api_client.complete_order(order.id)
        assert completed_order.status == "completed"
    
    def test_payment_service_integration(self):
        """测试支付服务集成"""
        # 创建用户和订单
        user = self.api_client.create_user(self.test_data.create_user_data())
        order = self.api_client.create_order(
            self.test_data.create_order_data(user_id=user.id)
        )
        
        # 创建支付
        payment_data = self.test_data.create_payment_data(
            order_id=order.id,
            amount=order.total_amount
        )
        payment = self.api_client.create_payment(payment_data)
        
        # 验证支付创建
        assert payment.id is not None
        assert payment.order_id == order.id
        assert payment.amount == order.total_amount
        
        # 测试支付处理
        processed_payment = self.api_client.process_payment(payment.id)
        assert processed_payment.status == "completed"
        
        # 验证订单状态更新
        updated_order = self.api_client.get_order(order.id)
        assert updated_order.status == "paid"
    
    def test_notification_service_integration(self):
        """测试通知服务集成"""
        # 创建用户
        user = self.api_client.create_user(self.test_data.create_user_data())
        
        # 发送通知
        notification_data = {
            "user_id": user.id,
            "type": "welcome",
            "message": "Welcome to our service!"
        }
        notification = self.api_client.send_notification(notification_data)
        
        # 验证通知发送
        assert notification.id is not None
        assert notification.user_id == user.id
        
        # 测试通知状态查询
        notifications = self.api_client.get_user_notifications(user.id)
        assert len(notifications) > 0
        assert any(n.id == notification.id for n in notifications)

class TestDatabaseIntegration:
    """数据库集成测试"""
    
    def setup_method(self):
        """测试前准备"""
        self.db_session = create_test_database_session()
        self.test_data = TestDataGenerator()
    
    def test_user_database_integration(self):
        """测试用户数据库集成"""
        # 创建用户
        user_data = self.test_data.create_user_data()
        user = User(**user_data)
        self.db_session.add(user)
        self.db_session.commit()
        
        # 验证用户创建
        assert user.id is not None
        assert user.email == user_data["email"]
        
        # 测试用户查询
        retrieved_user = self.db_session.query(User).filter_by(id=user.id).first()
        assert retrieved_user is not None
        assert retrieved_user.email == user.email
        
        # 测试用户更新
        retrieved_user.name = "Updated Name"
        self.db_session.commit()
        
        updated_user = self.db_session.query(User).filter_by(id=user.id).first()
        assert updated_user.name == "Updated Name"
        
        # 测试用户删除
        self.db_session.delete(retrieved_user)
        self.db_session.commit()
        
        deleted_user = self.db_session.query(User).filter_by(id=user.id).first()
        assert deleted_user is None
    
    def test_order_database_integration(self):
        """测试订单数据库集成"""
        # 创建用户
        user = User(**self.test_data.create_user_data())
        self.db_session.add(user)
        self.db_session.commit()
        
        # 创建订单
        order_data = self.test_data.create_order_data(user_id=user.id)
        order = Order(**order_data)
        self.db_session.add(order)
        self.db_session.commit()
        
        # 验证订单创建
        assert order.id is not None
        assert order.user_id == user.id
        
        # 测试订单查询
        retrieved_order = self.db_session.query(Order).filter_by(id=order.id).first()
        assert retrieved_order is not None
        assert retrieved_order.user_id == user.id
        
        # 测试关联查询
        user_with_orders = self.db_session.query(User).filter_by(id=user.id).first()
        assert len(user_with_orders.orders) > 0
        assert user_with_orders.orders[0].id == order.id
    
    def test_transaction_integration(self):
        """测试事务集成"""
        # 测试事务回滚
        user_data = self.test_data.create_user_data()
        user = User(**user_data)
        self.db_session.add(user)
        
        # 故意创建无效订单
        invalid_order = Order(user_id=user.id, total_amount=-100)  # 负数金额
        self.db_session.add(invalid_order)
        
        # 提交事务应该失败
        with pytest.raises(Exception):
            self.db_session.commit()
        
        # 验证数据未保存
        self.db_session.rollback()
        user_count = self.db_session.query(User).count()
        order_count = self.db_session.query(Order).count()
        assert user_count == 0
        assert order_count == 0

class TestAPIIntegration:
    """API集成测试"""
    
    def setup_method(self):
        """测试前准备"""
        self.base_url = "http://localhost:8080"
        self.api_client = APIClient(self.base_url)
        self.test_data = TestDataGenerator()
    
    def test_api_authentication_integration(self):
        """测试API认证集成"""
        # 创建用户
        user_data = self.test_data.create_user_data()
        user = self.api_client.create_user(user_data)
        
        # 登录获取token
        login_data = {
            "email": user.email,
            "password": user_data["password"]
        }
        auth_response = self.api_client.login(login_data)
        assert auth_response.token is not None
        
        # 使用token访问受保护资源
        headers = {"Authorization": f"Bearer {auth_response.token}"}
        profile = self.api_client.get_user_profile(headers=headers)
        assert profile.id == user.id
        
        # 测试token过期
        expired_token = "expired_token"
        headers = {"Authorization": f"Bearer {expired_token}"}
        with pytest.raises(UnauthorizedError):
            self.api_client.get_user_profile(headers=headers)
    
    def test_api_rate_limiting_integration(self):
        """测试API限流集成"""
        # 快速发送多个请求
        for i in range(10):
            response = self.api_client.get_public_data()
            assert response.status_code == 200
        
        # 超过限流阈值
        with pytest.raises(RateLimitExceededError):
            self.api_client.get_public_data()
    
    def test_api_error_handling_integration(self):
        """测试API错误处理集成"""
        # 测试404错误
        with pytest.raises(NotFoundError):
            self.api_client.get_user("non-existent-id")
        
        # 测试400错误
        invalid_data = {"invalid_field": "invalid_value"}
        with pytest.raises(BadRequestError):
            self.api_client.create_user(invalid_data)
        
        # 测试500错误
        with patch('service.external_api_call') as mock_call:
            mock_call.side_effect = Exception("Internal server error")
            with pytest.raises(InternalServerError):
                self.api_client.get_external_data()

class TestMessageQueueIntegration:
    """消息队列集成测试"""
    
    def setup_method(self):
        """测试前准备"""
        self.message_queue = MessageQueue("test-queue")
        self.test_data = TestDataGenerator()
    
    def test_message_publishing_integration(self):
        """测试消息发布集成"""
        # 发布消息
        message_data = self.test_data.create_message_data()
        message_id = self.message_queue.publish("test-topic", message_data)
        
        # 验证消息发布
        assert message_id is not None
        
        # 消费消息
        consumed_message = self.message_queue.consume("test-topic")
        assert consumed_message.id == message_id
        assert consumed_message.data == message_data
    
    def test_message_processing_integration(self):
        """测试消息处理集成"""
        # 发布处理消息
        order_data = self.test_data.create_order_data()
        message_id = self.message_queue.publish("order-processing", order_data)
        
        # 等待消息处理
        time.sleep(1)
        
        # 验证处理结果
        processed_order = self.api_client.get_order(order_data["id"])
        assert processed_order.status == "processed"
    
    def test_message_error_handling_integration(self):
        """测试消息错误处理集成"""
        # 发布错误消息
        invalid_data = {"invalid": "data"}
        message_id = self.message_queue.publish("test-topic", invalid_data)
        
        # 等待错误处理
        time.sleep(1)
        
        # 验证错误处理
        error_logs = self.message_queue.get_error_logs()
        assert len(error_logs) > 0
        assert any(log.message_id == message_id for log in error_logs)

class TestCacheIntegration:
    """缓存集成测试"""
    
    def setup_method(self):
        """测试前准备"""
        self.cache = Cache("test-cache")
        self.test_data = TestDataGenerator()
    
    def test_cache_set_get_integration(self):
        """测试缓存设置获取集成"""
        # 设置缓存
        key = "test-key"
        value = {"data": "test-value"}
        self.cache.set(key, value, ttl=60)
        
        # 获取缓存
        cached_value = self.cache.get(key)
        assert cached_value == value
        
        # 测试缓存过期
        self.cache.set(key, value, ttl=1)
        time.sleep(2)
        expired_value = self.cache.get(key)
        assert expired_value is None
    
    def test_cache_invalidation_integration(self):
        """测试缓存失效集成"""
        # 设置缓存
        key = "test-key"
        value = {"data": "test-value"}
        self.cache.set(key, value)
        
        # 验证缓存存在
        assert self.cache.get(key) == value
        
        # 失效缓存
        self.cache.delete(key)
        
        # 验证缓存已失效
        assert self.cache.get(key) is None
    
    def test_cache_pattern_integration(self):
        """测试缓存模式集成"""
        # 设置多个缓存项
        keys = ["user:1", "user:2", "order:1", "order:2"]
        for key in keys:
            self.cache.set(key, {"id": key})
        
        # 按模式获取缓存
        user_keys = self.cache.get_pattern("user:*")
        assert len(user_keys) == 2
        assert "user:1" in user_keys
        assert "user:2" in user_keys
        
        # 按模式删除缓存
        self.cache.delete_pattern("user:*")
        assert self.cache.get("user:1") is None
        assert self.cache.get("user:2") is None
        assert self.cache.get("order:1") is not None
```

### 2. 端到端集成测试

#### 完整业务流程测试

```python
class TestEndToEndIntegration:
    """端到端集成测试"""
    
    def setup_method(self):
        """测试前准备"""
        self.api_client = APIClient("http://localhost:8080")
        self.test_data = TestDataGenerator()
    
    def test_complete_user_journey(self):
        """测试完整用户旅程"""
        # 1. 用户注册
        user_data = self.test_data.create_user_data()
        user = self.api_client.register_user(user_data)
        assert user.id is not None
        
        # 2. 用户登录
        login_data = {
            "email": user.email,
            "password": user_data["password"]
        }
        auth_response = self.api_client.login(login_data)
        assert auth_response.token is not None
        
        # 3. 创建订单
        order_data = self.test_data.create_order_data(user_id=user.id)
        order = self.api_client.create_order(order_data, token=auth_response.token)
        assert order.id is not None
        
        # 4. 处理支付
        payment_data = self.test_data.create_payment_data(
            order_id=order.id,
            amount=order.total_amount
        )
        payment = self.api_client.create_payment(payment_data, token=auth_response.token)
        assert payment.id is not None
        
        # 5. 确认订单
        confirmed_order = self.api_client.confirm_order(order.id, token=auth_response.token)
        assert confirmed_order.status == "confirmed"
        
        # 6. 发送通知
        notifications = self.api_client.get_user_notifications(user.id, token=auth_response.token)
        assert len(notifications) > 0
        
        # 7. 用户查看订单历史
        order_history = self.api_client.get_user_orders(user.id, token=auth_response.token)
        assert len(order_history) > 0
        assert any(o.id == order.id for o in order_history)
    
    def test_error_recovery_flow(self):
        """测试错误恢复流程"""
        # 1. 创建用户
        user = self.api_client.create_user(self.test_data.create_user_data())
        
        # 2. 创建订单
        order = self.api_client.create_order(
            self.test_data.create_order_data(user_id=user.id)
        )
        
        # 3. 模拟支付失败
        with patch('payment_service.process_payment') as mock_payment:
            mock_payment.side_effect = PaymentError("Payment failed")
            
            with pytest.raises(PaymentError):
                self.api_client.process_payment(order.id)
        
        # 4. 验证订单状态
        updated_order = self.api_client.get_order(order.id)
        assert updated_order.status == "payment_failed"
        
        # 5. 重试支付
        payment_data = self.test_data.create_payment_data(
            order_id=order.id,
            amount=order.total_amount
        )
        payment = self.api_client.create_payment(payment_data)
        assert payment.id is not None
        
        # 6. 成功处理支付
        processed_payment = self.api_client.process_payment(payment.id)
        assert processed_payment.status == "completed"
        
        # 7. 验证订单状态更新
        final_order = self.api_client.get_order(order.id)
        assert final_order.status == "paid"
```

## 测试工具和实用程序

### 1. 测试环境管理

#### 测试环境设置

```python
import docker
import time
import requests
from typing import Dict, Any, List
import subprocess
import os

class TestEnvironmentManager:
    """测试环境管理器"""
    
    def __init__(self):
        self.docker_client = docker.from_env()
        self.containers = []
        self.services = {}
    
    def start_test_environment(self):
        """启动测试环境"""
        # 启动数据库
        db_container = self.docker_client.containers.run(
            "postgres:15",
            environment={
                "POSTGRES_DB": "test_db",
                "POSTGRES_USER": "test_user",
                "POSTGRES_PASSWORD": "test_password"
            },
            ports={"5432/tcp": 5432},
            detach=True
        )
        self.containers.append(db_container)
        
        # 启动Redis
        redis_container = self.docker_client.containers.run(
            "redis:7",
            ports={"6379/tcp": 6379},
            detach=True
        )
        self.containers.append(redis_container)
        
        # 启动应用服务
        app_container = self.docker_client.containers.run(
            "formal-framework-app:test",
            ports={"8080/tcp": 8080},
            environment={
                "DATABASE_URL": "postgresql://test_user:test_password@localhost:5432/test_db",
                "REDIS_URL": "redis://localhost:6379"
            },
            detach=True
        )
        self.containers.append(app_container)
        
        # 等待服务启动
        self.wait_for_services()
    
    def wait_for_services(self):
        """等待服务启动"""
        services = [
            {"name": "database", "port": 5432},
            {"name": "redis", "port": 6379},
            {"name": "app", "port": 8080}
        ]
        
        for service in services:
            self.wait_for_port(service["port"], timeout=30)
    
    def wait_for_port(self, port: int, timeout: int = 30):
        """等待端口可用"""
        start_time = time.time()
        while time.time() - start_time < timeout:
            try:
                response = requests.get(f"http://localhost:{port}/health", timeout=1)
                if response.status_code == 200:
                    return True
            except requests.exceptions.RequestException:
                pass
            time.sleep(1)
        
        raise TimeoutError(f"Service on port {port} did not start within {timeout} seconds")
    
    def stop_test_environment(self):
        """停止测试环境"""
        for container in self.containers:
            container.stop()
            container.remove()
        self.containers.clear()
    
    def cleanup_test_data(self):
        """清理测试数据"""
        # 清理数据库
        subprocess.run([
            "psql", "-h", "localhost", "-U", "test_user", "-d", "test_db",
            "-c", "TRUNCATE TABLE users, orders, payments CASCADE;"
        ])
        
        # 清理Redis
        redis_client = redis.Redis(host="localhost", port=6379, db=0)
        redis_client.flushdb()

# 测试环境fixture
@pytest.fixture(scope="session")
def test_environment():
    """测试环境fixture"""
    env_manager = TestEnvironmentManager()
    env_manager.start_test_environment()
    yield env_manager
    env_manager.stop_test_environment()

@pytest.fixture
def clean_test_environment(test_environment):
    """清理测试环境fixture"""
    yield test_environment
    test_environment.cleanup_test_data()
```

### 2. 测试数据管理

#### 测试数据工厂

```python
class IntegrationTestDataFactory:
    """集成测试数据工厂"""
    
    def __init__(self):
        self.faker = Faker()
        self.created_data = {
            "users": [],
            "orders": [],
            "payments": []
        }
    
    def create_user_data(self) -> Dict[str, Any]:
        """创建用户数据"""
        user_data = {
            "name": self.faker.name(),
            "email": self.faker.email(),
            "password": "TestPassword123!",
            "age": self.faker.random_int(min=18, max=80)
        }
        self.created_data["users"].append(user_data)
        return user_data
    
    def create_order_data(self, user_id: str = None) -> Dict[str, Any]:
        """创建订单数据"""
        order_data = {
            "user_id": user_id or self.faker.uuid4(),
            "items": [
                {
                    "name": self.faker.word(),
                    "price": self.faker.random_int(min=10, max=100),
                    "quantity": self.faker.random_int(min=1, max=5)
                }
                for _ in range(self.faker.random_int(min=1, max=3))
            ],
            "total_amount": self.faker.random_int(min=50, max=500)
        }
        self.created_data["orders"].append(order_data)
        return order_data
    
    def create_payment_data(self, order_id: str = None, amount: float = None) -> Dict[str, Any]:
        """创建支付数据"""
        payment_data = {
            "order_id": order_id or self.faker.uuid4(),
            "amount": amount or self.faker.random_int(min=50, max=500),
            "payment_method": "credit_card",
            "card_number": "4111111111111111",
            "expiry_date": "12/25",
            "cvv": "123"
        }
        self.created_data["payments"].append(payment_data)
        return payment_data
    
    def cleanup_created_data(self):
        """清理创建的数据"""
        # 这里可以实现清理逻辑
        self.created_data = {
            "users": [],
            "orders": [],
            "payments": []
        }
```

## 测试配置和运行

### 1. 集成测试配置

#### pytest集成测试配置

```ini
# pytest-integration.ini
[tool:pytest]
testpaths = tests/integration
python_files = test_*_integration.py
python_classes = Test*Integration
python_functions = test_*
addopts = 
    --strict-markers
    --verbose
    --tb=short
    --cov=src
    --cov-report=html
    --cov-report=term-missing
    --cov-fail-under=70
markers =
    integration: marks tests as integration tests
    slow: marks tests as slow
    database: marks tests that require database
    api: marks tests that require API
    message_queue: marks tests that require message queue
filterwarnings =
    ignore::DeprecationWarning
    ignore::PendingDeprecationWarning
```

### 2. 持续集成配置

#### GitHub Actions集成测试

```yaml
name: Integration Tests

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  integration-tests:
    runs-on: ubuntu-latest
    
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
      
      redis:
        image: redis:7
        options: >-
          --health-cmd "redis-cli ping"
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 6379:6379
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.11'
    
    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install -r requirements.txt
        pip install -r requirements-test.txt
    
    - name: Run database migrations
      run: |
        python manage.py migrate
      env:
        DATABASE_URL: postgresql://postgres:postgres@localhost:5432/test_db
        REDIS_URL: redis://localhost:6379
    
    - name: Start application
      run: |
        python manage.py runserver &
        sleep 30
      env:
        DATABASE_URL: postgresql://postgres:postgres@localhost:5432/test_db
        REDIS_URL: redis://localhost:6379
    
    - name: Run integration tests
      run: |
        pytest tests/integration/ --cov=src --cov-report=xml
      env:
        DATABASE_URL: postgresql://postgres:postgres@localhost:5432/test_db
        REDIS_URL: redis://localhost:6379
        API_BASE_URL: http://localhost:8000
    
    - name: Upload coverage to Codecov
      uses: codecov/codecov-action@v3
      with:
        file: ./coverage.xml
        flags: integration
        name: codecov-umbrella
```

## 最佳实践

1. **测试隔离**: 确保集成测试之间相互独立
2. **环境管理**: 使用容器化环境进行测试
3. **数据清理**: 测试后清理测试数据
4. **错误处理**: 测试各种错误场景
5. **性能考虑**: 监控集成测试性能
6. **持续集成**: 在CI/CD中运行集成测试
7. **文档维护**: 保持集成测试文档的更新

## 相关文档

- [单元测试框架](unit-testing.md)
- [端到端测试框架](e2e-testing.md)
- [性能测试框架](performance-testing.md)
- [验证脚本](../../verification-scripts/README.md)
