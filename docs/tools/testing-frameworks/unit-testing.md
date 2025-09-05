# 单元测试框架

## 概述

单元测试框架提供了完整的单元测试解决方案，支持多种编程语言和测试场景，确保代码质量和可靠性。

## 支持的语言和框架

### 1. Python测试框架

#### pytest框架

```python
import pytest
from unittest.mock import Mock, patch
from typing import List, Dict, Any
import sys
import os

# 添加项目根目录到Python路径
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))

class TestDataValidator:
    """数据验证器测试"""
    
    def setup_method(self):
        """测试前准备"""
        self.validator = DataValidator()
    
    def test_valid_email(self):
        """测试有效邮箱"""
        valid_emails = [
            "test@example.com",
            "user.name@domain.co.uk",
            "admin+tag@company.org"
        ]
        
        for email in valid_emails:
            assert self.validator.validate_email(email) == True
    
    def test_invalid_email(self):
        """测试无效邮箱"""
        invalid_emails = [
            "invalid-email",
            "@domain.com",
            "user@",
            "user@domain"
        ]
        
        for email in invalid_emails:
            assert self.validator.validate_email(email) == False
    
    @pytest.mark.parametrize("email,expected", [
        ("test@example.com", True),
        ("invalid-email", False),
        ("user@domain.co.uk", True),
        ("@domain.com", False)
    ])
    def test_email_validation_parametrized(self, email, expected):
        """参数化测试邮箱验证"""
        assert self.validator.validate_email(email) == expected
    
    def test_validate_user_data(self):
        """测试用户数据验证"""
        valid_user_data = {
            "name": "John Doe",
            "email": "john@example.com",
            "age": 25
        }
        
        result = self.validator.validate_user_data(valid_user_data)
        assert result.is_valid == True
        assert len(result.errors) == 0
    
    def test_validate_user_data_with_errors(self):
        """测试用户数据验证错误"""
        invalid_user_data = {
            "name": "",
            "email": "invalid-email",
            "age": -5
        }
        
        result = self.validator.validate_user_data(invalid_user_data)
        assert result.is_valid == False
        assert len(result.errors) > 0
    
    @patch('requests.get')
    def test_external_api_call(self, mock_get):
        """测试外部API调用"""
        # 模拟API响应
        mock_response = Mock()
        mock_response.status_code = 200
        mock_response.json.return_value = {"status": "success"}
        mock_get.return_value = mock_response
        
        # 测试API调用
        api_client = APIClient()
        result = api_client.get_data("test-endpoint")
        
        assert result["status"] == "success"
        mock_get.assert_called_once_with("https://api.example.com/test-endpoint")
    
    def test_database_operation(self):
        """测试数据库操作"""
        with patch('database.connection') as mock_db:
            mock_cursor = Mock()
            mock_cursor.fetchone.return_value = (1, "test@example.com")
            mock_db.cursor.return_value.__enter__.return_value = mock_cursor
            
            db_service = DatabaseService()
            user = db_service.get_user_by_id(1)
            
            assert user.id == 1
            assert user.email == "test@example.com"
    
    @pytest.mark.asyncio
    async def test_async_function(self):
        """测试异步函数"""
        async_service = AsyncService()
        result = await async_service.process_data("test-data")
        
        assert result == "processed-test-data"
    
    def test_exception_handling(self):
        """测试异常处理"""
        with pytest.raises(ValidationError) as exc_info:
            self.validator.validate_required_field(None)
        
        assert "Field is required" in str(exc_info.value)
    
    def teardown_method(self):
        """测试后清理"""
        # 清理测试数据
        pass

class TestBusinessLogic:
    """业务逻辑测试"""
    
    def test_calculate_total_price(self):
        """测试价格计算"""
        calculator = PriceCalculator()
        
        items = [
            {"price": 10.0, "quantity": 2},
            {"price": 15.0, "quantity": 1},
            {"price": 5.0, "quantity": 3}
        ]
        
        total = calculator.calculate_total(items)
        expected = (10.0 * 2) + (15.0 * 1) + (5.0 * 3)
        
        assert total == expected
    
    def test_apply_discount(self):
        """测试折扣应用"""
        calculator = PriceCalculator()
        
        # 测试10%折扣
        discounted_price = calculator.apply_discount(100.0, 0.1)
        assert discounted_price == 90.0
        
        # 测试0折扣
        discounted_price = calculator.apply_discount(100.0, 0.0)
        assert discounted_price == 100.0
        
        # 测试100%折扣
        discounted_price = calculator.apply_discount(100.0, 1.0)
        assert discounted_price == 0.0
    
    def test_invalid_discount(self):
        """测试无效折扣"""
        calculator = PriceCalculator()
        
        with pytest.raises(ValueError):
            calculator.apply_discount(100.0, -0.1)  # 负折扣
        
        with pytest.raises(ValueError):
            calculator.apply_discount(100.0, 1.1)   # 超过100%折扣

# 测试配置
@pytest.fixture(scope="session")
def test_database():
    """测试数据库fixture"""
    db = create_test_database()
    yield db
    db.cleanup()

@pytest.fixture
def sample_user():
    """示例用户fixture"""
    return {
        "id": 1,
        "name": "Test User",
        "email": "test@example.com",
        "age": 25
    }

# 测试标记
@pytest.mark.slow
def test_large_data_processing():
    """慢速测试"""
    processor = DataProcessor()
    result = processor.process_large_dataset()
    assert result.success == True

@pytest.mark.integration
def test_database_integration():
    """集成测试"""
    db_service = DatabaseService()
    user = db_service.create_user({"name": "Test", "email": "test@example.com"})
    assert user.id is not None
```

#### 测试配置

```python
# conftest.py
import pytest
import tempfile
import os
from unittest.mock import Mock

@pytest.fixture(scope="session")
def test_config():
    """测试配置"""
    return {
        "database_url": "sqlite:///test.db",
        "api_base_url": "https://test-api.example.com",
        "log_level": "DEBUG"
    }

@pytest.fixture
def temp_file():
    """临时文件fixture"""
    with tempfile.NamedTemporaryFile(delete=False) as f:
        f.write(b"test data")
        temp_path = f.name
    
    yield temp_path
    
    # 清理
    if os.path.exists(temp_path):
        os.unlink(temp_path)

@pytest.fixture
def mock_external_service():
    """模拟外部服务"""
    mock_service = Mock()
    mock_service.get_data.return_value = {"status": "success"}
    return mock_service

# 测试标记配置
def pytest_configure(config):
    """pytest配置"""
    config.addinivalue_line(
        "markers", "slow: marks tests as slow (deselect with '-m \"not slow\"')"
    )
    config.addinivalue_line(
        "markers", "integration: marks tests as integration tests"
    )
    config.addinivalue_line(
        "markers", "unit: marks tests as unit tests"
    )
```

### 2. JavaScript/Node.js测试框架

#### Jest框架

```javascript
// __tests__/dataValidator.test.js
const DataValidator = require('../src/dataValidator');
const APIClient = require('../src/apiClient');

describe('DataValidator', () => {
  let validator;

  beforeEach(() => {
    validator = new DataValidator();
  });

  afterEach(() => {
    // 清理
  });

  describe('email validation', () => {
    test('should validate correct email addresses', () => {
      const validEmails = [
        'test@example.com',
        'user.name@domain.co.uk',
        'admin+tag@company.org'
      ];

      validEmails.forEach(email => {
        expect(validator.validateEmail(email)).toBe(true);
      });
    });

    test('should reject invalid email addresses', () => {
      const invalidEmails = [
        'invalid-email',
        '@domain.com',
        'user@',
        'user@domain'
      ];

      invalidEmails.forEach(email => {
        expect(validator.validateEmail(email)).toBe(false);
      });
    });

    test.each([
      ['test@example.com', true],
      ['invalid-email', false],
      ['user@domain.co.uk', true],
      ['@domain.com', false]
    ])('should validate email %s as %s', (email, expected) => {
      expect(validator.validateEmail(email)).toBe(expected);
    });
  });

  describe('user data validation', () => {
    test('should validate correct user data', () => {
      const validUserData = {
        name: 'John Doe',
        email: 'john@example.com',
        age: 25
      };

      const result = validator.validateUserData(validUserData);
      expect(result.isValid).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    test('should return errors for invalid user data', () => {
      const invalidUserData = {
        name: '',
        email: 'invalid-email',
        age: -5
      };

      const result = validator.validateUserData(invalidUserData);
      expect(result.isValid).toBe(false);
      expect(result.errors.length).toBeGreaterThan(0);
    });
  });

  describe('API client', () => {
    test('should make successful API call', async () => {
      const mockResponse = {
        status: 200,
        data: { status: 'success' }
      };

      jest.spyOn(APIClient.prototype, 'get').mockResolvedValue(mockResponse);

      const client = new APIClient();
      const result = await client.getData('test-endpoint');

      expect(result.status).toBe('success');
      expect(client.get).toHaveBeenCalledWith('test-endpoint');
    });

    test('should handle API errors', async () => {
      const mockError = new Error('API Error');
      jest.spyOn(APIClient.prototype, 'get').mockRejectedValue(mockError);

      const client = new APIClient();
      
      await expect(client.getData('test-endpoint')).rejects.toThrow('API Error');
    });
  });

  describe('async operations', () => {
    test('should handle async data processing', async () => {
      const asyncService = new AsyncService();
      const result = await asyncService.processData('test-data');

      expect(result).toBe('processed-test-data');
    });
  });

  describe('error handling', () => {
    test('should throw validation error for required field', () => {
      expect(() => {
        validator.validateRequiredField(null);
      }).toThrow('Field is required');
    });
  });
});

// 测试工具函数
describe('Test utilities', () => {
  test('should create test user', () => {
    const testUser = createTestUser({
      name: 'Test User',
      email: 'test@example.com'
    });

    expect(testUser.id).toBeDefined();
    expect(testUser.name).toBe('Test User');
    expect(testUser.email).toBe('test@example.com');
  });

  test('should clean up test data', () => {
    const testData = createTestData();
    expect(testData).toBeDefined();

    cleanupTestData(testData);
    expect(getTestData(testData.id)).toBeNull();
  });
});

// 测试配置
// jest.config.js
module.exports = {
  testEnvironment: 'node',
  setupFilesAfterEnv: ['<rootDir>/tests/setup.js'],
  testMatch: [
    '**/__tests__/**/*.test.js',
    '**/?(*.)+(spec|test).js'
  ],
  collectCoverageFrom: [
    'src/**/*.js',
    '!src/**/*.test.js'
  ],
  coverageThreshold: {
    global: {
      branches: 80,
      functions: 80,
      lines: 80,
      statements: 80
    }
  },
  testTimeout: 10000
};
```

### 3. Go测试框架

#### 标准测试包

```go
package main

import (
    "testing"
    "github.com/stretchr/testify/assert"
    "github.com/stretchr/testify/mock"
    "github.com/stretchr/testify/suite"
)

// 测试套件
type DataValidatorTestSuite struct {
    suite.Suite
    validator *DataValidator
}

func (suite *DataValidatorTestSuite) SetupTest() {
    suite.validator = NewDataValidator()
}

func (suite *DataValidatorTestSuite) TearDownTest() {
    // 清理
}

func (suite *DataValidatorTestSuite) TestValidEmail() {
    validEmails := []string{
        "test@example.com",
        "user.name@domain.co.uk",
        "admin+tag@company.org",
    }

    for _, email := range validEmails {
        suite.True(suite.validator.ValidateEmail(email), "Email should be valid: %s", email)
    }
}

func (suite *DataValidatorTestSuite) TestInvalidEmail() {
    invalidEmails := []string{
        "invalid-email",
        "@domain.com",
        "user@",
        "user@domain",
    }

    for _, email := range invalidEmails {
        suite.False(suite.validator.ValidateEmail(email), "Email should be invalid: %s", email)
    }
}

func (suite *DataValidatorTestSuite) TestValidateUserData() {
    validUserData := &UserData{
        Name:  "John Doe",
        Email: "john@example.com",
        Age:   25,
    }

    result := suite.validator.ValidateUserData(validUserData)
    suite.True(result.IsValid)
    suite.Empty(result.Errors)
}

func (suite *DataValidatorTestSuite) TestValidateUserDataWithErrors() {
    invalidUserData := &UserData{
        Name:  "",
        Email: "invalid-email",
        Age:   -5,
    }

    result := suite.validator.ValidateUserData(invalidUserData)
    suite.False(result.IsValid)
    suite.NotEmpty(result.Errors)
}

// 运行测试套件
func TestDataValidatorTestSuite(t *testing.T) {
    suite.Run(t, new(DataValidatorTestSuite))
}

// 单独测试函数
func TestCalculateTotal(t *testing.T) {
    calculator := NewPriceCalculator()
    
    items := []Item{
        {Price: 10.0, Quantity: 2},
        {Price: 15.0, Quantity: 1},
        {Price: 5.0, Quantity: 3},
    }
    
    total := calculator.CalculateTotal(items)
    expected := (10.0 * 2) + (15.0 * 1) + (5.0 * 3)
    
    assert.Equal(t, expected, total)
}

func TestApplyDiscount(t *testing.T) {
    calculator := NewPriceCalculator()
    
    tests := []struct {
        name     string
        price    float64
        discount float64
        expected float64
    }{
        {"10% discount", 100.0, 0.1, 90.0},
        {"0% discount", 100.0, 0.0, 100.0},
        {"100% discount", 100.0, 1.0, 0.0},
    }
    
    for _, tt := range tests {
        t.Run(tt.name, func(t *testing.T) {
            result := calculator.ApplyDiscount(tt.price, tt.discount)
            assert.Equal(t, tt.expected, result)
        })
    }
}

func TestInvalidDiscount(t *testing.T) {
    calculator := NewPriceCalculator()
    
    // 测试负折扣
    assert.Panics(t, func() {
        calculator.ApplyDiscount(100.0, -0.1)
    })
    
    // 测试超过100%折扣
    assert.Panics(t, func() {
        calculator.ApplyDiscount(100.0, 1.1)
    })
}

// Mock测试
type MockAPIClient struct {
    mock.Mock
}

func (m *MockAPIClient) GetData(endpoint string) (map[string]interface{}, error) {
    args := m.Called(endpoint)
    return args.Get(0).(map[string]interface{}), args.Error(1)
}

func TestAPIClient(t *testing.T) {
    mockClient := new(MockAPIClient)
    
    expectedResponse := map[string]interface{}{
        "status": "success",
    }
    
    mockClient.On("GetData", "test-endpoint").Return(expectedResponse, nil)
    
    result, err := mockClient.GetData("test-endpoint")
    
    assert.NoError(t, err)
    assert.Equal(t, "success", result["status"])
    mockClient.AssertExpectations(t)
}

// 基准测试
func BenchmarkValidateEmail(b *testing.B) {
    validator := NewDataValidator()
    email := "test@example.com"
    
    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        validator.ValidateEmail(email)
    }
}

func BenchmarkCalculateTotal(b *testing.B) {
    calculator := NewPriceCalculator()
    items := []Item{
        {Price: 10.0, Quantity: 2},
        {Price: 15.0, Quantity: 1},
        {Price: 5.0, Quantity: 3},
    }
    
    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        calculator.CalculateTotal(items)
    }
}
```

## 测试工具和实用程序

### 1. 测试数据生成

#### 工厂模式

```python
import factory
from faker import Faker
from typing import Dict, Any, List
import random

fake = Faker()

class UserFactory(factory.Factory):
    """用户工厂"""
    class Meta:
        model = User
    
    name = factory.LazyFunction(lambda: fake.name())
    email = factory.LazyFunction(lambda: fake.email())
    age = factory.LazyFunction(lambda: random.randint(18, 80))
    created_at = factory.LazyFunction(lambda: fake.date_time())

class OrderFactory(factory.Factory):
    """订单工厂"""
    class Meta:
        model = Order
    
    user = factory.SubFactory(UserFactory)
    total_amount = factory.LazyFunction(lambda: round(random.uniform(10.0, 1000.0), 2))
    status = factory.LazyFunction(lambda: random.choice(['pending', 'completed', 'cancelled']))
    created_at = factory.LazyFunction(lambda: fake.date_time())

class TestDataGenerator:
    """测试数据生成器"""
    
    def __init__(self):
        self.factories = {
            'user': UserFactory,
            'order': OrderFactory,
        }
    
    def create_test_data(self, model: str, count: int = 1, **kwargs) -> List[Any]:
        """创建测试数据"""
        factory = self.factories.get(model)
        if not factory:
            raise ValueError(f"Unknown model: {model}")
        
        return factory.create_batch(count, **kwargs)
    
    def create_test_user(self, **kwargs) -> User:
        """创建测试用户"""
        return UserFactory(**kwargs)
    
    def create_test_order(self, **kwargs) -> Order:
        """创建测试订单"""
        return OrderFactory(**kwargs)
    
    def cleanup_test_data(self):
        """清理测试数据"""
        # 清理逻辑
        pass
```

### 2. 测试辅助工具

#### 测试工具类

```python
import json
import tempfile
import os
from contextlib import contextmanager
from typing import Any, Dict, List
import requests
from unittest.mock import Mock, patch

class TestUtils:
    """测试工具类"""
    
    @staticmethod
    def create_temp_file(content: str) -> str:
        """创建临时文件"""
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.json') as f:
            f.write(content)
            return f.name
    
    @staticmethod
    def read_json_file(file_path: str) -> Dict[str, Any]:
        """读取JSON文件"""
        with open(file_path, 'r') as f:
            return json.load(f)
    
    @staticmethod
    def write_json_file(file_path: str, data: Dict[str, Any]):
        """写入JSON文件"""
        with open(file_path, 'w') as f:
            json.dump(data, f, indent=2)
    
    @staticmethod
    @contextmanager
    def temp_file(content: str):
        """临时文件上下文管理器"""
        temp_path = TestUtils.create_temp_file(content)
        try:
            yield temp_path
        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)
    
    @staticmethod
    def mock_http_response(status_code: int = 200, json_data: Dict[str, Any] = None):
        """模拟HTTP响应"""
        mock_response = Mock()
        mock_response.status_code = status_code
        mock_response.json.return_value = json_data or {}
        return mock_response
    
    @staticmethod
    def assert_dict_contains(expected: Dict[str, Any], actual: Dict[str, Any]):
        """断言字典包含"""
        for key, value in expected.items():
            assert key in actual, f"Key '{key}' not found in actual dict"
            assert actual[key] == value, f"Value for key '{key}' does not match"
    
    @staticmethod
    def assert_list_contains(expected_items: List[Any], actual_list: List[Any]):
        """断言列表包含"""
        for item in expected_items:
            assert item in actual_list, f"Item {item} not found in actual list"

class DatabaseTestUtils:
    """数据库测试工具"""
    
    def __init__(self, db_session):
        self.db_session = db_session
    
    def create_test_user(self, **kwargs) -> User:
        """创建测试用户"""
        user = User(**kwargs)
        self.db_session.add(user)
        self.db_session.commit()
        return user
    
    def create_test_order(self, user: User, **kwargs) -> Order:
        """创建测试订单"""
        order = Order(user=user, **kwargs)
        self.db_session.add(order)
        self.db_session.commit()
        return order
    
    def cleanup_test_data(self):
        """清理测试数据"""
        self.db_session.rollback()
        self.db_session.close()

class APITestUtils:
    """API测试工具"""
    
    def __init__(self, base_url: str):
        self.base_url = base_url
        self.session = requests.Session()
    
    def make_request(self, method: str, endpoint: str, **kwargs) -> requests.Response:
        """发送API请求"""
        url = f"{self.base_url}{endpoint}"
        return self.session.request(method, url, **kwargs)
    
    def get(self, endpoint: str, **kwargs) -> requests.Response:
        """GET请求"""
        return self.make_request('GET', endpoint, **kwargs)
    
    def post(self, endpoint: str, **kwargs) -> requests.Response:
        """POST请求"""
        return self.make_request('POST', endpoint, **kwargs)
    
    def put(self, endpoint: str, **kwargs) -> requests.Response:
        """PUT请求"""
        return self.make_request('PUT', endpoint, **kwargs)
    
    def delete(self, endpoint: str, **kwargs) -> requests.Response:
        """DELETE请求"""
        return self.make_request('DELETE', endpoint, **kwargs)
```

## 测试配置和运行

### 1. 测试配置文件

#### pytest配置

```ini
# pytest.ini
[tool:pytest]
testpaths = tests
python_files = test_*.py *_test.py
python_classes = Test*
python_functions = test_*
addopts = 
    --strict-markers
    --strict-config
    --verbose
    --tb=short
    --cov=src
    --cov-report=html
    --cov-report=term-missing
    --cov-fail-under=80
markers =
    slow: marks tests as slow
    integration: marks tests as integration tests
    unit: marks tests as unit tests
    smoke: marks tests as smoke tests
filterwarnings =
    ignore::DeprecationWarning
    ignore::PendingDeprecationWarning
```

#### Jest配置

```json
{
  "name": "formal-framework-tests",
  "version": "1.0.0",
  "scripts": {
    "test": "jest",
    "test:watch": "jest --watch",
    "test:coverage": "jest --coverage",
    "test:ci": "jest --ci --coverage --watchAll=false"
  },
  "jest": {
    "testEnvironment": "node",
    "setupFilesAfterEnv": ["<rootDir>/tests/setup.js"],
    "testMatch": [
      "**/__tests__/**/*.test.js",
      "**/?(*.)+(spec|test).js"
    ],
    "collectCoverageFrom": [
      "src/**/*.js",
      "!src/**/*.test.js",
      "!src/**/*.spec.js"
    ],
    "coverageThreshold": {
      "global": {
        "branches": 80,
        "functions": 80,
        "lines": 80,
        "statements": 80
      }
    },
    "testTimeout": 10000,
    "verbose": true
  }
}
```

### 2. 持续集成配置

#### GitHub Actions

```yaml
name: Unit Tests

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python-version: [3.8, 3.9, 3.10, 3.11]
        node-version: [16, 18, 20]
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Set up Python ${{ matrix.python-version }}
      uses: actions/setup-python@v4
      with:
        python-version: ${{ matrix.python-version }}
    
    - name: Set up Node.js ${{ matrix.node-version }}
      uses: actions/setup-node@v3
      with:
        node-version: ${{ matrix.node-version }}
    
    - name: Install Python dependencies
      run: |
        python -m pip install --upgrade pip
        pip install -r requirements.txt
        pip install -r requirements-test.txt
    
    - name: Install Node.js dependencies
      run: |
        npm ci
    
    - name: Run Python tests
      run: |
        pytest tests/ --cov=src --cov-report=xml
    
    - name: Run Node.js tests
      run: |
        npm test -- --coverage
    
    - name: Upload coverage to Codecov
      uses: codecov/codecov-action@v3
      with:
        file: ./coverage.xml
        flags: unittests
        name: codecov-umbrella
```

## 最佳实践

1. **测试命名**: 使用描述性的测试名称
2. **测试结构**: 遵循AAA模式（Arrange, Act, Assert）
3. **测试隔离**: 确保测试之间相互独立
4. **测试数据**: 使用工厂模式生成测试数据
5. **Mock使用**: 适当使用Mock隔离外部依赖
6. **覆盖率**: 保持合理的测试覆盖率
7. **持续集成**: 在CI/CD中运行测试

## 相关文档

- [集成测试框架](integration-testing.md)
- [端到端测试框架](e2e-testing.md)
- [性能测试框架](performance-testing.md)
- [验证脚本](../../verification-scripts/README.md)
