#!/usr/bin/env python3
"""
交互模型测试
使用pytest验证交互模型的关键功能和约束
"""

import pytest
import json
import time
from typing import Dict, List, Any
from dataclasses import dataclass
from unittest.mock import Mock, patch, MagicMock

# 模拟交互模型类
@dataclass
class Endpoint:
    """端点实体"""
    id: str
    name: str
    path: str
    method: str
    version: str
    auth_required: bool
    rate_limit: int
    timeout: int
    status: str = "active"

@dataclass
class Resource:
    """资源实体"""
    id: str
    name: str
    type: str
    version: str
    schema: Dict[str, Any]
    status: str = "active"

@dataclass
class Operation:
    """操作实体"""
    id: str
    name: str
    type: str
    resource_id: str
    parameters: Dict[str, Any]
    status: str = "active"

class InteractionModel:
    """交互模型主类"""
    
    def __init__(self):
        self.endpoints: List[Endpoint] = []
        self.resources: List[Resource] = []
        self.operations: List[Operation] = []
        self.endpoint_paths: Dict[str, str] = {}
        self.resource_operations: Dict[str, List[str]] = {}
    
    def add_endpoint(self, endpoint: Endpoint) -> bool:
        """添加端点"""
        # 检查路径和方法组合的唯一性
        path_method = f"{endpoint.path}:{endpoint.method}"
        if path_method in self.endpoint_paths:
            return False
        
        self.endpoints.append(endpoint)
        self.endpoint_paths[path_method] = endpoint.id
        return True
    
    def add_resource(self, resource: Resource) -> bool:
        """添加资源"""
        # 检查名称唯一性
        if any(r.name == resource.name for r in self.resources):
            return False
        
        self.resources.append(resource)
        self.resource_operations[resource.id] = []
        return True
    
    def add_operation(self, operation: Operation) -> bool:
        """添加操作"""
        # 检查资源存在性
        if not any(r.id == operation.resource_id for r in self.resources):
            return False
        
        # 检查名称唯一性
        if any(o.name == operation.name for o in self.operations):
            return False
        
        self.operations.append(operation)
        self.resource_operations[operation.resource_id].append(operation.id)
        return True
    
    def get_endpoint_by_path(self, path: str, method: str) -> Endpoint:
        """根据路径和方法获取端点"""
        path_method = f"{path}:{method}"
        endpoint_id = self.endpoint_paths.get(path_method)
        if endpoint_id:
            return next((e for e in self.endpoints if e.id == endpoint_id), None)
        return None
    
    def get_resource_operations(self, resource_id: str) -> List[Operation]:
        """获取资源的操作列表"""
        operation_ids = self.resource_operations.get(resource_id, [])
        return [o for o in self.operations if o.id in operation_ids]
    
    def validate_endpoint(self, endpoint: Endpoint) -> List[str]:
        """验证端点"""
        errors = []
        
        # 路径验证
        if not endpoint.path.startswith('/'):
            errors.append("路径必须以/开头")
        
        if len(endpoint.path) > 255:
            errors.append("路径长度不能超过255字符")
        
        # 方法验证
        valid_methods = ['GET', 'POST', 'PUT', 'DELETE', 'PATCH', 'HEAD', 'OPTIONS']
        if endpoint.method not in valid_methods:
            errors.append(f"无效的HTTP方法: {endpoint.method}")
        
        # 版本验证
        if not self._is_valid_version(endpoint.version):
            errors.append(f"无效的版本号: {endpoint.version}")
        
        # 配置验证
        if endpoint.auth_required and endpoint.rate_limit <= 0:
            errors.append("需要认证的端点必须设置限流")
        
        if endpoint.timeout <= 0:
            errors.append("超时时间必须大于0")
        
        if endpoint.timeout > 30000:
            errors.append("超时时间不能超过30秒")
        
        return errors
    
    def _is_valid_version(self, version: str) -> bool:
        """验证版本号格式"""
        try:
            parts = version.split('.')
            if len(parts) != 3:
                return False
            
            major, minor, patch = parts
            if not all(part.isdigit() for part in [major, minor, patch]):
                return False
            
            return True
        except:
            return False

# 测试夹具
@pytest.fixture
def interaction_model():
    """创建交互模型实例"""
    return InteractionModel()

@pytest.fixture
def sample_endpoint():
    """创建示例端点"""
    return Endpoint(
        id="ep_001",
        name="User API",
        path="/api/v1/users",
        method="GET",
        version="1.0.0",
        auth_required=True,
        rate_limit=100,
        timeout=5000
    )

@pytest.fixture
def sample_resource():
    """创建示例资源"""
    return Resource(
        id="res_001",
        name="User",
        type="entity",
        version="1.0.0",
        schema={
            "type": "object",
            "properties": {
                "id": {"type": "string"},
                "name": {"type": "string"},
                "email": {"type": "string"}
            }
        }
    )

@pytest.fixture
def sample_operation():
    """创建示例操作"""
    return Operation(
        id="op_001",
        name="Get User",
        type="read",
        resource_id="res_001",
        parameters={
            "id": {"type": "string", "required": True}
        }
    )

# 测试类
class TestInteractionModel:
    """交互模型测试类"""
    
    def test_add_endpoint_success(self, interaction_model, sample_endpoint):
        """测试成功添加端点"""
        result = interaction_model.add_endpoint(sample_endpoint)
        assert result is True
        assert len(interaction_model.endpoints) == 1
        assert interaction_model.endpoints[0].id == "ep_001"
    
    def test_add_endpoint_duplicate_path_method(self, interaction_model, sample_endpoint):
        """测试添加重复路径和方法的端点"""
        # 添加第一个端点
        interaction_model.add_endpoint(sample_endpoint)
        
        # 创建相同路径和方法的端点
        duplicate_endpoint = Endpoint(
            id="ep_002",
            name="Duplicate API",
            path="/api/v1/users",
            method="GET",
            version="1.0.0",
            auth_required=False,
            rate_limit=50,
            timeout=3000
        )
        
        result = interaction_model.add_endpoint(duplicate_endpoint)
        assert result is False
        assert len(interaction_model.endpoints) == 1
    
    def test_add_resource_success(self, interaction_model, sample_resource):
        """测试成功添加资源"""
        result = interaction_model.add_resource(sample_resource)
        assert result is True
        assert len(interaction_model.resources) == 1
        assert interaction_model.resources[0].id == "res_001"
    
    def test_add_resource_duplicate_name(self, interaction_model, sample_resource):
        """测试添加重复名称的资源"""
        # 添加第一个资源
        interaction_model.add_resource(sample_resource)
        
        # 创建相同名称的资源
        duplicate_resource = Resource(
            id="res_002",
            name="User",  # 相同名称
            type="entity",
            version="1.0.0",
            schema={}
        )
        
        result = interaction_model.add_resource(duplicate_resource)
        assert result is False
        assert len(interaction_model.resources) == 1
    
    def test_add_operation_success(self, interaction_model, sample_resource, sample_operation):
        """测试成功添加操作"""
        # 先添加资源
        interaction_model.add_resource(sample_resource)
        
        # 添加操作
        result = interaction_model.add_operation(sample_operation)
        assert result is True
        assert len(interaction_model.operations) == 1
        assert interaction_model.operations[0].id == "op_001"
    
    def test_add_operation_resource_not_exists(self, interaction_model, sample_operation):
        """测试添加操作时资源不存在"""
        result = interaction_model.add_operation(sample_operation)
        assert result is False
        assert len(interaction_model.operations) == 0
    
    def test_get_endpoint_by_path(self, interaction_model, sample_endpoint):
        """测试根据路径和方法获取端点"""
        interaction_model.add_endpoint(sample_endpoint)
        
        endpoint = interaction_model.get_endpoint_by_path("/api/v1/users", "GET")
        assert endpoint is not None
        assert endpoint.id == "ep_001"
        assert endpoint.name == "User API"
    
    def test_get_endpoint_by_path_not_found(self, interaction_model, sample_endpoint):
        """测试获取不存在的端点"""
        interaction_model.add_endpoint(sample_endpoint)
        
        endpoint = interaction_model.get_endpoint_by_path("/api/v1/users", "POST")
        assert endpoint is None
    
    def test_get_resource_operations(self, interaction_model, sample_resource, sample_operation):
        """测试获取资源的操作列表"""
        interaction_model.add_resource(sample_resource)
        interaction_model.add_operation(sample_operation)
        
        operations = interaction_model.get_resource_operations("res_001")
        assert len(operations) == 1
        assert operations[0].id == "op_001"

class TestEndpointValidation:
    """端点验证测试类"""
    
    def test_validate_endpoint_valid(self, interaction_model, sample_endpoint):
        """测试验证有效端点"""
        errors = interaction_model.validate_endpoint(sample_endpoint)
        assert len(errors) == 0
    
    def test_validate_endpoint_invalid_path(self, interaction_model):
        """测试验证无效路径的端点"""
        invalid_endpoint = Endpoint(
            id="ep_001",
            name="Invalid API",
            path="api/v1/users",  # 不以/开头
            method="GET",
            version="1.0.0",
            auth_required=False,
            rate_limit=100,
            timeout=5000
        )
        
        errors = interaction_model.validate_endpoint(invalid_endpoint)
        assert len(errors) > 0
        assert "路径必须以/开头" in errors
    
    def test_validate_endpoint_invalid_method(self, interaction_model):
        """测试验证无效方法的端点"""
        invalid_endpoint = Endpoint(
            id="ep_001",
            name="Invalid API",
            path="/api/v1/users",
            method="INVALID",  # 无效方法
            version="1.0.0",
            auth_required=False,
            rate_limit=100,
            timeout=5000
        )
        
        errors = interaction_model.validate_endpoint(invalid_endpoint)
        assert len(errors) > 0
        assert "无效的HTTP方法" in errors
    
    def test_validate_endpoint_invalid_version(self, interaction_model):
        """测试验证无效版本的端点"""
        invalid_endpoint = Endpoint(
            id="ep_001",
            name="Invalid API",
            path="/api/v1/users",
            method="GET",
            version="invalid",  # 无效版本
            auth_required=False,
            rate_limit=100,
            timeout=5000
        )
        
        errors = interaction_model.validate_endpoint(invalid_endpoint)
        assert len(errors) > 0
        assert "无效的版本号" in errors
    
    def test_validate_endpoint_auth_without_rate_limit(self, interaction_model):
        """测试验证需要认证但无限流的端点"""
        invalid_endpoint = Endpoint(
            id="ep_001",
            name="Invalid API",
            path="/api/v1/users",
            method="GET",
            version="1.0.0",
            auth_required=True,  # 需要认证
            rate_limit=0,        # 无限流
            timeout=5000
        )
        
        errors = interaction_model.validate_endpoint(invalid_endpoint)
        assert len(errors) > 0
        assert "需要认证的端点必须设置限流" in errors
    
    def test_validate_endpoint_invalid_timeout(self, interaction_model):
        """测试验证无效超时的端点"""
        invalid_endpoint = Endpoint(
            id="ep_001",
            name="Invalid API",
            path="/api/v1/users",
            method="GET",
            version="1.0.0",
            auth_required=False,
            rate_limit=100,
            timeout=0  # 无效超时
        )
        
        errors = interaction_model.validate_endpoint(invalid_endpoint)
        assert len(errors) > 0
        assert "超时时间必须大于0" in errors

class TestModelConstraints:
    """模型约束测试类"""
    
    def test_endpoint_uniqueness_constraint(self, interaction_model):
        """测试端点唯一性约束"""
        endpoint1 = Endpoint(
            id="ep_001",
            name="User API 1",
            path="/api/v1/users",
            method="GET",
            version="1.0.0",
            auth_required=False,
            rate_limit=100,
            timeout=5000
        )
        
        endpoint2 = Endpoint(
            id="ep_002",
            name="User API 2",
            path="/api/v1/users",
            method="GET",  # 相同路径和方法
            version="1.0.0",
            auth_required=False,
            rate_limit=100,
            timeout=5000
        )
        
        # 第一个端点应该成功添加
        assert interaction_model.add_endpoint(endpoint1) is True
        
        # 第二个端点应该失败
        assert interaction_model.add_endpoint(endpoint2) is False
        
        # 验证只有一个端点
        assert len(interaction_model.endpoints) == 1
    
    def test_resource_integrity_constraint(self, interaction_model, sample_resource):
        """测试资源完整性约束"""
        # 添加资源
        interaction_model.add_resource(sample_resource)
        
        # 验证资源存在
        assert len(interaction_model.resources) == 1
        assert interaction_model.resources[0].id == "res_001"
        
        # 验证资源操作映射已创建
        assert "res_001" in interaction_model.resource_operations
        assert interaction_model.resource_operations["res_001"] == []
    
    def test_operation_resource_association_constraint(self, interaction_model, sample_resource, sample_operation):
        """测试操作资源关联约束"""
        # 先添加资源
        interaction_model.add_resource(sample_resource)
        
        # 添加操作
        interaction_model.add_operation(sample_operation)
        
        # 验证操作存在
        assert len(interaction_model.operations) == 1
        assert interaction_model.operations[0].id == "op_001"
        
        # 验证操作与资源关联
        operations = interaction_model.get_resource_operations("res_001")
        assert len(operations) == 1
        assert operations[0].id == "op_001"

class TestPerformance:
    """性能测试类"""
    
    def test_add_multiple_endpoints_performance(self, interaction_model):
        """测试添加多个端点的性能"""
        start_time = time.time()
        
        for i in range(1000):
            endpoint = Endpoint(
                id=f"ep_{i:03d}",
                name=f"API {i}",
                path=f"/api/v1/resource{i}",
                method="GET",
                version="1.0.0",
                auth_required=False,
                rate_limit=100,
                timeout=5000
            )
            interaction_model.add_endpoint(endpoint)
        
        end_time = time.time()
        execution_time = end_time - start_time
        
        # 验证性能要求
        assert execution_time < 1.0  # 应该在1秒内完成
        assert len(interaction_model.endpoints) == 1000
    
    def test_search_endpoint_performance(self, interaction_model):
        """测试搜索端点的性能"""
        # 添加1000个端点
        for i in range(1000):
            endpoint = Endpoint(
                id=f"ep_{i:03d}",
                name=f"API {i}",
                path=f"/api/v1/resource{i}",
                method="GET",
                version="1.0.0",
                auth_required=False,
                rate_limit=100,
                timeout=5000
            )
            interaction_model.add_endpoint(endpoint)
        
        # 测试搜索性能
        start_time = time.time()
        
        for i in range(100):
            endpoint = interaction_model.get_endpoint_by_path(f"/api/v1/resource{i}", "GET")
            assert endpoint is not None
        
        end_time = time.time()
        execution_time = end_time - start_time
        
        # 验证性能要求
        assert execution_time < 0.1  # 应该在0.1秒内完成

# 参数化测试
@pytest.mark.parametrize("path,method,expected_valid", [
    ("/api/v1/users", "GET", True),
    ("/api/v1/users", "POST", True),
    ("/api/v1/users", "PUT", True),
    ("/api/v1/users", "DELETE", True),
    ("/api/v1/users", "PATCH", True),
    ("/api/v1/users", "HEAD", True),
    ("/api/v1/users", "OPTIONS", True),
    ("/api/v1/users", "INVALID", False),
    ("api/v1/users", "GET", False),  # 不以/开头
    ("", "GET", False),  # 空路径
])
def test_endpoint_path_method_validation(interaction_model, path, method, expected_valid):
    """参数化测试端点路径和方法验证"""
    endpoint = Endpoint(
        id="ep_001",
        name="Test API",
        path=path,
        method=method,
        version="1.0.0",
        auth_required=False,
        rate_limit=100,
        timeout=5000
    )
    
    errors = interaction_model.validate_endpoint(endpoint)
    is_valid = len(errors) == 0
    
    assert is_valid == expected_valid

@pytest.mark.parametrize("version,expected_valid", [
    ("1.0.0", True),
    ("2.1.3", True),
    ("0.0.1", True),
    ("10.20.30", True),
    ("1.0", False),      # 缺少patch版本
    ("1.0.0.0", False),  # 版本段过多
    ("1.a.0", False),    # 非数字版本
    ("invalid", False),   # 完全无效
    ("", False),          # 空版本
])
def test_version_validation(interaction_model, version, expected_valid):
    """参数化测试版本号验证"""
    endpoint = Endpoint(
        id="ep_001",
        name="Test API",
        path="/api/v1/test",
        method="GET",
        version=version,
        auth_required=False,
        rate_limit=100,
        timeout=5000
    )
    
    errors = interaction_model.validate_endpoint(endpoint)
    is_valid = len(errors) == 0
    
    assert is_valid == expected_valid

# 标记测试
@pytest.mark.slow
def test_large_scale_performance(interaction_model):
    """标记为慢速测试的大规模性能测试"""
    start_time = time.time()
    
    # 添加10000个端点
    for i in range(10000):
        endpoint = Endpoint(
            id=f"ep_{i:04d}",
            name=f"API {i}",
            path=f"/api/v1/resource{i}",
            method="GET",
            version="1.0.0",
            auth_required=False,
            rate_limit=100,
            timeout=5000
        )
        interaction_model.add_endpoint(endpoint)
    
    end_time = time.time()
    execution_time = end_time - start_time
    
    # 验证性能要求
    assert execution_time < 5.0  # 应该在5秒内完成
    assert len(interaction_model.endpoints) == 10000

@pytest.mark.integration
def test_full_model_integration(interaction_model):
    """标记为集成测试的完整模型测试"""
    # 创建完整的模型结构
    resources = []
    operations = []
    endpoints = []
    
    # 添加资源
    for i in range(10):
        resource = Resource(
            id=f"res_{i:02d}",
            name=f"Resource{i}",
            type="entity",
            version="1.0.0",
            schema={"type": "object"}
        )
        interaction_model.add_resource(resource)
        resources.append(resource)
    
    # 添加操作
    for i, resource in enumerate(resources):
        for j in range(5):
            operation = Operation(
                id=f"op_{i:02d}_{j:02d}",
                name=f"Operation{i}_{j}",
                type="read" if j % 2 == 0 else "write",
                resource_id=resource.id,
                parameters={}
            )
            interaction_model.add_operation(operation)
            operations.append(operation)
    
    # 添加端点
    for i, operation in enumerate(operations):
        endpoint = Endpoint(
            id=f"ep_{i:03d}",
            name=f"API_{i}",
            path=f"/api/v1/{operation.name.lower()}",
            method="GET" if i % 2 == 0 else "POST",
            version="1.0.0",
            auth_required=i % 3 == 0,
            rate_limit=100 + (i * 10),
            timeout=1000 + (i * 100)
        )
        interaction_model.add_endpoint(endpoint)
        endpoints.append(endpoint)
    
    # 验证模型完整性
    assert len(interaction_model.resources) == 10
    assert len(interaction_model.operations) == 50
    assert len(interaction_model.endpoints) == 50
    
    # 验证关联关系
    for resource in resources:
        resource_ops = interaction_model.get_resource_operations(resource.id)
        assert len(resource_ops) == 5
    
    # 验证端点唯一性
    path_methods = set()
    for endpoint in endpoints:
        path_method = f"{endpoint.path}:{endpoint.method}"
        assert path_method not in path_methods
        path_methods.add(path_method)

if __name__ == "__main__":
    # 运行测试
    pytest.main([__file__, "-v", "--tb=short"])
