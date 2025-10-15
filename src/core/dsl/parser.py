#!/usr/bin/env python3
"""
形式化框架 DSL 解析器
支持交互、数据、功能等元模型的 DSL 解析
"""

import json
import yaml
from typing import Dict, List, Any, Optional, Union
from dataclasses import dataclass, field
from enum import Enum
import logging

logger = logging.getLogger(__name__)

class DSLType(Enum):
    """DSL 类型枚举"""
    INTERACTION = "interaction"
    DATA = "data"
    FUNCTIONAL = "functional"
    RUNTIME = "runtime"
    DEPLOYMENT = "deployment"
    MONITORING = "monitoring"
    CONTROL_SCHEDULING = "control_scheduling"
    TESTING = "testing"
    CICD = "cicd"
    DISTRIBUTED_PATTERN = "distributed_pattern"

@dataclass
class DSLNode:
    """DSL 节点基类"""
    id: str
    type: str
    name: str
    properties: Dict[str, Any] = field(default_factory=dict)
    children: List['DSLNode'] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)

@dataclass
class EndpointNode(DSLNode):
    """端点节点"""
    path: str
    method: str
    version: str
    security: Dict[str, Any] = field(default_factory=dict)
    performance: Dict[str, Any] = field(default_factory=dict)

@dataclass
class EntityNode(DSLNode):
    """实体节点"""
    fields: List[Dict[str, Any]] = field(default_factory=list)
    constraints: List[Dict[str, Any]] = field(default_factory=list)
    indexes: List[Dict[str, Any]] = field(default_factory=list)

@dataclass
class BusinessLogicNode(DSLNode):
    """业务逻辑节点"""
    input_schema: Dict[str, Any] = field(default_factory=dict)
    output_schema: Dict[str, Any] = field(default_factory=dict)
    rules: List[Dict[str, Any]] = field(default_factory=list)

@dataclass
class WorkloadNode(DSLNode):
    """工作负载节点"""
    replicas: int = 1
    resources: Dict[str, Any] = field(default_factory=dict)
    strategy: str = "rolling"
    health: Dict[str, Any] = field(default_factory=dict)
    scaling: Dict[str, Any] = field(default_factory=dict)

@dataclass
class ServiceNode(DSLNode):
    """服务节点"""
    service_type: str = "ClusterIP"
    ports: List[Dict[str, Any]] = field(default_factory=list)
    selector: Dict[str, str] = field(default_factory=dict)
    endpoints: List[str] = field(default_factory=list)

@dataclass
class MetricNode(DSLNode):
    """指标节点"""
    metric_type: str = "gauge"
    unit: str = ""
    labels: List[str] = field(default_factory=list)
    collection: Dict[str, Any] = field(default_factory=dict)
    storage: Dict[str, Any] = field(default_factory=dict)

@dataclass
class TestCaseNode(DSLNode):
    """测试用例节点"""
    priority: str = "medium"
    preconditions: List[str] = field(default_factory=list)
    steps: List[Dict[str, Any]] = field(default_factory=list)
    expected_result: str = ""
    tags: List[str] = field(default_factory=list)

@dataclass
class SchedulerNode(DSLNode):
    """调度器节点"""
    strategy: str = "fifo"
    priority_algorithm: str = "static"
    resource_pool: Dict[str, Any] = field(default_factory=dict)
    load_balancing: Dict[str, Any] = field(default_factory=dict)

class DSLParser:
    """DSL 解析器"""
    
    def __init__(self):
        self.supported_formats = ['yaml', 'json']
        self.node_factories = {
            'endpoint': EndpointNode,
            'entity': EntityNode,
            'business_logic': BusinessLogicNode,
            'workload': WorkloadNode,
            'service': ServiceNode,
            'metric': MetricNode,
            'test_case': TestCaseNode,
            'scheduler': SchedulerNode
        }
    
    def parse(self, content: str, format_type: str = 'yaml') -> DSLNode:
        """
        解析 DSL 内容
        
        Args:
            content: DSL 内容
            format_type: 格式类型 (yaml/json)
            
        Returns:
            解析后的 DSL 节点
        """
        try:
            if format_type == 'yaml':
                data = yaml.safe_load(content)
            elif format_type == 'json':
                data = json.loads(content)
            else:
                raise ValueError(f"不支持的格式类型: {format_type}")
            
            return self._parse_node(data)
        except Exception as e:
            logger.error(f"DSL 解析失败: {e}")
            raise
    
    def _parse_node(self, data: Dict[str, Any]) -> DSLNode:
        """解析单个节点"""
        node_type = data.get('type', 'generic')
        node_id = data.get('id', '')
        node_name = data.get('name', '')
        
        # 创建节点
        if node_type in self.node_factories:
            node = self.node_factories[node_type](
                id=node_id,
                type=node_type,
                name=node_name
            )
        else:
            node = DSLNode(
                id=node_id,
                type=node_type,
                name=node_name
            )
        
        # 解析属性
        for key, value in data.items():
            if key not in ['id', 'type', 'name', 'children']:
                if hasattr(node, key):
                    setattr(node, key, value)
                else:
                    node.properties[key] = value
        
        # 解析子节点
        if 'children' in data:
            for child_data in data['children']:
                child_node = self._parse_node(child_data)
                node.children.append(child_node)
        
        return node
    
    def validate(self, node: DSLNode) -> List[str]:
        """
        验证 DSL 节点
        
        Args:
            node: DSL 节点
            
        Returns:
            验证错误列表
        """
        errors = []
        
        # 基础验证
        if not node.id:
            errors.append(f"节点 {node.name} 缺少 ID")
        
        if not node.name:
            errors.append(f"节点 {node.id} 缺少名称")
        
        # 类型特定验证
        if isinstance(node, EndpointNode):
            errors.extend(self._validate_endpoint(node))
        elif isinstance(node, EntityNode):
            errors.extend(self._validate_entity(node))
        elif isinstance(node, BusinessLogicNode):
            errors.extend(self._validate_business_logic(node))
        elif isinstance(node, WorkloadNode):
            errors.extend(self._validate_workload(node))
        elif isinstance(node, ServiceNode):
            errors.extend(self._validate_service(node))
        elif isinstance(node, MetricNode):
            errors.extend(self._validate_metric(node))
        elif isinstance(node, TestCaseNode):
            errors.extend(self._validate_test_case(node))
        elif isinstance(node, SchedulerNode):
            errors.extend(self._validate_scheduler(node))
        
        # 递归验证子节点
        for child in node.children:
            errors.extend(self.validate(child))
        
        return errors
    
    def _validate_endpoint(self, endpoint: EndpointNode) -> List[str]:
        """验证端点节点"""
        errors = []
        
        if not endpoint.path:
            errors.append(f"端点 {endpoint.name} 缺少路径")
        
        if not endpoint.method:
            errors.append(f"端点 {endpoint.name} 缺少 HTTP 方法")
        
        if not endpoint.version:
            errors.append(f"端点 {endpoint.name} 缺少版本")
        
        return errors
    
    def _validate_entity(self, entity: EntityNode) -> List[str]:
        """验证实体节点"""
        errors = []
        
        if not entity.fields:
            errors.append(f"实体 {entity.name} 缺少字段定义")
        
        # 验证字段
        field_names = set()
        for field in entity.fields:
            if 'name' not in field:
                errors.append(f"实体 {entity.name} 的字段缺少名称")
            elif field['name'] in field_names:
                errors.append(f"实体 {entity.name} 的字段名称重复: {field['name']}")
            else:
                field_names.add(field['name'])
        
        return errors
    
    def _validate_business_logic(self, logic: BusinessLogicNode) -> List[str]:
        """验证业务逻辑节点"""
        errors = []
        
        if not logic.input_schema:
            errors.append(f"业务逻辑 {logic.name} 缺少输入模式")
        
        if not logic.output_schema:
            errors.append(f"业务逻辑 {logic.name} 缺少输出模式")
        
        return errors
    
    def _validate_workload(self, workload: WorkloadNode) -> List[str]:
        """验证工作负载节点"""
        errors = []
        
        if workload.replicas < 0:
            errors.append(f"工作负载 {workload.name} 副本数不能为负数")
        
        if not workload.resources:
            errors.append(f"工作负载 {workload.name} 缺少资源配置")
        
        return errors
    
    def _validate_service(self, service: ServiceNode) -> List[str]:
        """验证服务节点"""
        errors = []
        
        if not service.ports:
            errors.append(f"服务 {service.name} 缺少端口配置")
        
        if not service.selector:
            errors.append(f"服务 {service.name} 缺少选择器配置")
        
        return errors
    
    def _validate_metric(self, metric: MetricNode) -> List[str]:
        """验证指标节点"""
        errors = []
        
        valid_types = ['counter', 'gauge', 'histogram', 'summary']
        if metric.metric_type not in valid_types:
            errors.append(f"指标 {metric.name} 类型无效: {metric.metric_type}")
        
        if not metric.collection:
            errors.append(f"指标 {metric.name} 缺少收集配置")
        
        return errors
    
    def _validate_test_case(self, test_case: TestCaseNode) -> List[str]:
        """验证测试用例节点"""
        errors = []
        
        if not test_case.steps:
            errors.append(f"测试用例 {test_case.name} 缺少测试步骤")
        
        if not test_case.expected_result:
            errors.append(f"测试用例 {test_case.name} 缺少预期结果")
        
        valid_priorities = ['low', 'medium', 'high', 'critical']
        if test_case.priority not in valid_priorities:
            errors.append(f"测试用例 {test_case.name} 优先级无效: {test_case.priority}")
        
        return errors
    
    def _validate_scheduler(self, scheduler: SchedulerNode) -> List[str]:
        """验证调度器节点"""
        errors = []
        
        valid_strategies = ['fifo', 'priority', 'round_robin', 'weighted', 'custom']
        if scheduler.strategy not in valid_strategies:
            errors.append(f"调度器 {scheduler.name} 策略无效: {scheduler.strategy}")
        
        if not scheduler.resource_pool:
            errors.append(f"调度器 {scheduler.name} 缺少资源池配置")
        
        return errors

class DSLGenerator:
    """DSL 生成器"""
    
    def __init__(self):
        self.templates = {
            'interaction': self._generate_interaction_dsl,
            'data': self._generate_data_dsl,
            'functional': self._generate_functional_dsl
        }
    
    def generate(self, model_type: str, config: Dict[str, Any]) -> str:
        """
        生成 DSL 内容
        
        Args:
            model_type: 模型类型
            config: 配置参数
            
        Returns:
            生成的 DSL 内容
        """
        if model_type not in self.templates:
            raise ValueError(f"不支持的模型类型: {model_type}")
        
        return self.templates[model_type](config)
    
    def _generate_interaction_dsl(self, config: Dict[str, Any]) -> str:
        """生成交互模型 DSL"""
        return f"""
type: interaction_model
name: {config.get('name', 'InteractionModel')}
version: {config.get('version', '1.0.0')}

endpoints:
  - id: {config.get('endpoint_id', 'api_endpoint')}
    name: {config.get('endpoint_name', 'API Endpoint')}
    path: {config.get('path', '/api/v1')}
    method: {config.get('method', 'GET')}
    version: {config.get('version', '1.0.0')}
    security:
      authentication: {config.get('auth', 'bearer')}
      authorization: {config.get('authorization', 'role-based')}
    performance:
      timeout: {config.get('timeout', 30)}
      rate_limit: {config.get('rate_limit', 1000)}
"""
    
    def _generate_data_dsl(self, config: Dict[str, Any]) -> str:
        """生成数据模型 DSL"""
        return f"""
type: data_model
name: {config.get('name', 'DataModel')}
version: {config.get('version', '1.0.0')}

entities:
  - id: {config.get('entity_id', 'entity')}
    name: {config.get('entity_name', 'Entity')}
    fields:
      - name: id
        type: string
        nullable: false
        primary_key: true
      - name: name
        type: string
        nullable: false
      - name: created_at
        type: timestamp
        nullable: false
        default: now()
    constraints:
      - type: unique
        fields: [name]
    indexes:
      - type: primary
        fields: [id]
      - type: index
        fields: [name]
"""
    
    def _generate_functional_dsl(self, config: Dict[str, Any]) -> str:
        """生成功能模型 DSL"""
        return f"""
type: functional_model
name: {config.get('name', 'FunctionalModel')}
version: {config.get('version', '1.0.0')}

business_logic:
  - id: {config.get('logic_id', 'business_logic')}
    name: {config.get('logic_name', 'Business Logic')}
    type: {config.get('logic_type', 'validation')}
    input_schema:
      type: object
      properties:
        input_data:
          type: string
    output_schema:
      type: object
      properties:
        result:
          type: boolean
    rules:
      - condition: "input_data is not null"
        action: "return true"
"""

class DSLValidator:
    """DSL 验证器"""
    
    def __init__(self):
        self.validators = {
            'interaction': self._validate_interaction_model,
            'data': self._validate_data_model,
            'functional': self._validate_functional_model
        }
    
    def validate(self, node: DSLNode) -> Dict[str, Any]:
        """
        验证 DSL 模型
        
        Args:
            node: DSL 节点
            
        Returns:
            验证结果
        """
        result = {
            'valid': True,
            'errors': [],
            'warnings': [],
            'suggestions': []
        }
        
        # 基础验证
        parser = DSLParser()
        errors = parser.validate(node)
        result['errors'].extend(errors)
        
        # 类型特定验证
        if node.type in self.validators:
            type_result = self.validators[node.type](node)
            result['errors'].extend(type_result.get('errors', []))
            result['warnings'].extend(type_result.get('warnings', []))
            result['suggestions'].extend(type_result.get('suggestions', []))
        
        result['valid'] = len(result['errors']) == 0
        
        return result
    
    def _validate_interaction_model(self, node: DSLNode) -> Dict[str, Any]:
        """验证交互模型"""
        result = {'errors': [], 'warnings': [], 'suggestions': []}
        
        # 检查端点定义
        endpoints = [child for child in node.children if child.type == 'endpoint']
        if not endpoints:
            result['warnings'].append("交互模型缺少端点定义")
        
        # 检查安全配置
        for endpoint in endpoints:
            if 'security' not in endpoint.properties:
                result['warnings'].append(f"端点 {endpoint.name} 缺少安全配置")
        
        return result
    
    def _validate_data_model(self, node: DSLNode) -> Dict[str, Any]:
        """验证数据模型"""
        result = {'errors': [], 'warnings': [], 'suggestions': []}
        
        # 检查实体定义
        entities = [child for child in node.children if child.type == 'entity']
        if not entities:
            result['warnings'].append("数据模型缺少实体定义")
        
        # 检查字段定义
        for entity in entities:
            if not hasattr(entity, 'fields') or not entity.fields:
                result['warnings'].append(f"实体 {entity.name} 缺少字段定义")
        
        return result
    
    def _validate_functional_model(self, node: DSLNode) -> Dict[str, Any]:
        """验证功能模型"""
        result = {'errors': [], 'warnings': [], 'suggestions': []}
        
        # 检查业务逻辑定义
        logic_nodes = [child for child in node.children if child.type == 'business_logic']
        if not logic_nodes:
            result['warnings'].append("功能模型缺少业务逻辑定义")
        
        return result

# 使用示例
if __name__ == "__main__":
    # 创建解析器
    parser = DSLParser()
    generator = DSLGenerator()
    validator = DSLValidator()
    
    # 生成示例 DSL
    config = {
        'name': 'UserAPI',
        'endpoint_name': 'User Management API',
        'path': '/api/v1/users',
        'method': 'GET'
    }
    
    dsl_content = generator.generate('interaction', config)
    print("生成的 DSL:")
    print(dsl_content)
    
    # 解析 DSL
    node = parser.parse(dsl_content, 'yaml')
    print(f"\n解析结果: {node.name} ({node.type})")
    
    # 验证 DSL
    validation_result = validator.validate(node)
    print(f"\n验证结果: {'通过' if validation_result['valid'] else '失败'}")
    if validation_result['errors']:
        print("错误:", validation_result['errors'])
    if validation_result['warnings']:
        print("警告:", validation_result['warnings'])
