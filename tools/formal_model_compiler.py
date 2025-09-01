#!/usr/bin/env python3
"""
Formal Model DSL Compiler
Formal Model框架的核心DSL编译器实现

支持词法分析、语法分析、语义分析和代码生成
"""

import re
import json
import yaml
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass
from enum import Enum
import logging

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class TokenType(Enum):
    """词法单元类型"""
    # 关键字
    MODEL = "MODEL"
    ENTITY = "ENTITY"
    OPERATION = "OPERATION"
    RELATION = "RELATION"
    CONSTRAINT = "CONSTRAINT"
    API = "API"
    CONTAINER = "CONTAINER"
    CONFIG = "CONFIG"
    ALERT = "ALERT"
    
    # 标识符和字面量
    IDENTIFIER = "IDENTIFIER"
    STRING = "STRING"
    NUMBER = "NUMBER"
    BOOLEAN = "BOOLEAN"
    
    # 运算符
    EQUALS = "EQUALS"
    COLON = "COLON"
    SEMICOLON = "SEMICOLON"
    COMMA = "COMMA"
    DOT = "DOT"
    ARROW = "ARROW"
    
    # 分隔符
    LPAREN = "LPAREN"
    RPAREN = "RPAREN"
    LBRACE = "LBRACE"
    RBRACE = "RBRACE"
    LBRACKET = "LBRACKET"
    RBRACKET = "RBRACKET"
    
    # 特殊
    EOF = "EOF"
    ERROR = "ERROR"

@dataclass
class Token:
    """词法单元"""
    type: TokenType
    value: str
    line: int
    column: int

class Lexer:
    """词法分析器"""
    
    def __init__(self, source: str):
        self.source = source
        self.position = 0
        self.line = 1
        self.column = 1
        self.tokens = []
        
        # 关键字映射
        self.keywords = {
            'model': TokenType.MODEL,
            'entity': TokenType.ENTITY,
            'operation': TokenType.OPERATION,
            'relation': TokenType.RELATION,
            'constraint': TokenType.CONSTRAINT,
            'api': TokenType.API,
            'container': TokenType.CONTAINER,
            'config': TokenType.CONFIG,
            'alert': TokenType.ALERT,
            'true': TokenType.BOOLEAN,
            'false': TokenType.BOOLEAN
        }
        
        # 正则表达式模式
        self.patterns = [
            (r'\s+', None),  # 空白字符
            (r'//.*', None),  # 单行注释
            (r'/\*.*?\*/', None),  # 多行注释
            (r'[a-zA-Z_][a-zA-Z0-9_]*', self._match_identifier),
            (r'"[^"]*"', self._match_string),
            (r'\d+', self._match_number),
            (r'=', lambda m: Token(TokenType.EQUALS, m.group(), self.line, self.column)),
            (r':', lambda m: Token(TokenType.COLON, m.group(), self.line, self.column)),
            (r';', lambda m: Token(TokenType.SEMICOLON, m.group(), self.line, self.column)),
            (r',', lambda m: Token(TokenType.COMMA, m.group(), self.line, self.column)),
            (r'\.', lambda m: Token(TokenType.DOT, m.group(), self.line, self.column)),
            (r'->', lambda m: Token(TokenType.ARROW, m.group(), self.line, self.column)),
            (r'\(', lambda m: Token(TokenType.LPAREN, m.group(), self.line, self.column)),
            (r'\)', lambda m: Token(TokenType.RPAREN, m.group(), self.line, self.column)),
            (r'\{', lambda m: Token(TokenType.LBRACE, m.group(), self.line, self.column)),
            (r'\}', lambda m: Token(TokenType.RBRACE, m.group(), self.line, self.column)),
            (r'\[', lambda m: Token(TokenType.LBRACKET, m.group(), self.line, self.column)),
            (r'\]', lambda m: Token(TokenType.RBRACKET, m.group(), self.line, self.column))
        ]
    
    def _match_identifier(self, match):
        """匹配标识符"""
        value = match.group()
        token_type = self.keywords.get(value.lower(), TokenType.IDENTIFIER)
        return Token(token_type, value, self.line, self.column)
    
    def _match_string(self, match):
        """匹配字符串"""
        value = match.group()[1:-1]  # 去掉引号
        return Token(TokenType.STRING, value, self.line, self.column)
    
    def _match_number(self, match):
        """匹配数字"""
        value = match.group()
        return Token(TokenType.NUMBER, value, self.line, self.column)
    
    def tokenize(self) -> List[Token]:
        """词法分析"""
        while self.position < len(self.source):
            match = None
            
            for pattern, handler in self.patterns:
                regex = re.compile(pattern)
                match = regex.match(self.source, self.position)
                
                if match:
                    if handler:
                        token = handler(match)
                        if token:
                            self.tokens.append(token)
                    
                    # 更新位置
                    self.position = match.end()
                    self.column += match.end() - match.start()
                    
                    # 处理换行
                    if '\n' in match.group():
                        lines = match.group().count('\n')
                        self.line += lines
                        self.column = 1
                    
                    break
            
            if not match:
                # 无法匹配的字符
                char = self.source[self.position]
                error_token = Token(TokenType.ERROR, char, self.line, self.column)
                self.tokens.append(error_token)
                self.position += 1
                self.column += 1
        
        # 添加EOF标记
        self.tokens.append(Token(TokenType.EOF, "", self.line, self.column))
        
        return self.tokens

class ASTNode:
    """抽象语法树节点基类"""
    pass

@dataclass
class ModelNode(ASTNode):
    """模型节点"""
    name: str
    type: str
    entities: List['EntityNode']
    operations: List['OperationNode']
    relations: List['RelationNode']
    constraints: List['ConstraintNode']

@dataclass
class EntityNode(ASTNode):
    """实体节点"""
    name: str
    attributes: List['AttributeNode']
    constraints: List['ConstraintNode']

@dataclass
class AttributeNode(ASTNode):
    """属性节点"""
    name: str
    type: str
    required: bool
    default: Optional[str]

@dataclass
class OperationNode(ASTNode):
    """操作节点"""
    name: str
    parameters: List['ParameterNode']
    return_type: str
    implementation: Optional[str]

@dataclass
class ParameterNode(ASTNode):
    """参数节点"""
    name: str
    type: str
    required: bool

@dataclass
class RelationNode(ASTNode):
    """关系节点"""
    name: str
    source: str
    target: str
    type: str  # one-to-one, one-to-many, many-to-many

@dataclass
class ConstraintNode(ASTNode):
    """约束节点"""
    name: str
    expression: str
    message: str

class Parser:
    """语法分析器"""
    
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.position = 0
        self.current_token = tokens[0] if tokens else None
    
    def advance(self):
        """前进到下一个词法单元"""
        self.position += 1
        if self.position < len(self.tokens):
            self.current_token = self.tokens[self.position]
        else:
            self.current_token = None
    
    def peek(self, offset: int = 1) -> Optional[Token]:
        """查看指定偏移位置的词法单元"""
        pos = self.position + offset
        if pos < len(self.tokens):
            return self.tokens[pos]
        return None
    
    def match(self, expected_type: TokenType) -> bool:
        """匹配指定类型的词法单元"""
        if self.current_token and self.current_token.type == expected_type:
            self.advance()
            return True
        return False
    
    def expect(self, expected_type: TokenType) -> Token:
        """期望指定类型的词法单元"""
        if self.current_token and self.current_token.type == expected_type:
            token = self.current_token
            self.advance()
            return token
        else:
            raise SyntaxError(f"Expected {expected_type}, got {self.current_token.type if self.current_token else 'EOF'}")
    
    def parse(self) -> ModelNode:
        """解析模型"""
        # 解析模型声明
        self.expect(TokenType.MODEL)
        model_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.COLON)
        model_type = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.LBRACE)
        
        # 解析模型内容
        entities = []
        operations = []
        relations = []
        constraints = []
        
        while self.current_token and self.current_token.type != TokenType.RBRACE:
            if self.current_token.type == TokenType.ENTITY:
                entities.append(self.parse_entity())
            elif self.current_token.type == TokenType.OPERATION:
                operations.append(self.parse_operation())
            elif self.current_token.type == TokenType.RELATION:
                relations.append(self.parse_relation())
            elif self.current_token.type == TokenType.CONSTRAINT:
                constraints.append(self.parse_constraint())
            else:
                raise SyntaxError(f"Unexpected token: {self.current_token.type}")
        
        self.expect(TokenType.RBRACE)
        
        return ModelNode(model_name, model_type, entities, operations, relations, constraints)
    
    def parse_entity(self) -> EntityNode:
        """解析实体"""
        self.expect(TokenType.ENTITY)
        entity_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.LBRACE)
        
        attributes = []
        constraints = []
        
        while self.current_token and self.current_token.type != TokenType.RBRACE:
            if self.current_token.type == TokenType.IDENTIFIER:
                attributes.append(self.parse_attribute())
            elif self.current_token.type == TokenType.CONSTRAINT:
                constraints.append(self.parse_constraint())
            else:
                raise SyntaxError(f"Unexpected token in entity: {self.current_token.type}")
        
        self.expect(TokenType.RBRACE)
        
        return EntityNode(entity_name, attributes, constraints)
    
    def parse_attribute(self) -> AttributeNode:
        """解析属性"""
        attr_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.COLON)
        attr_type = self.expect(TokenType.IDENTIFIER).value
        
        required = True
        default = None
        
        if self.current_token and self.current_token.type == TokenType.EQUALS:
            self.advance()
            if self.current_token.type == TokenType.STRING:
                default = self.current_token.value
                self.advance()
            elif self.current_token.type == TokenType.NUMBER:
                default = self.current_token.value
                self.advance()
            elif self.current_token.type == TokenType.BOOLEAN:
                default = self.current_token.value
                self.advance()
        
        self.expect(TokenType.SEMICOLON)
        
        return AttributeNode(attr_name, attr_type, required, default)
    
    def parse_operation(self) -> OperationNode:
        """解析操作"""
        self.expect(TokenType.OPERATION)
        op_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.LPAREN)
        
        parameters = []
        if self.current_token and self.current_token.type != TokenType.RPAREN:
            parameters.append(self.parse_parameter())
            while self.current_token and self.current_token.type == TokenType.COMMA:
                self.advance()
                parameters.append(self.parse_parameter())
        
        self.expect(TokenType.RPAREN)
        self.expect(TokenType.ARROW)
        return_type = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.SEMICOLON)
        
        return OperationNode(op_name, parameters, return_type, None)
    
    def parse_parameter(self) -> ParameterNode:
        """解析参数"""
        param_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.COLON)
        param_type = self.expect(TokenType.IDENTIFIER).value
        
        required = True
        if self.current_token and self.current_token.type == TokenType.IDENTIFIER:
            if self.current_token.value.lower() == 'optional':
                required = False
                self.advance()
        
        return ParameterNode(param_name, param_type, required)
    
    def parse_relation(self) -> RelationNode:
        """解析关系"""
        self.expect(TokenType.RELATION)
        relation_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.LPAREN)
        source = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.COMMA)
        target = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.RPAREN)
        self.expect(TokenType.COLON)
        relation_type = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.SEMICOLON)
        
        return RelationNode(relation_name, source, target, relation_type)
    
    def parse_constraint(self) -> ConstraintNode:
        """解析约束"""
        self.expect(TokenType.CONSTRAINT)
        constraint_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.COLON)
        expression = self.expect(TokenType.STRING).value
        self.expect(TokenType.COMMA)
        message = self.expect(TokenType.STRING).value
        self.expect(TokenType.SEMICOLON)
        
        return ConstraintNode(constraint_name, expression, message)

class SemanticAnalyzer:
    """语义分析器"""
    
    def __init__(self):
        self.symbol_table = {}
        self.errors = []
        self.warnings = []
    
    def analyze(self, ast: ModelNode) -> bool:
        """语义分析"""
        self.errors.clear()
        self.warnings.clear()
        
        # 分析模型
        self.analyze_model(ast)
        
        # 分析实体
        for entity in ast.entities:
            self.analyze_entity(entity, ast)
        
        # 分析操作
        for operation in ast.operations:
            self.analyze_operation(operation, ast)
        
        # 分析关系
        for relation in ast.relations:
            self.analyze_relation(relation, ast)
        
        # 分析约束
        for constraint in ast.constraints:
            self.analyze_constraint(constraint, ast)
        
        return len(self.errors) == 0
    
    def analyze_model(self, model: ModelNode):
        """分析模型"""
        if model.name in self.symbol_table:
            self.errors.append(f"Model '{model.name}' is already defined")
        else:
            self.symbol_table[model.name] = {
                'type': 'model',
                'node': model
            }
    
    def analyze_entity(self, entity: EntityNode, model: ModelNode):
        """分析实体"""
        entity_key = f"{model.name}.{entity.name}"
        
        if entity_key in self.symbol_table:
            self.errors.append(f"Entity '{entity.name}' is already defined in model '{model.name}'")
        else:
            self.symbol_table[entity_key] = {
                'type': 'entity',
                'node': entity,
                'model': model.name
            }
        
        # 分析属性
        for attr in entity.attributes:
            self.analyze_attribute(attr, entity, model)
    
    def analyze_attribute(self, attr: AttributeNode, entity: EntityNode, model: ModelNode):
        """分析属性"""
        attr_key = f"{model.name}.{entity.name}.{attr.name}"
        
        if attr_key in self.symbol_table:
            self.errors.append(f"Attribute '{attr.name}' is already defined in entity '{entity.name}'")
        else:
            self.symbol_table[attr_key] = {
                'type': 'attribute',
                'node': attr,
                'entity': entity.name,
                'model': model.name
            }
    
    def analyze_operation(self, operation: OperationNode, model: ModelNode):
        """分析操作"""
        op_key = f"{model.name}.{operation.name}"
        
        if op_key in self.symbol_table:
            self.errors.append(f"Operation '{operation.name}' is already defined in model '{model.name}'")
        else:
            self.symbol_table[op_key] = {
                'type': 'operation',
                'node': operation,
                'model': model.name
            }
        
        # 分析参数
        for param in operation.parameters:
            self.analyze_parameter(param, operation, model)
    
    def analyze_parameter(self, param: ParameterNode, operation: OperationNode, model: ModelNode):
        """分析参数"""
        param_key = f"{model.name}.{operation.name}.{param.name}"
        
        if param_key in self.symbol_table:
            self.errors.append(f"Parameter '{param.name}' is already defined in operation '{operation.name}'")
        else:
            self.symbol_table[param_key] = {
                'type': 'parameter',
                'node': param,
                'operation': operation.name,
                'model': model.name
            }
    
    def analyze_relation(self, relation: RelationNode, model: ModelNode):
        """分析关系"""
        relation_key = f"{model.name}.{relation.name}"
        
        if relation_key in self.symbol_table:
            self.errors.append(f"Relation '{relation.name}' is already defined in model '{model.name}'")
        else:
            # 检查源实体和目标实体是否存在
            source_key = f"{model.name}.{relation.source}"
            target_key = f"{model.name}.{relation.target}"
            
            if source_key not in self.symbol_table:
                self.errors.append(f"Source entity '{relation.source}' not found for relation '{relation.name}'")
            
            if target_key not in self.symbol_table:
                self.errors.append(f"Target entity '{relation.target}' not found for relation '{relation.name}'")
            
            self.symbol_table[relation_key] = {
                'type': 'relation',
                'node': relation,
                'model': model.name
            }
    
    def analyze_constraint(self, constraint: ConstraintNode, model: ModelNode):
        """分析约束"""
        constraint_key = f"{model.name}.{constraint.name}"
        
        if constraint_key in self.symbol_table:
            self.errors.append(f"Constraint '{constraint.name}' is already defined in model '{model.name}'")
        else:
            self.symbol_table[constraint_key] = {
                'type': 'constraint',
                'node': constraint,
                'model': model.name
            }
    
    def get_errors(self) -> List[str]:
        """获取错误列表"""
        return self.errors
    
    def get_warnings(self) -> List[str]:
        """获取警告列表"""
        return self.warnings

class CodeGenerator:
    """代码生成器"""
    
    def __init__(self, target_language: str = "java"):
        self.target_language = target_language
        self.generated_code = {}
    
    def generate(self, ast: ModelNode) -> Dict[str, str]:
        """生成代码"""
        self.generated_code.clear()
        
        if self.target_language == "java":
            self.generate_java(ast)
        elif self.target_language == "python":
            self.generate_python(ast)
        elif self.target_language == "typescript":
            self.generate_typescript(ast)
        else:
            raise ValueError(f"Unsupported target language: {self.target_language}")
        
        return self.generated_code
    
    def generate_java(self, ast: ModelNode):
        """生成Java代码"""
        # 生成实体类
        for entity in ast.entities:
            java_code = self.generate_java_entity(entity)
            self.generated_code[f"{entity.name}.java"] = java_code
        
        # 生成服务类
        service_code = self.generate_java_service(ast)
        self.generated_code[f"{ast.name}Service.java"] = service_code
        
        # 生成控制器类
        controller_code = self.generate_java_controller(ast)
        self.generated_code[f"{ast.name}Controller.java"] = controller_code
    
    def generate_java_entity(self, entity: EntityNode) -> str:
        """生成Java实体类"""
        code = []
        code.append("package com.formalmodel.entity;")
        code.append("")
        code.append("import javax.persistence.*;")
        code.append("import java.util.*;")
        code.append("")
        code.append(f"@Entity")
        code.append(f"@Table(name = \"{entity.name.lower()}\")")
        code.append(f"public class {entity.name} {{")
        code.append("")
        
        # 生成属性
        for attr in entity.attributes:
            java_type = self.map_type_to_java(attr.type)
            code.append(f"    @Column(name = \"{attr.name.lower()}\")")
            if not attr.required:
                code.append("    @Column(nullable = true)")
            code.append(f"    private {java_type} {attr.name};")
            code.append("")
        
        # 生成构造函数
        code.append(f"    public {entity.name}() {{")
        code.append("    }")
        code.append("")
        
        # 生成getter和setter
        for attr in entity.attributes:
            java_type = self.map_type_to_java(attr.type)
            code.append(f"    public {java_type} get{attr.name.capitalize()}() {{")
            code.append(f"        return {attr.name};")
            code.append("    }")
            code.append("")
            code.append(f"    public void set{attr.name.capitalize()}({java_type} {attr.name}) {{")
            code.append(f"        this.{attr.name} = {attr.name};")
            code.append("    }")
            code.append("")
        
        code.append("}")
        return '\n'.join(code)
    
    def generate_java_service(self, ast: ModelNode) -> str:
        """生成Java服务类"""
        code = []
        code.append("package com.formalmodel.service;")
        code.append("")
        code.append("import com.formalmodel.entity.*;")
        code.append("import com.formalmodel.repository.*;")
        code.append("import org.springframework.beans.factory.annotation.Autowired;")
        code.append("import org.springframework.stereotype.Service;")
        code.append("import java.util.*;")
        code.append("")
        code.append("@Service")
        code.append(f"public class {ast.name}Service {{")
        code.append("")
        
        # 生成依赖注入
        for entity in ast.entities:
            code.append(f"    @Autowired")
            code.append(f"    private {entity.name}Repository {entity.name.lower()}Repository;")
            code.append("")
        
        # 生成操作方法
        for operation in ast.operations:
            code.append(self.generate_java_operation(operation, ast))
            code.append("")
        
        code.append("}")
        return '\n'.join(code)
    
    def generate_java_operation(self, operation: OperationNode, ast: ModelNode) -> str:
        """生成Java操作方法"""
        code = []
        
        # 方法签名
        return_type = self.map_type_to_java(operation.return_type)
        params = []
        for param in operation.parameters:
            param_type = self.map_type_to_java(param.type)
            params.append(f"{param_type} {param.name}")
        
        code.append(f"    public {return_type} {operation.name}({', '.join(params)}) {{")
        
        # 方法体
        code.append("        // TODO: Implement operation logic")
        if return_type != "void":
            code.append(f"        return null; // TODO: Return actual value")
        
        code.append("    }")
        
        return '\n'.join(code)
    
    def generate_java_controller(self, ast: ModelNode) -> str:
        """生成Java控制器类"""
        code = []
        code.append("package com.formalmodel.controller;")
        code.append("")
        code.append("import com.formalmodel.service.*;")
        code.append("import org.springframework.beans.factory.annotation.Autowired;")
        code.append("import org.springframework.web.bind.annotation.*;")
        code.append("import java.util.*;")
        code.append("")
        code.append("@RestController")
        code.append(f"@RequestMapping(\"/api/{ast.name.lower()}\")")
        code.append(f"public class {ast.name}Controller {{")
        code.append("")
        
        code.append("    @Autowired")
        code.append(f"    private {ast.name}Service {ast.name.lower()}Service;")
        code.append("")
        
        # 生成API端点
        for operation in ast.operations:
            code.append(self.generate_java_endpoint(operation, ast))
            code.append("")
        
        code.append("}")
        return '\n'.join(code)
    
    def generate_java_endpoint(self, operation: OperationNode, ast: ModelNode) -> str:
        """生成Java API端点"""
        code = []
        
        # 确定HTTP方法
        http_method = "GET"
        if operation.name.startswith("create") or operation.name.startswith("add"):
            http_method = "POST"
        elif operation.name.startswith("update") or operation.name.startswith("modify"):
            http_method = "PUT"
        elif operation.name.startswith("delete") or operation.name.startswith("remove"):
            http_method = "DELETE"
        
        # 端点路径
        path = f"/{operation.name.lower()}"
        
        # 方法签名
        return_type = self.map_type_to_java(operation.return_type)
        params = []
        for param in operation.parameters:
            param_type = self.map_type_to_java(param.type)
            if param_type in ["String", "Integer", "Long", "Double", "Boolean"]:
                params.append(f"@RequestParam {param_type} {param.name}")
            else:
                params.append(f"@RequestBody {param_type} {param.name}")
        
        code.append(f"    @{http_method}Mapping(\"{path}\")")
        code.append(f"    public {return_type} {operation.name}({', '.join(params)}) {{")
        code.append(f"        return {ast.name.lower()}Service.{operation.name}({', '.join(p.name for p in operation.parameters)});")
        code.append("    }")
        
        return '\n'.join(code)
    
    def map_type_to_java(self, type_name: str) -> str:
        """映射类型到Java类型"""
        type_mapping = {
            'string': 'String',
            'number': 'Integer',
            'integer': 'Integer',
            'long': 'Long',
            'double': 'Double',
            'float': 'Float',
            'boolean': 'Boolean',
            'date': 'Date',
            'datetime': 'LocalDateTime',
            'list': 'List',
            'map': 'Map',
            'set': 'Set'
        }
        return type_mapping.get(type_name.lower(), 'Object')
    
    def generate_python(self, ast: ModelNode):
        """生成Python代码"""
        # 生成数据类
        for entity in ast.entities:
            python_code = self.generate_python_entity(entity)
            self.generated_code[f"{entity.name}.py"] = python_code
        
        # 生成服务类
        service_code = self.generate_python_service(ast)
        self.generated_code[f"{ast.name}_service.py"] = service_code
        
        # 生成API类
        api_code = self.generate_python_api(ast)
        self.generated_code[f"{ast.name}_api.py"] = api_code
    
    def generate_python_entity(self, entity: EntityNode) -> str:
        """生成Python实体类"""
        code = []
        code.append("from dataclasses import dataclass")
        code.append("from typing import Optional, List, Dict, Any")
        code.append("from datetime import datetime")
        code.append("")
        code.append("@dataclass")
        code.append(f"class {entity.name}:")
        
        # 生成属性
        for attr in entity.attributes:
            python_type = self.map_type_to_python(attr.type)
            if not attr.required:
                python_type = f"Optional[{python_type}]"
            code.append(f"    {attr.name}: {python_type}")
        
        code.append("")
        return '\n'.join(code)
    
    def generate_python_service(self, ast: ModelNode) -> str:
        """生成Python服务类"""
        code = []
        code.append("from typing import List, Optional, Dict, Any")
        code.append("")
        code.append(f"class {ast.name}Service:")
        code.append("    def __init__(self):")
        code.append("        pass")
        code.append("")
        
        # 生成操作方法
        for operation in ast.operations:
            code.append(self.generate_python_operation(operation, ast))
            code.append("")
        
        return '\n'.join(code)
    
    def generate_python_operation(self, operation: OperationNode, ast: ModelNode) -> str:
        """生成Python操作方法"""
        code = []
        
        # 方法签名
        return_type = self.map_type_to_python(operation.return_type)
        params = []
        for param in operation.parameters:
            param_type = self.map_type_to_python(param.type)
            if not param.required:
                param_type = f"Optional[{param_type}]"
            params.append(f"{param.name}: {param_type}")
        
        code.append(f"    def {operation.name}(self, {', '.join(params)}) -> {return_type}:")
        code.append("        # TODO: Implement operation logic")
        if return_type != "None":
            code.append("        return None  # TODO: Return actual value")
        
        return '\n'.join(code)
    
    def map_type_to_python(self, type_name: str) -> str:
        """映射类型到Python类型"""
        type_mapping = {
            'string': 'str',
            'number': 'int',
            'integer': 'int',
            'long': 'int',
            'double': 'float',
            'float': 'float',
            'boolean': 'bool',
            'date': 'datetime',
            'datetime': 'datetime',
            'list': 'List',
            'map': 'Dict',
            'set': 'Set'
        }
        return type_mapping.get(type_name.lower(), 'Any')
    
    def generate_typescript(self, ast: ModelNode):
        """生成TypeScript代码"""
        # 生成接口
        for entity in ast.entities:
            ts_code = self.generate_typescript_interface(entity)
            self.generated_code[f"{entity.name}.ts"] = ts_code
        
        # 生成服务类
        service_code = self.generate_typescript_service(ast)
        self.generated_code[f"{ast.name}Service.ts"] = service_code
    
    def generate_typescript_interface(self, entity: EntityNode) -> str:
        """生成TypeScript接口"""
        code = []
        code.append(f"export interface {entity.name} {{")
        
        # 生成属性
        for attr in entity.attributes:
            ts_type = self.map_type_to_typescript(attr.type)
            if not attr.required:
                ts_type = f"{ts_type}?"
            code.append(f"    {attr.name}: {ts_type};")
        
        code.append("}")
        code.append("")
        return '\n'.join(code)
    
    def generate_typescript_service(self, ast: ModelNode) -> str:
        """生成TypeScript服务类"""
        code = []
        code.append("import { Injectable } from '@angular/core';")
        code.append("import { HttpClient } from '@angular/common/http';")
        code.append("import { Observable } from 'rxjs';")
        code.append("")
        
        for entity in ast.entities:
            code.append(f"import {{ {entity.name} }} from './{entity.name}';")
        
        code.append("")
        code.append("@Injectable({")
        code.append("    providedIn: 'root'")
        code.append("})")
        code.append(f"export class {ast.name}Service {{")
        code.append("")
        code.append("    constructor(private http: HttpClient) {}")
        code.append("")
        
        # 生成操作方法
        for operation in ast.operations:
            code.append(self.generate_typescript_operation(operation, ast))
            code.append("")
        
        code.append("}")
        return '\n'.join(code)
    
    def generate_typescript_operation(self, operation: OperationNode, ast: ModelNode) -> str:
        """生成TypeScript操作方法"""
        code = []
        
        # 方法签名
        return_type = self.map_type_to_typescript(operation.return_type)
        params = []
        for param in operation.parameters:
            param_type = self.map_type_to_typescript(param.type)
            if not param.required:
                param_type = f"{param_type}?"
            params.append(f"{param.name}: {param_type}")
        
        code.append(f"    {operation.name}({', '.join(params)}): Observable<{return_type}> {{")
        code.append("        // TODO: Implement operation logic")
        code.append("        return this.http.get<{}>('/api/{}');".format(return_type, operation.name.lower()))
        code.append("    }")
        
        return '\n'.join(code)
    
    def map_type_to_typescript(self, type_name: str) -> str:
        """映射类型到TypeScript类型"""
        type_mapping = {
            'string': 'string',
            'number': 'number',
            'integer': 'number',
            'long': 'number',
            'double': 'number',
            'float': 'number',
            'boolean': 'boolean',
            'date': 'Date',
            'datetime': 'Date',
            'list': 'Array',
            'map': 'Map',
            'set': 'Set'
        }
        return type_mapping.get(type_name.lower(), 'any')

class FormalModelCompiler:
    """Formal Model编译器主类"""
    
    def __init__(self, target_language: str = "java"):
        self.target_language = target_language
        self.lexer = None
        self.parser = None
        self.semantic_analyzer = SemanticAnalyzer()
        self.code_generator = CodeGenerator(target_language)
    
    def compile(self, source: str) -> Dict[str, Any]:
        """编译Formal Model DSL"""
        try:
            # 词法分析
            logger.info("Starting lexical analysis...")
            self.lexer = Lexer(source)
            tokens = self.lexer.tokenize()
            
            # 检查词法错误
            error_tokens = [t for t in tokens if t.type == TokenType.ERROR]
            if error_tokens:
                errors = [f"Lexical error at line {t.line}, column {t.column}: unexpected character '{t.value}'" 
                         for t in error_tokens]
                return {
                    'success': False,
                    'errors': errors,
                    'warnings': []
                }
            
            # 语法分析
            logger.info("Starting syntax analysis...")
            self.parser = Parser(tokens)
            ast = self.parser.parse()
            
            # 语义分析
            logger.info("Starting semantic analysis...")
            semantic_success = self.semantic_analyzer.analyze(ast)
            
            if not semantic_success:
                return {
                    'success': False,
                    'errors': self.semantic_analyzer.get_errors(),
                    'warnings': self.semantic_analyzer.get_warnings()
                }
            
            # 代码生成
            logger.info("Starting code generation...")
            generated_code = self.code_generator.generate(ast)
            
            return {
                'success': True,
                'ast': ast,
                'generated_code': generated_code,
                'errors': [],
                'warnings': self.semantic_analyzer.get_warnings()
            }
            
        except Exception as e:
            logger.error(f"Compilation error: {str(e)}")
            return {
                'success': False,
                'errors': [str(e)],
                'warnings': []
            }

def main():
    """主函数"""
    # 示例DSL代码
    sample_dsl = """
    model ECommerceSystem: data_model {
        entity User {
            id: string;
            name: string;
            email: string;
            password: string;
        }
        
        entity Product {
            id: string;
            name: string;
            price: number;
            description: string;
        }
        
        entity Order {
            id: string;
            userId: string;
            total: number;
            status: string;
        }
        
        operation createUser(name: string, email: string, password: string) -> User;
        operation createProduct(name: string, price: number, description: string) -> Product;
        operation createOrder(userId: string, total: number) -> Order;
        
        relation UserOrders(User, Order): one-to-many;
        relation ProductOrders(Product, Order): many-to-many;
        
        constraint UserEmailUnique: "email must be unique", "Email already exists";
        constraint ProductPricePositive: "price > 0", "Price must be positive";
    }
    """
    
    # 创建编译器
    compiler = FormalModelCompiler("java")
    
    # 编译
    result = compiler.compile(sample_dsl)
    
    # 输出结果
    if result['success']:
        print("✅ Compilation successful!")
        print("\n📁 Generated files:")
        for filename, code in result['generated_code'].items():
            print(f"  - {filename}")
        
        print("\n⚠️  Warnings:")
        for warning in result['warnings']:
            print(f"  - {warning}")
        
        # 保存生成的文件
        import os
        output_dir = "generated"
        os.makedirs(output_dir, exist_ok=True)
        
        for filename, code in result['generated_code'].items():
            filepath = os.path.join(output_dir, filename)
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(code)
            print(f"💾 Saved: {filepath}")
        
    else:
        print("❌ Compilation failed!")
        print("\n🚨 Errors:")
        for error in result['errors']:
            print(f"  - {error}")

if __name__ == "__main__":
    main()
