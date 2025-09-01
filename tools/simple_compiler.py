#!/usr/bin/env python3
"""
Simple Formal Model DSL Compiler
简化版的Formal Model DSL编译器
"""

import re
import json
import yaml
from typing import Dict, List, Optional, Any
from dataclasses import dataclass
from enum import Enum

class TokenType(Enum):
    """词法单元类型"""
    MODEL = "MODEL"
    ENTITY = "ENTITY"
    OPERATION = "OPERATION"
    IDENTIFIER = "IDENTIFIER"
    STRING = "STRING"
    NUMBER = "NUMBER"
    EQUALS = "EQUALS"
    COLON = "COLON"
    SEMICOLON = "SEMICOLON"
    COMMA = "COMMA"
    LBRACE = "LBRACE"
    RBRACE = "RBRACE"
    LPAREN = "LPAREN"
    RPAREN = "RPAREN"
    ARROW = "ARROW"
    EOF = "EOF"

@dataclass
class Token:
    """词法单元"""
    type: TokenType
    value: str
    line: int

class SimpleLexer:
    """简化词法分析器"""
    
    def __init__(self, source: str):
        self.source = source
        self.position = 0
        self.line = 1
        self.tokens = []
        
        # 关键字
        self.keywords = {
            'model': TokenType.MODEL,
            'entity': TokenType.ENTITY,
            'operation': TokenType.OPERATION
        }
    
    def tokenize(self) -> List[Token]:
        """词法分析"""
        while self.position < len(self.source):
            char = self.source[self.position]
            
            # 跳过空白字符
            if char.isspace():
                if char == '\n':
                    self.line += 1
                self.position += 1
                continue
            
            # 跳过注释
            if char == '/' and self.position + 1 < len(self.source):
                if self.source[self.position + 1] == '/':
                    while self.position < len(self.source) and self.source[self.position] != '\n':
                        self.position += 1
                    continue
            
            # 标识符和关键字
            if char.isalpha() or char == '_':
                identifier = self.read_identifier()
                token_type = self.keywords.get(identifier.lower(), TokenType.IDENTIFIER)
                self.tokens.append(Token(token_type, identifier, self.line))
                continue
            
            # 数字
            if char.isdigit():
                number = self.read_number()
                self.tokens.append(Token(TokenType.NUMBER, number, self.line))
                continue
            
            # 字符串
            if char == '"':
                string = self.read_string()
                self.tokens.append(Token(TokenType.STRING, string, self.line))
                continue
            
            # 单字符标记
            if char == '=':
                self.tokens.append(Token(TokenType.EQUALS, char, self.line))
            elif char == ':':
                self.tokens.append(Token(TokenType.COLON, char, self.line))
            elif char == ';':
                self.tokens.append(Token(TokenType.SEMICOLON, char, self.line))
            elif char == ',':
                self.tokens.append(Token(TokenType.COMMA, char, self.line))
            elif char == '{':
                self.tokens.append(Token(TokenType.LBRACE, char, self.line))
            elif char == '}':
                self.tokens.append(Token(TokenType.RBRACE, char, self.line))
            elif char == '(':
                self.tokens.append(Token(TokenType.LPAREN, char, self.line))
            elif char == ')':
                self.tokens.append(Token(TokenType.RPAREN, char, self.line))
            elif char == '-':
                if self.position + 1 < len(self.source) and self.source[self.position + 1] == '>':
                    self.tokens.append(Token(TokenType.ARROW, '->', self.line))
                    self.position += 1
                else:
                    self.tokens.append(Token(TokenType.IDENTIFIER, char, self.line))
            else:
                # 未知字符
                self.tokens.append(Token(TokenType.IDENTIFIER, char, self.line))
            
            self.position += 1
        
        self.tokens.append(Token(TokenType.EOF, "", self.line))
        return self.tokens
    
    def read_identifier(self) -> str:
        """读取标识符"""
        start = self.position
        while (self.position < len(self.source) and 
               (self.source[self.position].isalnum() or self.source[self.position] == '_')):
            self.position += 1
        return self.source[start:self.position]
    
    def read_number(self) -> str:
        """读取数字"""
        start = self.position
        while (self.position < len(self.source) and 
               (self.source[self.position].isdigit() or self.source[self.position] == '.')):
            self.position += 1
        return self.source[start:self.position]
    
    def read_string(self) -> str:
        """读取字符串"""
        self.position += 1  # 跳过开始的引号
        start = self.position
        while (self.position < len(self.source) and 
               self.source[self.position] != '"'):
            self.position += 1
        string = self.source[start:self.position]
        self.position += 1  # 跳过结束的引号
        return string

@dataclass
class ASTNode:
    """抽象语法树节点"""
    pass

@dataclass
class ModelNode(ASTNode):
    """模型节点"""
    name: str
    type: str
    entities: List['EntityNode']
    operations: List['OperationNode']

@dataclass
class EntityNode(ASTNode):
    """实体节点"""
    name: str
    attributes: List['AttributeNode']

@dataclass
class AttributeNode(ASTNode):
    """属性节点"""
    name: str
    type: str

@dataclass
class OperationNode(ASTNode):
    """操作节点"""
    name: str
    parameters: List['ParameterNode']
    return_type: str

@dataclass
class ParameterNode(ASTNode):
    """参数节点"""
    name: str
    type: str

class SimpleParser:
    """简化语法分析器"""
    
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
        
        while self.current_token and self.current_token.type != TokenType.RBRACE:
            if self.current_token.type == TokenType.ENTITY:
                entities.append(self.parse_entity())
            elif self.current_token.type == TokenType.OPERATION:
                operations.append(self.parse_operation())
            else:
                self.advance()  # 跳过未知标记
        
        self.expect(TokenType.RBRACE)
        
        return ModelNode(model_name, model_type, entities, operations)
    
    def parse_entity(self) -> EntityNode:
        """解析实体"""
        self.expect(TokenType.ENTITY)
        entity_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.LBRACE)
        
        attributes = []
        while self.current_token and self.current_token.type != TokenType.RBRACE:
            if self.current_token.type == TokenType.IDENTIFIER:
                attributes.append(self.parse_attribute())
            else:
                self.advance()
        
        self.expect(TokenType.RBRACE)
        return EntityNode(entity_name, attributes)
    
    def parse_attribute(self) -> AttributeNode:
        """解析属性"""
        attr_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.COLON)
        attr_type = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.SEMICOLON)
        return AttributeNode(attr_name, attr_type)
    
    def parse_operation(self) -> OperationNode:
        """解析操作"""
        self.expect(TokenType.OPERATION)
        op_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.LPAREN)
        
        parameters = []
        if self.current_token and self.current_token.type != TokenType.RPAREN:
            parameters.append(self.parse_parameter())
            # 处理多个参数，用逗号分隔
            while self.current_token and self.current_token.type == TokenType.COMMA:
                self.expect(TokenType.COMMA)  # 跳过逗号
                parameters.append(self.parse_parameter())
        
        self.expect(TokenType.RPAREN)
        self.expect(TokenType.ARROW)
        return_type = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.SEMICOLON)
        
        return OperationNode(op_name, parameters, return_type)
    
    def parse_parameter(self) -> ParameterNode:
        """解析参数"""
        param_name = self.expect(TokenType.IDENTIFIER).value
        self.expect(TokenType.COLON)
        param_type = self.expect(TokenType.IDENTIFIER).value
        return ParameterNode(param_name, param_type)

class SimpleCodeGenerator:
    """简化代码生成器"""
    
    def __init__(self, target_language: str = "java"):
        self.target_language = target_language
    
    def generate(self, ast: ModelNode) -> Dict[str, str]:
        """生成代码"""
        if self.target_language == "java":
            return self.generate_java(ast)
        elif self.target_language == "python":
            return self.generate_python(ast)
        else:
            raise ValueError(f"Unsupported target language: {self.target_language}")
    
    def generate_java(self, ast: ModelNode) -> Dict[str, str]:
        """生成Java代码"""
        generated_code = {}
        
        # 生成实体类
        for entity in ast.entities:
            java_code = self.generate_java_entity(entity)
            generated_code[f"{entity.name}.java"] = java_code
        
        # 生成服务类
        service_code = self.generate_java_service(ast)
        generated_code[f"{ast.name}Service.java"] = service_code
        
        return generated_code
    
    def generate_java_entity(self, entity: EntityNode) -> str:
        """生成Java实体类"""
        code = []
        code.append("package com.formalmodel.entity;")
        code.append("")
        code.append("import javax.persistence.*;")
        code.append("")
        code.append(f"@Entity")
        code.append(f"@Table(name = \"{entity.name.lower()}\")")
        code.append(f"public class {entity.name} {{")
        code.append("")
        
        # 生成属性
        for attr in entity.attributes:
            java_type = self.map_type_to_java(attr.type)
            code.append(f"    @Column(name = \"{attr.name.lower()}\")")
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
        code.append("import org.springframework.stereotype.Service;")
        code.append("import java.util.*;")
        code.append("")
        code.append("@Service")
        code.append(f"public class {ast.name}Service {{")
        code.append("")
        
        # 生成操作方法
        for operation in ast.operations:
            code.append(self.generate_java_operation(operation))
            code.append("")
        
        code.append("}")
        return '\n'.join(code)
    
    def generate_java_operation(self, operation: OperationNode) -> str:
        """生成Java操作方法"""
        code = []
        
        # 方法签名
        return_type = self.map_type_to_java(operation.return_type)
        params = []
        for param in operation.parameters:
            param_type = self.map_type_to_java(param.type)
            params.append(f"{param_type} {param.name}")
        
        code.append(f"    public {return_type} {operation.name}({', '.join(params)}) {{")
        code.append("        // TODO: Implement operation logic")
        if return_type != "void":
            code.append(f"        return null; // TODO: Return actual value")
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
            'datetime': 'LocalDateTime'
        }
        return type_mapping.get(type_name.lower(), 'Object')
    
    def generate_python(self, ast: ModelNode) -> Dict[str, str]:
        """生成Python代码"""
        generated_code = {}
        
        # 生成数据类
        for entity in ast.entities:
            python_code = self.generate_python_entity(entity)
            generated_code[f"{entity.name}.py"] = python_code
        
        # 生成服务类
        service_code = self.generate_python_service(ast)
        generated_code[f"{ast.name}_service.py"] = service_code
        
        return generated_code
    
    def generate_python_entity(self, entity: EntityNode) -> str:
        """生成Python实体类"""
        code = []
        code.append("from dataclasses import dataclass")
        code.append("from typing import Optional")
        code.append("")
        code.append("@dataclass")
        code.append(f"class {entity.name}:")
        
        # 生成属性
        for attr in entity.attributes:
            python_type = self.map_type_to_python(attr.type)
            code.append(f"    {attr.name}: {python_type}")
        
        code.append("")
        return '\n'.join(code)
    
    def generate_python_service(self, ast: ModelNode) -> str:
        """生成Python服务类"""
        code = []
        code.append("from typing import List, Optional")
        code.append("")
        code.append(f"class {ast.name}Service:")
        code.append("    def __init__(self):")
        code.append("        pass")
        code.append("")
        
        # 生成操作方法
        for operation in ast.operations:
            code.append(self.generate_python_operation(operation))
            code.append("")
        
        return '\n'.join(code)
    
    def generate_python_operation(self, operation: OperationNode) -> str:
        """生成Python操作方法"""
        code = []
        
        # 方法签名
        return_type = self.map_type_to_python(operation.return_type)
        params = []
        for param in operation.parameters:
            param_type = self.map_type_to_python(param.type)
            params.append(f"{param.name}: {param_type}")
        
        code.append(f"    def {operation.name}(self, {', '.join(params)}) -> {return_type}:")
        code.append("        # TODO: Implement operation logic")
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
            'datetime': 'datetime'
        }
        return type_mapping.get(type_name.lower(), 'Any')

class SimpleCompiler:
    """简化编译器"""
    
    def __init__(self, target_language: str = "java"):
        self.target_language = target_language
    
    def compile(self, source: str) -> Dict[str, Any]:
        """编译Formal Model DSL"""
        try:
            # 词法分析
            lexer = SimpleLexer(source)
            tokens = lexer.tokenize()
            
            # 语法分析
            parser = SimpleParser(tokens)
            ast = parser.parse()
            
            # 代码生成
            code_generator = SimpleCodeGenerator(self.target_language)
            generated_code = code_generator.generate(ast)
            
            return {
                'success': True,
                'ast': ast,
                'generated_code': generated_code,
                'errors': [],
                'warnings': []
            }
            
        except Exception as e:
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
        }
        
        entity Product {
            id: string;
            name: string;
            price: number;
        }
        
        operation createUser(name: string, email: string) -> User;
        operation createProduct(name: string, price: number) -> Product;
    }
    """
    
    # 创建编译器
    compiler = SimpleCompiler("python")
    
    # 编译
    result = compiler.compile(sample_dsl)
    
    # 输出结果
    if result['success']:
        print("✅ Compilation successful!")
        print("\n📁 Generated files:")
        for filename, code in result['generated_code'].items():
            print(f"  - {filename}")
        
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
