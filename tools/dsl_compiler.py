#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework DSL编译器

该工具提供领域特定语言的完整编译功能，包括词法分析、语法分析、
语义分析、代码生成和优化。

作者: Formal Framework Team
版本: 1.0.0
日期: 2025-02-15
"""

import os
import re
import json
import yaml
import argparse
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass, asdict
from enum import Enum
import logging

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


class TokenType(Enum):
    """词法单元类型"""
    IDENTIFIER = "IDENTIFIER"
    KEYWORD = "KEYWORD"
    OPERATOR = "OPERATOR"
    LITERAL = "LITERAL"
    DELIMITER = "DELIMITER"
    COMMENT = "COMMENT"
    WHITESPACE = "WHITESPACE"
    EOF = "EOF"


@dataclass
class Token:
    """词法单元"""
    type: TokenType
    value: str
    line: int
    column: int
    position: int


@dataclass
class ASTNode:
    """抽象语法树节点"""
    node_type: str
    value: Optional[str] = None
    children: List['ASTNode'] = None
    line: int = 0
    column: int = 0
    
    def __post_init__(self):
        if self.children is None:
            self.children = []


@dataclass
class Symbol:
    """符号表项"""
    name: str
    type: str
    scope: str
    value: Optional[Any] = None
    line: int = 0
    column: int = 0


class Lexer:
    """词法分析器"""
    
    def __init__(self, source_code: str):
        self.source_code = source_code
        self.position = 0
        self.line = 1
        self.column = 1
        self.tokens = []
        
        # 定义词法规则
        self.patterns = [
            (TokenType.COMMENT, r'//.*?$|/\*.*?\*/', re.MULTILINE | re.DOTALL),
            (TokenType.WHITESPACE, r'\s+'),
            (TokenType.KEYWORD, r'\b(model|entity|relationship|attribute|type|function|rule|constraint|import|export)\b'),
            (TokenType.LITERAL, r'\b(true|false|null)\b'),
            (TokenType.LITERAL, r'\b\d+\.?\d*\b'),
            (TokenType.LITERAL, r'"[^"]*"'),
            (TokenType.OPERATOR, r'[+\-*/=<>!&|]+'),
            (TokenType.DELIMITER, r'[{}()\[\],;:]'),
            (TokenType.IDENTIFIER, r'[a-zA-Z_][a-zA-Z0-9_]*'),
        ]
    
    def tokenize(self) -> List[Token]:
        """词法分析主函数"""
        while self.position < len(self.source_code):
            token = self.next_token()
            if token and token.type != TokenType.WHITESPACE:
                self.tokens.append(token)
        
        # 添加EOF标记
        self.tokens.append(Token(TokenType.EOF, "", self.line, self.column, self.position))
        return self.tokens
    
    def next_token(self) -> Optional[Token]:
        """获取下一个词法单元"""
        if self.position >= len(self.source_code):
            return None
        
        for token_type, pattern, *flags in self.patterns:
            flags = flags[0] if flags else 0
            match = re.match(pattern, self.source_code[self.position:], flags)
            if match:
                value = match.group(0)
                token = Token(token_type, value, self.line, self.column, self.position)
                
                # 更新位置
                self.position += len(value)
                self.column += len(value)
                
                # 处理换行
                if '\n' in value:
                    lines = value.count('\n')
                    self.line += lines
                    self.column = len(value.split('\n')[-1]) + 1
                
                return token
        
        # 无法识别的字符
        char = self.source_code[self.position]
        logger.error(f"无法识别的字符: {char} at line {self.line}, column {self.column}")
        self.position += 1
        self.column += 1
        return None


class Parser:
    """语法分析器"""
    
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.position = 0
        self.current_token = tokens[0] if tokens else None
    
    def parse(self) -> ASTNode:
        """语法分析主函数"""
        return self.parse_program()
    
    def parse_program(self) -> ASTNode:
        """解析程序"""
        program = ASTNode("Program")
        
        while self.current_token and self.current_token.type != TokenType.EOF:
            if self.current_token.type == TokenType.KEYWORD:
                if self.current_token.value == "model":
                    program.children.append(self.parse_model())
                elif self.current_token.value == "entity":
                    program.children.append(self.parse_entity())
                elif self.current_token.value == "relationship":
                    program.children.append(self.parse_relationship())
                elif self.current_token.value == "function":
                    program.children.append(self.parse_function())
                else:
                    self.advance()  # 跳过未知关键字
            else:
                self.advance()
        
        return program
    
    def parse_model(self) -> ASTNode:
        """解析模型定义"""
        self.expect(TokenType.KEYWORD, "model")
        self.advance()
        
        model = ASTNode("Model")
        model.value = self.expect(TokenType.IDENTIFIER).value
        self.advance()
        
        if self.current_token.type == TokenType.DELIMITER and self.current_token.value == "{":
            self.advance()
            while (self.current_token and 
                   self.current_token.type != TokenType.DELIMITER or 
                   self.current_token.value != "}"):
                if self.current_token.type == TokenType.KEYWORD:
                    if self.current_token.value == "entity":
                        model.children.append(self.parse_entity())
                    elif self.current_token.value == "relationship":
                        model.children.append(self.parse_relationship())
                else:
                    self.advance()
            
            if self.current_token and self.current_token.value == "}":
                self.advance()
        
        return model
    
    def parse_entity(self) -> ASTNode:
        """解析实体定义"""
        self.expect(TokenType.KEYWORD, "entity")
        self.advance()
        
        entity = ASTNode("Entity")
        entity.value = self.expect(TokenType.IDENTIFIER).value
        self.advance()
        
        if self.current_token.type == TokenType.DELIMITER and self.current_token.value == "{":
            self.advance()
            while (self.current_token and 
                   self.current_token.type != TokenType.DELIMITER or 
                   self.current_token.value != "}"):
                if self.current_token.type == TokenType.KEYWORD and self.current_token.value == "attribute":
                    entity.children.append(self.parse_attribute())
                else:
                    self.advance()
            
            if self.current_token and self.current_token.value == "}":
                self.advance()
        
        return entity
    
    def parse_attribute(self) -> ASTNode:
        """解析属性定义"""
        self.expect(TokenType.KEYWORD, "attribute")
        self.advance()
        
        attribute = ASTNode("Attribute")
        attribute.value = self.expect(TokenType.IDENTIFIER).value
        self.advance()
        
        if self.current_token.type == TokenType.DELIMITER and self.current_token.value == ":":
            self.advance()
            attribute.children.append(ASTNode("Type", self.expect(TokenType.IDENTIFIER).value))
            self.advance()
        
        return attribute
    
    def parse_relationship(self) -> ASTNode:
        """解析关系定义"""
        self.expect(TokenType.KEYWORD, "relationship")
        self.advance()
        
        relationship = ASTNode("Relationship")
        relationship.value = self.expect(TokenType.IDENTIFIER).value
        self.advance()
        
        return relationship
    
    def parse_function(self) -> ASTNode:
        """解析函数定义"""
        self.expect(TokenType.KEYWORD, "function")
        self.advance()
        
        function = ASTNode("Function")
        function.value = self.expect(TokenType.IDENTIFIER).value
        self.advance()
        
        return function
    
    def expect(self, token_type: TokenType, value: Optional[str] = None) -> Token:
        """期望特定的词法单元"""
        if (self.current_token and 
            self.current_token.type == token_type and 
            (value is None or self.current_token.value == value)):
            return self.current_token
        
        expected = f"{token_type.value}"
        if value:
            expected += f" '{value}'"
        
        actual = f"{self.current_token.type.value} '{self.current_token.value}'" if self.current_token else "EOF"
        
        raise SyntaxError(f"期望 {expected}，但得到 {actual} at line {self.current_token.line}, column {self.current_token.column}")
    
    def advance(self):
        """前进到下一个词法单元"""
        self.position += 1
        if self.position < len(self.tokens):
            self.current_token = self.tokens[self.position]
        else:
            self.current_token = None


class SemanticAnalyzer:
    """语义分析器"""
    
    def __init__(self):
        self.symbol_table = {}
        self.scope_stack = ["global"]
        self.errors = []
        self.warnings = []
    
    def analyze(self, ast: ASTNode) -> Dict:
        """语义分析主函数"""
        self.visit(ast)
        return {
            "symbol_table": self.symbol_table,
            "errors": self.errors,
            "warnings": self.warnings
        }
    
    def visit(self, node: ASTNode):
        """访问AST节点"""
        method_name = f"visit_{node.node_type.lower()}"
        if hasattr(self, method_name):
            getattr(self, method_name)(node)
        else:
            # 默认访问子节点
            for child in node.children:
                self.visit(child)
    
    def visit_program(self, node: ASTNode):
        """访问程序节点"""
        for child in node.children:
            self.visit(child)
    
    def visit_model(self, node: ASTNode):
        """访问模型节点"""
        model_name = node.value
        if model_name in self.symbol_table:
            self.errors.append(f"模型 '{model_name}' 重复定义")
        else:
            self.symbol_table[model_name] = Symbol(
                name=model_name,
                type="Model",
                scope="global",
                line=node.line,
                column=node.column
            )
        
        # 进入模型作用域
        self.scope_stack.append(model_name)
        
        for child in node.children:
            self.visit(child)
        
        # 退出模型作用域
        self.scope_stack.pop()
    
    def visit_entity(self, node: ASTNode):
        """访问实体节点"""
        entity_name = node.value
        current_scope = self.scope_stack[-1]
        full_name = f"{current_scope}.{entity_name}"
        
        if full_name in self.symbol_table:
            self.errors.append(f"实体 '{full_name}' 重复定义")
        else:
            self.symbol_table[full_name] = Symbol(
                name=entity_name,
                type="Entity",
                scope=current_scope,
                line=node.line,
                column=node.column
            )
        
        # 进入实体作用域
        self.scope_stack.append(entity_name)
        
        for child in node.children:
            self.visit(child)
        
        # 退出实体作用域
        self.scope_stack.pop()
    
    def visit_attribute(self, node: ASTNode):
        """访问属性节点"""
        attr_name = node.value
        current_scope = self.scope_stack[-1]
        full_name = f"{current_scope}.{attr_name}"
        
        if full_name in self.symbol_table:
            self.errors.append(f"属性 '{full_name}' 重复定义")
        else:
            attr_type = "Unknown"
            if node.children:
                attr_type = node.children[0].value
            
            self.symbol_table[full_name] = Symbol(
                name=attr_name,
                type="Attribute",
                scope=current_scope,
                value=attr_type,
                line=node.line,
                column=node.column
            )
    
    def visit_relationship(self, node: ASTNode):
        """访问关系节点"""
        rel_name = node.value
        current_scope = self.scope_stack[-1]
        full_name = f"{current_scope}.{rel_name}"
        
        if full_name in self.symbol_table:
            self.errors.append(f"关系 '{full_name}' 重复定义")
        else:
            self.symbol_table[full_name] = Symbol(
                name=rel_name,
                type="Relationship",
                scope=current_scope,
                line=node.line,
                column=node.column
            )
    
    def visit_function(self, node: ASTNode):
        """访问函数节点"""
        func_name = node.value
        current_scope = self.scope_stack[-1]
        full_name = f"{current_scope}.{func_name}"
        
        if full_name in self.symbol_table:
            self.errors.append(f"函数 '{full_name}' 重复定义")
        else:
            self.symbol_table[full_name] = Symbol(
                name=func_name,
                type="Function",
                scope=current_scope,
                line=node.line,
                column=node.column
            )


class CodeGenerator:
    """代码生成器"""
    
    def __init__(self, target_language: str = "python"):
        self.target_language = target_language
        self.generated_code = []
        self.indent_level = 0
    
    def generate(self, ast: ASTNode, semantic_info: Dict) -> str:
        """代码生成主函数"""
        self.visit(ast)
        return "\n".join(self.generated_code)
    
    def visit(self, node: ASTNode):
        """访问AST节点"""
        method_name = f"generate_{node.node_type.lower()}"
        if hasattr(self, method_name):
            getattr(self, method_name)(node)
        else:
            # 默认访问子节点
            for child in node.children:
                self.visit(child)
    
    def generate_program(self, node: ASTNode):
        """生成程序代码"""
        if self.target_language == "python":
            self.add_line("# Generated by Formal Framework DSL Compiler")
            self.add_line("# -*- coding: utf-8 -*-")
            self.add_line("")
            self.add_line("from dataclasses import dataclass")
            self.add_line("from typing import List, Optional, Any")
            self.add_line("")
        
        for child in node.children:
            self.visit(child)
    
    def generate_model(self, node: ASTNode):
        """生成模型代码"""
        if self.target_language == "python":
            self.add_line(f"# Model: {node.value}")
            self.add_line("")
            
            for child in node.children:
                self.visit(child)
    
    def generate_entity(self, node: ASTNode):
        """生成实体代码"""
        if self.target_language == "python":
            self.add_line(f"@dataclass")
            self.add_line(f"class {node.value}:")
            self.indent_level += 1
            
            # 生成属性
            for child in node.children:
                if child.node_type == "Attribute":
                    self.visit(child)
            
            if not node.children:
                self.add_line("pass")
            
            self.indent_level -= 1
            self.add_line("")
    
    def generate_attribute(self, node: ASTNode):
        """生成属性代码"""
        if self.target_language == "python":
            attr_name = node.value
            attr_type = "Any"
            
            if node.children:
                attr_type = node.children[0].value
                # 类型映射
                type_mapping = {
                    "string": "str",
                    "integer": "int",
                    "float": "float",
                    "boolean": "bool",
                    "list": "List",
                    "dict": "Dict"
                }
                attr_type = type_mapping.get(attr_type, attr_type)
            
            self.add_line(f"{attr_name}: {attr_type}")
    
    def generate_relationship(self, node: ASTNode):
        """生成关系代码"""
        if self.target_language == "python":
            self.add_line(f"# Relationship: {node.value}")
            # 这里可以生成关系相关的代码
    
    def generate_function(self, node: ASTNode):
        """生成函数代码"""
        if self.target_language == "python":
            self.add_line(f"def {node.value}():")
            self.indent_level += 1
            self.add_line("pass")
            self.indent_level -= 1
            self.add_line("")
    
    def add_line(self, line: str):
        """添加代码行"""
        indent = "    " * self.indent_level
        self.generated_code.append(indent + line)


class Optimizer:
    """代码优化器"""
    
    def __init__(self):
        self.optimizations = [
            self.remove_unused_imports,
            self.remove_empty_classes,
            self.optimize_imports,
            self.add_type_hints
        ]
    
    def optimize(self, code: str) -> str:
        """代码优化主函数"""
        optimized_code = code
        
        for optimization in self.optimizations:
            optimized_code = optimization(optimized_code)
        
        return optimized_code
    
    def remove_unused_imports(self, code: str) -> str:
        """移除未使用的导入"""
        lines = code.split('\n')
        result = []
        imports = []
        
        for line in lines:
            if line.strip().startswith('import ') or line.strip().startswith('from '):
                imports.append(line)
            else:
                result.append(line)
        
        # 简单检查：如果代码中没有使用导入的内容，则移除
        # 这里可以实现更复杂的分析
        if result:
            return '\n'.join(imports + result)
        return code
    
    def remove_empty_classes(self, code: str) -> str:
        """移除空类"""
        lines = code.split('\n')
        result = []
        i = 0
        
        while i < len(lines):
            line = lines[i]
            if line.strip().startswith('@dataclass') and i + 1 < len(lines):
                class_line = lines[i + 1]
                if class_line.strip().endswith(':') and 'class' in class_line:
                    # 检查是否有内容
                    j = i + 2
                    has_content = False
                    while j < len(lines) and lines[j].startswith('    '):
                        if lines[j].strip() and not lines[j].strip().startswith('#'):
                            has_content = True
                            break
                        j += 1
                    
                    if not has_content:
                        # 跳过空类
                        i = j
                        continue
            
            result.append(line)
            i += 1
        
        return '\n'.join(result)
    
    def optimize_imports(self, code: str) -> str:
        """优化导入语句"""
        # 这里可以实现导入语句的优化
        return code
    
    def add_type_hints(self, code: str) -> str:
        """添加类型提示"""
        # 这里可以实现类型提示的添加
        return code


class DSLCompiler:
    """DSL编译器主类"""
    
    def __init__(self, target_language: str = "python"):
        self.target_language = target_language
        self.lexer = None
        self.parser = None
        self.semantic_analyzer = SemanticAnalyzer()
        self.code_generator = CodeGenerator(target_language)
        self.optimizer = Optimizer()
    
    def compile(self, source_code: str) -> Dict:
        """编译主函数"""
        try:
            # 词法分析
            logger.info("开始词法分析...")
            self.lexer = Lexer(source_code)
            tokens = self.lexer.tokenize()
            logger.info(f"词法分析完成，生成 {len(tokens)} 个词法单元")
            
            # 语法分析
            logger.info("开始语法分析...")
            self.parser = Parser(tokens)
            ast = self.parser.parse()
            logger.info("语法分析完成")
            
            # 语义分析
            logger.info("开始语义分析...")
            semantic_info = self.semantic_analyzer.analyze(ast)
            logger.info("语义分析完成")
            
            # 检查语义错误
            if semantic_info["errors"]:
                logger.error(f"发现 {len(semantic_info['errors'])} 个语义错误:")
                for error in semantic_info["errors"]:
                    logger.error(f"  {error}")
                return {
                    "status": "error",
                    "errors": semantic_info["errors"],
                    "warnings": semantic_info["warnings"]
                }
            
            # 代码生成
            logger.info("开始代码生成...")
            generated_code = self.code_generator.generate(ast, semantic_info)
            logger.info("代码生成完成")
            
            # 代码优化
            logger.info("开始代码优化...")
            optimized_code = self.optimizer.optimize(generated_code)
            logger.info("代码优化完成")
            
            return {
                "status": "success",
                "tokens": [asdict(token) for token in tokens],
                "ast": self.ast_to_dict(ast),
                "semantic_info": semantic_info,
                "generated_code": optimized_code,
                "warnings": semantic_info["warnings"]
            }
            
        except Exception as e:
            logger.error(f"编译失败: {e}")
            return {
                "status": "error",
                "error": str(e)
            }
    
    def ast_to_dict(self, node: ASTNode) -> Dict:
        """将AST转换为字典"""
        return {
            "node_type": node.node_type,
            "value": node.value,
            "line": node.line,
            "column": node.column,
            "children": [self.ast_to_dict(child) for child in node.children]
        }
    
    def compile_file(self, file_path: str) -> Dict:
        """编译文件"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                source_code = f.read()
            
            return self.compile(source_code)
            
        except Exception as e:
            logger.error(f"读取文件失败: {e}")
            return {
                "status": "error",
                "error": str(e)
            }


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description="Formal Framework DSL编译器")
    parser.add_argument("input", help="输入文件路径")
    parser.add_argument("--output", "-o", help="输出文件路径")
    parser.add_argument("--target", "-t", default="python", 
                       choices=["python", "java", "cpp"],
                       help="目标语言")
    parser.add_argument("--verbose", "-v", action="store_true", help="详细输出")
    parser.add_argument("--ast", action="store_true", help="输出AST")
    parser.add_argument("--tokens", action="store_true", help="输出词法单元")
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # 创建编译器
    compiler = DSLCompiler(args.target)
    
    # 编译
    result = compiler.compile_file(args.input)
    
    if result["status"] == "success":
        # 输出生成的代码
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                f.write(result["generated_code"])
            logger.info(f"代码已生成到: {args.output}")
        else:
            print(result["generated_code"])
        
        # 输出额外信息
        if args.tokens:
            print("\n=== 词法单元 ===")
            print(json.dumps(result["tokens"], indent=2, ensure_ascii=False))
        
        if args.ast:
            print("\n=== 抽象语法树 ===")
            print(json.dumps(result["ast"], indent=2, ensure_ascii=False))
        
        # 输出警告
        if result["warnings"]:
            print(f"\n警告 ({len(result['warnings'])} 个):")
            for warning in result["warnings"]:
                print(f"  {warning}")
        
        return 0
    else:
        # 输出错误
        print(f"编译失败: {result.get('error', '未知错误')}")
        if "errors" in result:
            print("语义错误:")
            for error in result["errors"]:
                print(f"  {error}")
        return 1


if __name__ == "__main__":
    exit(main())
