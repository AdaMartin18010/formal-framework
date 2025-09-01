#!/usr/bin/env python3
"""
Formal Model CLI Tool
命令行工具，提供Formal Model框架的核心功能
"""

import argparse
import sys
import os
from pathlib import Path
from typing import Optional, List
import json
import yaml

# 导入编译器
from simple_compiler import SimpleCompiler


class FormalModelCLI:
    """Formal Model 命令行工具"""
    
    def __init__(self):
        self.compiler = SimpleCompiler()
        self.config = self._load_config()
    
    def _load_config(self) -> dict:
        """加载配置文件"""
        config_path = Path("config.yaml")
        if config_path.exists():
            with open(config_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        return {
            'output_dir': 'generated',
            'target_languages': ['java', 'python'],
            'verbose': False
        }
    
    def compile(self, source_file: str, output_dir: Optional[str] = None, 
                target_languages: Optional[List[str]] = None) -> bool:
        """编译DSL文件"""
        try:
            print(f"🔧 编译文件: {source_file}")
            
            # 读取源文件
            with open(source_file, 'r', encoding='utf-8') as f:
                source_code = f.read()
            
            # 设置输出目录
            if output_dir is None:
                output_dir = self.config.get('output_dir', 'generated')
            
            # 设置目标语言
            if target_languages is None:
                target_languages = self.config.get('target_languages', ['java', 'python'])
            
            # 编译
            success = self.compiler.compile(source_code, output_dir, target_languages)
            
            if success:
                print(f"✅ 编译成功！输出目录: {output_dir}")
                return True
            else:
                print("❌ 编译失败")
                return False
                
        except FileNotFoundError:
            print(f"❌ 文件未找到: {source_file}")
            return False
        except Exception as e:
            print(f"❌ 编译错误: {e}")
            return False
    
    def validate(self, source_file: str) -> bool:
        """验证DSL文件语法"""
        try:
            print(f"🔍 验证文件: {source_file}")
            
            with open(source_file, 'r', encoding='utf-8') as f:
                source_code = f.read()
            
            # 尝试词法分析
            tokens = self.compiler.lexer.tokenize(source_code)
            if not tokens:
                print("❌ 词法分析失败")
                return False
            
            # 尝试语法分析
            ast = self.compiler.parser.parse(tokens)
            if not ast:
                print("❌ 语法分析失败")
                return False
            
            print("✅ 语法验证通过")
            return True
            
        except Exception as e:
            print(f"❌ 验证错误: {e}")
            return False
    
    def generate_docs(self, source_file: str, output_file: Optional[str] = None) -> bool:
        """生成文档"""
        try:
            print(f"📚 生成文档: {source_file}")
            
            with open(source_file, 'r', encoding='utf-8') as f:
                source_code = f.read()
            
            # 解析AST
            tokens = self.compiler.lexer.tokenize(source_code)
            ast = self.compiler.parser.parse(tokens)
            
            if not ast:
                print("❌ 解析失败，无法生成文档")
                return False
            
            # 生成文档内容
            doc_content = self._generate_documentation(ast)
            
            # 设置输出文件
            if output_file is None:
                output_file = Path(source_file).stem + "_docs.md"
            
            # 保存文档
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(doc_content)
            
            print(f"✅ 文档生成成功: {output_file}")
            return True
            
        except Exception as e:
            print(f"❌ 文档生成错误: {e}")
            return False
    
    def _generate_documentation(self, ast) -> str:
        """从AST生成文档"""
        doc_lines = []
        doc_lines.append("# Formal Model 文档")
        doc_lines.append("")
        
        if hasattr(ast, 'models'):
            for model in ast.models:
                doc_lines.append(f"## 模型: {model.name}")
                doc_lines.append("")
                
                if hasattr(model, 'entities'):
                    doc_lines.append("### 实体")
                    for entity in model.entities:
                        doc_lines.append(f"- **{entity.name}**")
                        if hasattr(entity, 'attributes'):
                            for attr in entity.attributes:
                                doc_lines.append(f"  - {attr.name}: {attr.type}")
                        doc_lines.append("")
                
                if hasattr(model, 'operations'):
                    doc_lines.append("### 操作")
                    for op in model.operations:
                        params = ", ".join([f"{p.name}: {p.type}" for p in op.parameters])
                        doc_lines.append(f"- **{op.name}**({params}) -> {op.return_type}")
                    doc_lines.append("")
        
        return "\n".join(doc_lines)
    
    def list_templates(self) -> None:
        """列出可用的模板"""
        templates = [
            {
                'name': 'ecommerce',
                'description': '电子商务系统模板',
                'file': 'templates/ecommerce.dsl'
            },
            {
                'name': 'banking',
                'description': '银行系统模板',
                'file': 'templates/banking.dsl'
            },
            {
                'name': 'inventory',
                'description': '库存管理系统模板',
                'file': 'templates/inventory.dsl'
            }
        ]
        
        print("📋 可用模板:")
        for template in templates:
            print(f"  - {template['name']}: {template['description']}")
    
    def create_project(self, project_name: str, template: Optional[str] = None) -> bool:
        """创建新项目"""
        try:
            print(f"🚀 创建项目: {project_name}")
            
            # 创建项目目录
            project_dir = Path(project_name)
            project_dir.mkdir(exist_ok=True)
            
            # 创建子目录
            (project_dir / "src").mkdir(exist_ok=True)
            (project_dir / "docs").mkdir(exist_ok=True)
            (project_dir / "tests").mkdir(exist_ok=True)
            
            # 创建配置文件
            config = {
                'project_name': project_name,
                'version': '1.0.0',
                'output_dir': 'generated',
                'target_languages': ['java', 'python']
            }
            
            with open(project_dir / "formal-model.yaml", 'w', encoding='utf-8') as f:
                yaml.dump(config, f, default_flow_style=False, allow_unicode=True)
            
            # 创建示例DSL文件
            sample_dsl = self._get_sample_dsl(template)
            with open(project_dir / "src" / "main.dsl", 'w', encoding='utf-8') as f:
                f.write(sample_dsl)
            
            # 创建README
            readme_content = f"""# {project_name}

Formal Model 项目

## 使用方法

1. 编辑 `src/main.dsl` 文件
2. 运行编译命令: `formal-model compile src/main.dsl`
3. 查看生成的代码在 `generated/` 目录

## 项目结构

- `src/`: DSL源文件
- `docs/`: 文档
- `tests/`: 测试文件
- `generated/`: 生成的代码
"""
            
            with open(project_dir / "README.md", 'w', encoding='utf-8') as f:
                f.write(readme_content)
            
            print(f"✅ 项目创建成功: {project_dir}")
            return True
            
        except Exception as e:
            print(f"❌ 项目创建失败: {e}")
            return False
    
    def _get_sample_dsl(self, template: Optional[str] = None) -> str:
        """获取示例DSL代码"""
        if template == 'ecommerce':
            return """model ECommerceSystem: data_model {
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
}"""
        elif template == 'banking':
            return """model BankingSystem: data_model {
    entity Account {
        id: string;
        balance: number;
        type: string;
    }

    entity Transaction {
        id: string;
        amount: number;
        type: string;
    }

    operation createAccount(type: string) -> Account;
    operation transfer(from: string, to: string, amount: number) -> Transaction;
}"""
        else:
            return """model SampleSystem: data_model {
    entity Entity {
        id: string;
        name: string;
    }

    operation createEntity(name: string) -> Entity;
}"""
    
    def show_info(self) -> None:
        """显示工具信息"""
        info = {
            'name': 'Formal Model CLI',
            'version': '1.0.0',
            'description': 'Formal Model框架命令行工具',
            'features': [
                'DSL编译',
                '语法验证',
                '文档生成',
                '项目创建',
                '模板管理'
            ]
        }
        
        print("📊 工具信息:")
        for key, value in info.items():
            if isinstance(value, list):
                print(f"  {key}:")
                for item in value:
                    print(f"    - {item}")
            else:
                print(f"  {key}: {value}")


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='Formal Model 命令行工具',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例用法:
  formal-model compile model.dsl                    # 编译DSL文件
  formal-model validate model.dsl                   # 验证语法
  formal-model docs model.dsl                       # 生成文档
  formal-model create myproject                     # 创建新项目
  formal-model create myproject --template ecommerce # 使用模板创建项目
  formal-model templates                            # 列出模板
  formal-model info                                 # 显示工具信息
        """
    )
    
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # 编译命令
    compile_parser = subparsers.add_parser('compile', help='编译DSL文件')
    compile_parser.add_argument('source', help='源文件路径')
    compile_parser.add_argument('-o', '--output', help='输出目录')
    compile_parser.add_argument('-t', '--targets', nargs='+', 
                               choices=['java', 'python'], help='目标语言')
    
    # 验证命令
    validate_parser = subparsers.add_parser('validate', help='验证DSL语法')
    validate_parser.add_argument('source', help='源文件路径')
    
    # 文档命令
    docs_parser = subparsers.add_parser('docs', help='生成文档')
    docs_parser.add_argument('source', help='源文件路径')
    docs_parser.add_argument('-o', '--output', help='输出文件')
    
    # 创建项目命令
    create_parser = subparsers.add_parser('create', help='创建新项目')
    create_parser.add_argument('name', help='项目名称')
    create_parser.add_argument('--template', help='使用模板')
    
    # 模板命令
    subparsers.add_parser('templates', help='列出可用模板')
    
    # 信息命令
    subparsers.add_parser('info', help='显示工具信息')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return
    
    cli = FormalModelCLI()
    
    if args.command == 'compile':
        success = cli.compile(args.source, args.output, args.targets)
        sys.exit(0 if success else 1)
    
    elif args.command == 'validate':
        success = cli.validate(args.source)
        sys.exit(0 if success else 1)
    
    elif args.command == 'docs':
        success = cli.generate_docs(args.source, args.output)
        sys.exit(0 if success else 1)
    
    elif args.command == 'create':
        success = cli.create_project(args.name, args.template)
        sys.exit(0 if success else 1)
    
    elif args.command == 'templates':
        cli.list_templates()
    
    elif args.command == 'info':
        cli.show_info()


if __name__ == '__main__':
    main()
