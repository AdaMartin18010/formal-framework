#!/usr/bin/env python3
"""
Formal Model CLI Tool
Formal Model框架命令行工具
"""

import argparse
import sys
import os
import json
import yaml
from pathlib import Path
from typing import Dict, List, Optional, Any
from simple_compiler import SimpleCompiler

class FormalModelCLI:
    """Formal Model命令行工具"""
    
    def __init__(self):
        self.compiler = SimpleCompiler()
        
    def compile_dsl(self, input_file: str, output_dir: str, target_language: str = "java") -> bool:
        """编译DSL文件"""
        try:
            # 读取DSL文件
            with open(input_file, 'r', encoding='utf-8') as f:
                dsl_content = f.read()
            
            # 编译
            result = self.compiler.compile(dsl_content)
            
            if not result['success']:
                print(f"❌ 编译失败: {input_file}")
                for error in result['errors']:
                    print(f"  - {error}")
                return False
            
            # 创建输出目录
            os.makedirs(output_dir, exist_ok=True)
            
            # 保存生成的文件
            for filename, code in result['generated_code'].items():
                filepath = os.path.join(output_dir, filename)
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(code)
                print(f"💾 生成: {filepath}")
            
            print(f"✅ 编译成功: {input_file}")
            return True
            
        except Exception as e:
            print(f"❌ 编译错误: {e}")
            return False
    
    def validate_model(self, model_file: str) -> bool:
        """验证模型文件"""
        try:
            # 读取模型文件
            with open(model_file, 'r', encoding='utf-8') as f:
                if model_file.endswith('.json'):
                    model_data = json.load(f)
                elif model_file.endswith('.yaml') or model_file.endswith('.yml'):
                    model_data = yaml.safe_load(f)
                else:
                    print(f"❌ 不支持的文件格式: {model_file}")
                    return False
            
            # 基本验证
            required_fields = ['name', 'type', 'entities']
            for field in required_fields:
                if field not in model_data:
                    print(f"❌ 缺少必需字段: {field}")
                    return False
            
            # 实体验证
            for entity in model_data.get('entities', []):
                if 'name' not in entity:
                    print(f"❌ 实体缺少name字段")
                    return False
                
                for attr in entity.get('attributes', []):
                    if 'name' not in attr or 'type' not in attr:
                        print(f"❌ 属性缺少name或type字段")
                        return False
            
            print(f"✅ 模型验证通过: {model_file}")
            return True
            
        except Exception as e:
            print(f"❌ 验证错误: {e}")
            return False
    
    def generate_docs(self, model_file: str, output_file: str) -> bool:
        """生成文档"""
        try:
            # 读取模型文件
            with open(model_file, 'r', encoding='utf-8') as f:
                if model_file.endswith('.json'):
                    model_data = json.load(f)
                elif model_file.endswith('.yaml') or model_file.endswith('.yml'):
                    model_data = yaml.safe_load(f)
                else:
                    print(f"❌ 不支持的文件格式: {model_file}")
                    return False
            
            # 生成Markdown文档
            doc_content = self._generate_markdown_doc(model_data)
            
            # 保存文档
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(doc_content)
            
            print(f"📄 文档生成成功: {output_file}")
            return True
            
        except Exception as e:
            print(f"❌ 文档生成错误: {e}")
            return False
    
    def _generate_markdown_doc(self, model_data: Dict) -> str:
        """生成Markdown文档"""
        lines = []
        
        # 标题
        lines.append(f"# {model_data['name']} 模型文档")
        lines.append("")
        lines.append(f"**模型类型**: {model_data['type']}")
        lines.append("")
        
        # 实体
        lines.append("## 实体定义")
        lines.append("")
        
        for entity in model_data.get('entities', []):
            lines.append(f"### {entity['name']}")
            lines.append("")
            
            if 'description' in entity:
                lines.append(f"{entity['description']}")
                lines.append("")
            
            lines.append("#### 属性")
            lines.append("")
            lines.append("| 属性名 | 类型 | 描述 |")
            lines.append("|--------|------|------|")
            
            for attr in entity.get('attributes', []):
                desc = attr.get('description', '')
                lines.append(f"| {attr['name']} | {attr['type']} | {desc} |")
            
            lines.append("")
        
        # 操作
        if 'operations' in model_data:
            lines.append("## 操作定义")
            lines.append("")
            
            for operation in model_data['operations']:
                lines.append(f"### {operation['name']}")
                lines.append("")
                
                if 'description' in operation:
                    lines.append(f"{operation['description']}")
                    lines.append("")
                
                # 参数
                if operation.get('parameters'):
                    lines.append("#### 参数")
                    lines.append("")
                    lines.append("| 参数名 | 类型 | 描述 |")
                    lines.append("|--------|------|------|")
                    
                    for param in operation['parameters']:
                        desc = param.get('description', '')
                        lines.append(f"| {param['name']} | {param['type']} | {desc} |")
                    
                    lines.append("")
                
                # 返回值
                if 'return_type' in operation:
                    lines.append(f"#### 返回值")
                    lines.append("")
                    lines.append(f"类型: `{operation['return_type']}`")
                    lines.append("")
        
        return '\n'.join(lines)
    
    def list_templates(self) -> None:
        """列出可用模板"""
        templates = {
            'ecommerce': '电子商务系统模型',
            'user_management': '用户管理系统模型',
            'inventory': '库存管理系统模型',
            'order_processing': '订单处理系统模型'
        }
        
        print("📋 可用模板:")
        for name, desc in templates.items():
            print(f"  - {name}: {desc}")
    
    def create_template(self, template_name: str, output_file: str) -> bool:
        """创建模板文件"""
        templates = {
            'ecommerce': {
                'name': 'ECommerceSystem',
                'type': 'business_model',
                'description': '电子商务系统模型',
                'entities': [
                    {
                        'name': 'User',
                        'description': '用户实体',
                        'attributes': [
                            {'name': 'id', 'type': 'string', 'description': '用户ID'},
                            {'name': 'name', 'type': 'string', 'description': '用户姓名'},
                            {'name': 'email', 'type': 'string', 'description': '邮箱地址'},
                            {'name': 'phone', 'type': 'string', 'description': '电话号码'}
                        ]
                    },
                    {
                        'name': 'Product',
                        'description': '商品实体',
                        'attributes': [
                            {'name': 'id', 'type': 'string', 'description': '商品ID'},
                            {'name': 'name', 'type': 'string', 'description': '商品名称'},
                            {'name': 'price', 'type': 'number', 'description': '商品价格'},
                            {'name': 'category', 'type': 'string', 'description': '商品分类'}
                        ]
                    },
                    {
                        'name': 'Order',
                        'description': '订单实体',
                        'attributes': [
                            {'name': 'id', 'type': 'string', 'description': '订单ID'},
                            {'name': 'user_id', 'type': 'string', 'description': '用户ID'},
                            {'name': 'total_amount', 'type': 'number', 'description': '订单总金额'},
                            {'name': 'status', 'type': 'string', 'description': '订单状态'}
                        ]
                    }
                ],
                'operations': [
                    {
                        'name': 'createUser',
                        'description': '创建用户',
                        'parameters': [
                            {'name': 'name', 'type': 'string', 'description': '用户姓名'},
                            {'name': 'email', 'type': 'string', 'description': '邮箱地址'}
                        ],
                        'return_type': 'User'
                    },
                    {
                        'name': 'createProduct',
                        'description': '创建商品',
                        'parameters': [
                            {'name': 'name', 'type': 'string', 'description': '商品名称'},
                            {'name': 'price', 'type': 'number', 'description': '商品价格'}
                        ],
                        'return_type': 'Product'
                    }
                ]
            }
        }
        
        if template_name not in templates:
            print(f"❌ 模板不存在: {template_name}")
            return False
        
        try:
            # 保存为JSON格式
            with open(output_file, 'w', encoding='utf-8') as f:
                json.dump(templates[template_name], f, indent=2, ensure_ascii=False)
            
            print(f"📄 模板创建成功: {output_file}")
            return True
            
        except Exception as e:
            print(f"❌ 模板创建错误: {e}")
            return False

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Formal Model CLI Tool')
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # 编译命令
    compile_parser = subparsers.add_parser('compile', help='编译DSL文件')
    compile_parser.add_argument('input', help='输入DSL文件')
    compile_parser.add_argument('-o', '--output', default='generated', help='输出目录')
    compile_parser.add_argument('-t', '--target', choices=['java', 'python'], default='java', help='目标语言')
    
    # 验证命令
    validate_parser = subparsers.add_parser('validate', help='验证模型文件')
    validate_parser.add_argument('model', help='模型文件')
    
    # 文档生成命令
    doc_parser = subparsers.add_parser('docs', help='生成文档')
    doc_parser.add_argument('model', help='模型文件')
    doc_parser.add_argument('-o', '--output', help='输出文档文件')
    
    # 模板命令
    template_parser = subparsers.add_parser('template', help='模板管理')
    template_subparsers = template_parser.add_subparsers(dest='template_command', help='模板命令')
    
    list_parser = template_subparsers.add_parser('list', help='列出可用模板')
    
    create_parser = template_subparsers.add_parser('create', help='创建模板文件')
    create_parser.add_argument('name', help='模板名称')
    create_parser.add_argument('-o', '--output', help='输出文件')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return
    
    cli = FormalModelCLI()
    
    if args.command == 'compile':
        success = cli.compile_dsl(args.input, args.output, args.target)
        sys.exit(0 if success else 1)
    
    elif args.command == 'validate':
        success = cli.validate_model(args.model)
        sys.exit(0 if success else 1)
    
    elif args.command == 'docs':
        output_file = args.output or f"{Path(args.model).stem}_docs.md"
        success = cli.generate_docs(args.model, output_file)
        sys.exit(0 if success else 1)
    
    elif args.command == 'template':
        if args.template_command == 'list':
            cli.list_templates()
        elif args.template_command == 'create':
            output_file = args.output or f"{args.name}_template.json"
            success = cli.create_template(args.name, output_file)
            sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()
