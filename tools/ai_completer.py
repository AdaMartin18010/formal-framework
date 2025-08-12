#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework AI辅助补全工具

基于AI自动补全理论内容，生成相关案例和最佳实践
"""

import os
import yaml
import json
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime
import argparse
import openai
from openai import OpenAI


@dataclass
class CompletionRequest:
    """补全请求"""
    file_path: str
    content: str
    missing_sections: List[str]
    context: Dict
    target_language: str = "zh-CN"


@dataclass
class CompletionResult:
    """补全结果"""
    file_path: str
    original_content: str
    completed_content: str
    added_sections: List[str]
    suggestions: List[str]
    quality_score: float


class AICompleter:
    """AI辅助补全器"""
    
    def __init__(self, config_path: str = "config/automation_config.yaml"):
        """初始化AI补全器"""
        self.config = self._load_config(config_path)
        self.client = None
        self._init_ai_client()
        
    def _load_config(self, config_path: str) -> Dict:
        """加载配置文件"""
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        except FileNotFoundError:
            print(f"警告: 配置文件 {config_path} 不存在，使用默认配置")
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict:
        """获取默认配置"""
        return {
            'ai_completer': {
                'model': 'gpt-4',
                'max_tokens': 2000,
                'temperature': 0.7,
                'enabled': False
            },
            'completion_templates': {
                'theory': {
                    'sections': ['概念定义', '理论基础', '应用案例', '最佳实践'],
                    'prompt_template': '请为以下理论文档补全缺失的章节：{missing_sections}'
                },
                'dsl': {
                    'sections': ['语法定义', '语义规则', '示例代码', '最佳实践'],
                    'prompt_template': '请为以下DSL文档补全缺失的章节：{missing_sections}'
                }
            }
        }
    
    def _init_ai_client(self):
        """初始化AI客户端"""
        if not self.config['ai_completer']['enabled']:
            print("AI功能已禁用，请在配置文件中启用")
            return
        
        api_key = os.getenv('OPENAI_API_KEY')
        if not api_key:
            print("警告: 未设置OPENAI_API_KEY环境变量")
            return
        
        try:
            self.client = OpenAI(api_key=api_key)
            print("AI客户端初始化成功")
        except Exception as e:
            print(f"AI客户端初始化失败: {e}")
    
    def complete_file(self, file_path: str, target_sections: List[str] = None) -> Optional[CompletionResult]:
        """补全单个文件"""
        if not self.client:
            print("AI客户端未初始化，无法进行补全")
            return None
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"读取文件失败 {file_path}: {e}")
            return None
        
        # 分析现有内容
        existing_sections = self._extract_sections(content)
        
        # 确定需要补全的章节
        if target_sections is None:
            target_sections = self._get_required_sections(file_path)
        
        missing_sections = [s for s in target_sections if s not in existing_sections]
        
        if not missing_sections:
            print(f"文件 {file_path} 已包含所有必需章节")
            return None
        
        # 创建补全请求
        request = CompletionRequest(
            file_path=file_path,
            content=content,
            missing_sections=missing_sections,
            context=self._extract_context(file_path, content)
        )
        
        # 执行AI补全
        try:
            completed_content = self._ai_complete(request)
            if completed_content:
                return CompletionResult(
                    file_path=file_path,
                    original_content=content,
                    completed_content=completed_content,
                    added_sections=missing_sections,
                    suggestions=self._generate_suggestions(request, completed_content),
                    quality_score=self._calculate_completion_quality(content, completed_content)
                )
        except Exception as e:
            print(f"AI补全失败 {file_path}: {e}")
        
        return None
    
    def _extract_sections(self, content: str) -> List[str]:
        """提取文档章节"""
        sections = []
        lines = content.split('\n')
        
        for line in lines:
            if line.strip().startswith('#'):
                title = line.strip().lstrip('#').strip()
                if title:
                    sections.append(title)
        
        return sections
    
    def _get_required_sections(self, file_path: str) -> List[str]:
        """获取文件类型对应的必需章节"""
        if 'theory.md' in file_path:
            return self.config['completion_templates']['theory']['sections']
        elif 'dsl-draft.md' in file_path:
            return self.config['completion_templates']['dsl']['sections']
        else:
            return ['概念定义', '理论基础', '应用案例', '最佳实践']
    
    def _extract_context(self, file_path: str, content: str) -> Dict:
        """提取文件上下文信息"""
        context = {
            'file_type': 'theory' if 'theory.md' in file_path else 'dsl',
            'domain': self._extract_domain(file_path),
            'existing_sections': self._extract_sections(content),
            'content_length': len(content),
            'has_code_blocks': bool(re.search(r'```[\w]*\n', content)),
            'has_links': bool(re.search(r'\[([^\]]+)\]\(([^)]+)\)', content))
        }
        return context
    
    def _extract_domain(self, file_path: str) -> str:
        """提取文件所属领域"""
        path_parts = Path(file_path).parts
        
        # 从路径中提取领域信息
        if 'formal-model' in path_parts:
            for part in path_parts:
                if part in ['interaction-model', 'data-model', 'functional-model', 
                           'runtime-model', 'deployment-model', 'monitoring-model']:
                    return part.replace('-', ' ')
        elif 'industry-model' in path_parts:
            for part in path_parts:
                if part.endswith('-architecture') or part.endswith('-model'):
                    return part.replace('-', ' ')
        
        return '通用'
    
    def _ai_complete(self, request: CompletionRequest) -> Optional[str]:
        """使用AI补全内容"""
        if not self.client:
            return None
        
        # 构建提示词
        prompt = self._build_completion_prompt(request)
        
        try:
            response = self.client.chat.completions.create(
                model=self.config['ai_completer']['model'],
                messages=[
                    {
                        "role": "system",
                        "content": "你是一个专业的软件工程文档编写助手，专门负责补全形式化建模相关的理论文档和DSL文档。请根据现有内容，补全缺失的章节，确保内容准确、完整、符合学术标准。"
                    },
                    {
                        "role": "user",
                        "content": prompt
                    }
                ],
                max_tokens=self.config['ai_completer']['max_tokens'],
                temperature=self.config['ai_completer']['temperature']
            )
            
            completed_content = response.choices[0].message.content
            
            # 将补全内容合并到原文档
            return self._merge_completion(request.content, completed_content, request.missing_sections)
            
        except Exception as e:
            print(f"AI API调用失败: {e}")
            return None
    
    def _build_completion_prompt(self, request: CompletionRequest) -> str:
        """构建补全提示词"""
        domain = request.context['domain']
        missing_sections = request.missing_sections
        
        prompt = f"""
请为以下{domain}领域的文档补全缺失的章节。

**现有内容：**
```
{request.content}
```

**需要补全的章节：**
{', '.join(missing_sections)}

**要求：**
1. 保持与现有内容风格一致
2. 使用中文编写
3. 内容要准确、完整、符合学术标准
4. 包含具体的代码示例和最佳实践
5. 添加相关的内部链接和外部参考

**补全格式：**
请直接返回补全后的完整文档内容，包括原有内容和新增内容。
"""
        return prompt
    
    def _merge_completion(self, original_content: str, completion_content: str, added_sections: List[str]) -> str:
        """合并补全内容到原文档"""
        # 简单的合并策略：在文档末尾添加新内容
        merged_content = original_content.rstrip() + "\n\n"
        
        # 添加补全的内容
        merged_content += completion_content
        
        return merged_content
    
    def _generate_suggestions(self, request: CompletionRequest, completed_content: str) -> List[str]:
        """生成改进建议"""
        suggestions = []
        
        # 基于补全结果生成建议
        if len(completed_content) - len(request.content) < 1000:
            suggestions.append("建议增加更多详细的技术说明和示例")
        
        if not re.search(r'```[\w]*\n', completed_content):
            suggestions.append("建议添加代码示例来提高实用性")
        
        if not re.search(r'\[([^\]]+)\]\(([^)]+)\)', completed_content):
            suggestions.append("建议添加相关链接增强文档关联性")
        
        return suggestions
    
    def _calculate_completion_quality(self, original_content: str, completed_content: str) -> float:
        """计算补全质量分数"""
        # 简单的质量评估
        original_length = len(original_content)
        completed_length = len(completed_content)
        
        # 内容增长比例
        growth_ratio = (completed_length - original_length) / original_length if original_length > 0 else 0
        
        # 基础分数
        base_score = 0.5
        
        # 根据内容增长调整分数
        if growth_ratio > 0.5:
            base_score += 0.3
        elif growth_ratio > 0.2:
            base_score += 0.2
        else:
            base_score += 0.1
        
        # 检查是否有代码示例
        if re.search(r'```[\w]*\n', completed_content):
            base_score += 0.1
        
        # 检查是否有链接
        if re.search(r'\[([^\]]+)\]\(([^)]+)\)', completed_content):
            base_score += 0.1
        
        return min(base_score, 1.0)
    
    def batch_complete(self, file_patterns: List[str] = None, output_dir: str = None) -> List[CompletionResult]:
        """批量补全文件"""
        if not self.client:
            print("AI客户端未初始化，无法进行批量补全")
            return []
        
        # 获取需要补全的文件
        if file_patterns is None:
            file_patterns = ['**/theory.md', '**/dsl-draft.md']
        
        files_to_complete = []
        for pattern in file_patterns:
            for file_path in Path('.').rglob(pattern):
                if file_path.is_file():
                    files_to_complete.append(str(file_path))
        
        print(f"找到 {len(files_to_complete)} 个文件需要补全")
        
        results = []
        for i, file_path in enumerate(files_to_complete, 1):
            print(f"正在处理 ({i}/{len(files_to_complete)}): {file_path}")
            
            result = self.complete_file(file_path)
            if result:
                results.append(result)
                
                # 保存补全结果
                if output_dir:
                    self._save_completion_result(result, output_dir)
        
        return results
    
    def _save_completion_result(self, result: CompletionResult, output_dir: str):
        """保存补全结果"""
        output_path = Path(output_dir) / Path(result.file_path).name
        
        # 确保输出目录存在
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        # 保存补全后的内容
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(result.completed_content)
        
        # 保存补全报告
        report_path = output_path.with_suffix('.completion_report.json')
        report = {
            'file_path': result.file_path,
            'added_sections': result.added_sections,
            'suggestions': result.suggestions,
            'quality_score': result.quality_score,
            'completion_time': datetime.now().isoformat()
        }
        
        with open(report_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
    
    def generate_completion_report(self, results: List[CompletionResult], output_path: str = None) -> str:
        """生成补全报告"""
        if output_path is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_path = f"reports/ai_completion_report_{timestamp}.md"
        
        report_content = f"""# AI辅助补全报告

**生成时间**: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}
**补全文件数**: {len(results)}

## 补全概览

- **成功补全**: {len(results)} 个文件
- **平均质量分数**: {sum(r.quality_score for r in results) / len(results) if results else 0:.2f}

## 补全详情

"""
        
        for result in results:
            report_content += f"""### {result.file_path}

- **质量分数**: {result.quality_score:.2f}
- **新增章节**: {', '.join(result.added_sections)}
- **建议**:
"""
            for suggestion in result.suggestions:
                report_content += f"  - {suggestion}\n"
            report_content += "\n"
        
        # 保存报告
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report_content)
        
        print(f"补全报告已保存到: {output_path}")
        return output_path


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Formal Framework AI辅助补全工具')
    parser.add_argument('--config', default='config/automation_config.yaml', help='配置文件路径')
    parser.add_argument('--file', help='单个文件路径')
    parser.add_argument('--pattern', nargs='+', help='文件模式列表')
    parser.add_argument('--output-dir', help='输出目录')
    parser.add_argument('--report', help='报告输出路径')
    
    args = parser.parse_args()
    
    # 创建AI补全器
    completer = AICompleter(args.config)
    
    if args.file:
        # 补全单个文件
        result = completer.complete_file(args.file)
        if result:
            print(f"文件 {args.file} 补全成功")
            if args.output_dir:
                completer._save_completion_result(result, args.output_dir)
        else:
            print(f"文件 {args.file} 补全失败或无需补全")
    else:
        # 批量补全
        results = completer.batch_complete(args.pattern, args.output_dir)
        
        if results:
            # 生成报告
            report_path = completer.generate_completion_report(results, args.report)
            print(f"批量补全完成，共处理 {len(results)} 个文件")
            print(f"报告已保存到: {report_path}")
        else:
            print("没有文件需要补全或补全失败")


if __name__ == "__main__":
    main() 