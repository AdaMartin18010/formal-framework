#!/usr/bin/env python3
"""
文档质量检查器 - 检查文档的质量指标
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple
import argparse
import statistics
from datetime import datetime

class DocumentQualityChecker:
    def __init__(self, root_dir: str = "docs"):
        self.root_dir = Path(root_dir)
        self.quality_metrics = {}
        
    def find_markdown_files(self) -> List[Path]:
        """查找所有Markdown文件"""
        markdown_files = []
        for file_path in self.root_dir.rglob("*.md"):
            if file_path.is_file():
                markdown_files.append(file_path)
        return markdown_files
    
    def check_document_structure(self, file_path: Path) -> Dict:
        """检查文档结构"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {'error': str(e)}
        
        structure_metrics = {
            'has_title': bool(re.search(r'^#\s+.+', content, re.MULTILINE)),
            'has_toc': '## 目录' in content or '## Table of Contents' in content,
            'has_overview': '## 概述' in content or '## Overview' in content,
            'has_conclusion': '## 总结' in content or '## 结论' in content or '## Conclusion' in content,
            'has_references': '## 参考文献' in content or '## References' in content,
            'title_count': len(re.findall(r'^#+\s+', content, re.MULTILINE)),
            'section_count': len(re.findall(r'^##\s+', content, re.MULTILINE)),
            'subsection_count': len(re.findall(r'^###\s+', content, re.MULTILINE))
        }
        
        return structure_metrics
    
    def check_content_quality(self, file_path: Path) -> Dict:
        """检查内容质量"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {'error': str(e)}
        
        # 基本统计
        lines = content.split('\n')
        words = content.split()
        
        content_metrics = {
            'line_count': len(lines),
            'word_count': len(words),
            'char_count': len(content),
            'non_empty_lines': len([line for line in lines if line.strip()]),
            'code_blocks': len(re.findall(r'```', content)) // 2,
            'links': len(re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)),
            'images': len(re.findall(r'!\[([^\]]*)\]\(([^)]+)\)', content)),
            'tables': len(re.findall(r'\|.*\|', content)),
            'lists': len(re.findall(r'^[\s]*[-*+]\s+', content, re.MULTILINE))
        }
        
        # 内容质量指标
        content_metrics.update({
            'avg_words_per_line': content_metrics['word_count'] / max(content_metrics['line_count'], 1),
            'code_block_ratio': content_metrics['code_blocks'] / max(content_metrics['line_count'], 1),
            'link_density': content_metrics['links'] / max(content_metrics['word_count'], 1),
            'structure_ratio': (content_metrics['tables'] + content_metrics['lists']) / max(content_metrics['line_count'], 1)
        })
        
        return content_metrics
    
    def check_format_consistency(self, file_path: Path) -> Dict:
        """检查格式一致性"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {'error': str(e)}
        
        format_metrics = {
            'consistent_heading_style': self._check_heading_consistency(content),
            'consistent_list_style': self._check_list_consistency(content),
            'consistent_code_style': self._check_code_consistency(content),
            'consistent_link_style': self._check_link_consistency(content),
            'has_proper_spacing': self._check_spacing(content),
            'has_proper_indentation': self._check_indentation(content)
        }
        
        return format_metrics
    
    def _check_heading_consistency(self, content: str) -> bool:
        """检查标题一致性"""
        headings = re.findall(r'^(#+)\s+(.+)', content, re.MULTILINE)
        if not headings:
            return True
        
        # 检查标题层级是否连续
        levels = [len(h[0]) for h in headings]
        for i in range(1, len(levels)):
            if levels[i] > levels[i-1] + 1:
                return False
        
        return True
    
    def _check_list_consistency(self, content: str) -> bool:
        """检查列表一致性"""
        list_items = re.findall(r'^[\s]*([-*+])\s+', content, re.MULTILINE)
        if not list_items:
            return True
        
        # 检查是否使用统一的列表标记
        unique_markers = set(list_items)
        return len(unique_markers) == 1
    
    def _check_code_consistency(self, content: str) -> bool:
        """检查代码块一致性"""
        code_blocks = re.findall(r'```(\w+)?', content)
        if not code_blocks:
            return True
        
        # 检查代码块是否有语言标识
        has_language = any(block.strip() for block in code_blocks)
        return has_language
    
    def _check_link_consistency(self, content: str) -> bool:
        """检查链接一致性"""
        links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        if not links:
            return True
        
        # 检查链接格式是否一致
        for link_text, link_url in links:
            if not link_text.strip() or not link_url.strip():
                return False
        
        return True
    
    def _check_spacing(self, content: str) -> bool:
        """检查间距"""
        lines = content.split('\n')
        
        # 检查是否有过多的空行
        empty_line_count = 0
        for line in lines:
            if not line.strip():
                empty_line_count += 1
            else:
                empty_line_count = 0
            
            if empty_line_count > 2:
                return False
        
        return True
    
    def _check_indentation(self, content: str) -> bool:
        """检查缩进"""
        lines = content.split('\n')
        
        for line in lines:
            if line.strip():
                # 检查是否使用一致的缩进（空格或制表符）
                leading_spaces = len(line) - len(line.lstrip(' '))
                leading_tabs = len(line) - len(line.lstrip('\t'))
                
                if leading_spaces > 0 and leading_tabs > 0:
                    return False
        
        return True
    
    def check_readability(self, file_path: Path) -> Dict:
        """检查可读性"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {'error': str(e)}
        
        # 移除代码块和链接
        clean_content = re.sub(r'```.*?```', '', content, flags=re.DOTALL)
        clean_content = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', clean_content)
        
        sentences = re.split(r'[.!?]+', clean_content)
        words = clean_content.split()
        
        readability_metrics = {
            'sentence_count': len([s for s in sentences if s.strip()]),
            'avg_words_per_sentence': len(words) / max(len([s for s in sentences if s.strip()]), 1),
            'avg_chars_per_word': sum(len(word) for word in words) / max(len(words), 1),
            'long_sentences': len([s for s in sentences if len(s.split()) > 20]),
            'short_sentences': len([s for s in sentences if len(s.split()) < 5])
        }
        
        return readability_metrics
    
    def calculate_quality_score(self, metrics: Dict) -> float:
        """计算质量评分"""
        if 'error' in metrics:
            return 0.0
        
        score = 0.0
        max_score = 100.0
        
        # 结构完整性 (30分)
        structure_score = 0
        if metrics.get('has_title', False):
            structure_score += 5
        if metrics.get('has_toc', False):
            structure_score += 10
        if metrics.get('has_overview', False):
            structure_score += 5
        if metrics.get('has_conclusion', False):
            structure_score += 5
        if metrics.get('has_references', False):
            structure_score += 5
        
        score += structure_score * 0.3
        
        # 内容质量 (40分)
        content_score = 0
        word_count = metrics.get('word_count', 0)
        if 500 <= word_count <= 10000:
            content_score += 10
        elif word_count > 100:
            content_score += 5
        
        if metrics.get('code_blocks', 0) > 0:
            content_score += 5
        
        if metrics.get('links', 0) >= 3:
            content_score += 10
        
        if metrics.get('tables', 0) > 0 or metrics.get('lists', 0) > 0:
            content_score += 5
        
        if metrics.get('images', 0) > 0:
            content_score += 5
        
        # 可读性评分
        avg_words_per_sentence = metrics.get('avg_words_per_sentence', 0)
        if 10 <= avg_words_per_sentence <= 20:
            content_score += 5
        
        score += content_score * 0.4
        
        # 格式一致性 (30分)
        format_score = 0
        if metrics.get('consistent_heading_style', False):
            format_score += 10
        if metrics.get('consistent_list_style', False):
            format_score += 5
        if metrics.get('consistent_code_style', False):
            format_score += 5
        if metrics.get('consistent_link_style', False):
            format_score += 5
        if metrics.get('has_proper_spacing', False):
            format_score += 3
        if metrics.get('has_proper_indentation', False):
            format_score += 2
        
        score += format_score * 0.3
        
        return min(score, max_score)
    
    def check_document_quality(self, file_path: Path) -> Dict:
        """检查单个文档的质量"""
        print(f"📄 检查文档: {file_path.name}")
        
        # 检查各个维度
        structure_metrics = self.check_document_structure(file_path)
        content_metrics = self.check_content_quality(file_path)
        format_metrics = self.check_format_consistency(file_path)
        readability_metrics = self.check_readability(file_path)
        
        # 合并所有指标
        all_metrics = {
            **structure_metrics,
            **content_metrics,
            **format_metrics,
            **readability_metrics
        }
        
        # 计算质量评分
        quality_score = self.calculate_quality_score(all_metrics)
        all_metrics['quality_score'] = quality_score
        
        return all_metrics
    
    def check_all_documents(self) -> Dict:
        """检查所有文档的质量"""
        print("🔍 开始检查所有文档的质量...")
        
        markdown_files = self.find_markdown_files()
        print(f"📁 找到 {len(markdown_files)} 个Markdown文件")
        
        all_results = {
            'total_files': len(markdown_files),
            'file_results': [],
            'overall_metrics': {},
            'quality_distribution': {}
        }
        
        quality_scores = []
        
        # 逐个检查文档
        for i, file_path in enumerate(markdown_files, 1):
            print(f"📄 处理文件 {i}/{len(markdown_files)}: {file_path.name}")
            
            try:
                result = self.check_document_quality(file_path)
                result['file_path'] = str(file_path)
                all_results['file_results'].append(result)
                
                if 'quality_score' in result:
                    quality_scores.append(result['quality_score'])
                
            except Exception as e:
                print(f"❌ 处理 {file_path} 时出错: {e}")
                all_results['file_results'].append({
                    'file_path': str(file_path),
                    'error': str(e),
                    'quality_score': 0.0
                })
        
        # 计算总体指标
        if quality_scores:
            all_results['overall_metrics'] = {
                'avg_quality_score': statistics.mean(quality_scores),
                'median_quality_score': statistics.median(quality_scores),
                'min_quality_score': min(quality_scores),
                'max_quality_score': max(quality_scores),
                'std_quality_score': statistics.stdev(quality_scores) if len(quality_scores) > 1 else 0
            }
            
            # 质量分布
            excellent = len([s for s in quality_scores if s >= 90])
            good = len([s for s in quality_scores if 80 <= s < 90])
            fair = len([s for s in quality_scores if 70 <= s < 80])
            poor = len([s for s in quality_scores if s < 70])
            
            all_results['quality_distribution'] = {
                'excellent': excellent,
                'good': good,
                'fair': fair,
                'poor': poor
            }
        
        return all_results
    
    def generate_report(self, results: Dict) -> str:
        """生成质量检查报告"""
        report = []
        report.append("# 📊 文档质量检查报告")
        report.append("")
        report.append(f"**检查时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("")
        
        # 总体统计
        report.append("## 📈 总体统计")
        report.append("")
        report.append(f"- **总文件数**: {results['total_files']}")
        
        if 'overall_metrics' in results and results['overall_metrics']:
            metrics = results['overall_metrics']
            report.append(f"- **平均质量评分**: {metrics['avg_quality_score']:.1f}")
            report.append(f"- **中位数质量评分**: {metrics['median_quality_score']:.1f}")
            report.append(f"- **最低质量评分**: {metrics['min_quality_score']:.1f}")
            report.append(f"- **最高质量评分**: {metrics['max_quality_score']:.1f}")
            report.append(f"- **质量评分标准差**: {metrics['std_quality_score']:.1f}")
        
        if 'quality_distribution' in results and results['quality_distribution']:
            dist = results['quality_distribution']
            total = sum(dist.values())
            report.append("")
            report.append("### 质量分布")
            report.append("")
            report.append(f"- **优秀 (90-100分)**: {dist['excellent']} 个文件 ({dist['excellent']/total*100:.1f}%)")
            report.append(f"- **良好 (80-89分)**: {dist['good']} 个文件 ({dist['good']/total*100:.1f}%)")
            report.append(f"- **一般 (70-79分)**: {dist['fair']} 个文件 ({dist['fair']/total*100:.1f}%)")
            report.append(f"- **较差 (<70分)**: {dist['poor']} 个文件 ({dist['poor']/total*100:.1f}%)")
        
        report.append("")
        
        # 详细结果
        report.append("## 📋 详细结果")
        report.append("")
        
        # 按质量评分排序
        file_results = [r for r in results['file_results'] if 'quality_score' in r]
        file_results.sort(key=lambda x: x.get('quality_score', 0), reverse=True)
        
        # 显示前10个和后10个
        report.append("### 🏆 质量评分最高的10个文档")
        report.append("")
        for i, result in enumerate(file_results[:10], 1):
            score = result.get('quality_score', 0)
            file_name = Path(result['file_path']).name
            report.append(f"{i}. **{file_name}** - {score:.1f}分")
        report.append("")
        
        report.append("### ⚠️ 质量评分最低的10个文档")
        report.append("")
        for i, result in enumerate(file_results[-10:], 1):
            score = result.get('quality_score', 0)
            file_name = Path(result['file_path']).name
            report.append(f"{len(file_results)-10+i}. **{file_name}** - {score:.1f}分")
        report.append("")
        
        # 需要改进的文档
        poor_quality_files = [r for r in file_results if r.get('quality_score', 0) < 70]
        if poor_quality_files:
            report.append("## 🚨 需要改进的文档")
            report.append("")
            for result in poor_quality_files:
                score = result.get('quality_score', 0)
                file_name = Path(result['file_path']).name
                report.append(f"- **{file_name}** - {score:.1f}分")
                
                # 提供改进建议
                suggestions = self.get_improvement_suggestions(result)
                if suggestions:
                    report.append("  - 改进建议:")
                    for suggestion in suggestions:
                        report.append(f"    - {suggestion}")
                report.append("")
        
        return "\n".join(report)
    
    def get_improvement_suggestions(self, result: Dict) -> List[str]:
        """获取改进建议"""
        suggestions = []
        
        if not result.get('has_title', False):
            suggestions.append("添加文档标题")
        
        if not result.get('has_toc', False):
            suggestions.append("添加目录结构")
        
        if not result.get('has_overview', False):
            suggestions.append("添加概述部分")
        
        if not result.get('has_references', False):
            suggestions.append("添加参考文献")
        
        word_count = result.get('word_count', 0)
        if word_count < 500:
            suggestions.append("增加文档内容，建议至少500字")
        elif word_count > 10000:
            suggestions.append("文档过长，建议拆分为多个文档")
        
        if result.get('links', 0) < 3:
            suggestions.append("增加内部链接和外部引用")
        
        if result.get('code_blocks', 0) == 0:
            suggestions.append("添加代码示例")
        
        if not result.get('consistent_heading_style', False):
            suggestions.append("统一标题格式")
        
        if not result.get('consistent_list_style', False):
            suggestions.append("统一列表格式")
        
        return suggestions
    
    def save_report(self, results: Dict, output_file: str = "document_quality_report.md"):
        """保存质量检查报告"""
        report = self.generate_report(results)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"📄 质量检查报告已保存到: {output_file}")

def main():
    parser = argparse.ArgumentParser(description='检查文档质量')
    parser.add_argument('--root', default='docs', help='文档根目录 (默认: docs)')
    parser.add_argument('--output', default='document_quality_report.md', help='输出报告文件')
    
    args = parser.parse_args()
    
    checker = DocumentQualityChecker(args.root)
    results = checker.check_all_documents()
    checker.save_report(results, args.output)
    
    # 打印简要统计
    print("\n" + "="*50)
    print("📊 质量检查完成统计:")
    print(f"总文件数: {results['total_files']}")
    
    if 'overall_metrics' in results and results['overall_metrics']:
        metrics = results['overall_metrics']
        print(f"平均质量评分: {metrics['avg_quality_score']:.1f}")
        print(f"质量评分范围: {metrics['min_quality_score']:.1f} - {metrics['max_quality_score']:.1f}")
    
    if 'quality_distribution' in results and results['quality_distribution']:
        dist = results['quality_distribution']
        print(f"优秀文档: {dist['excellent']} 个")
        print(f"需要改进: {dist['poor']} 个")
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
