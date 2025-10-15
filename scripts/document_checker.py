#!/usr/bin/env python3
"""
文档完成度检查脚本
用于检查形式化框架项目的文档完成度和质量
"""

import os
import re
import json
import yaml
from pathlib import Path
from typing import Dict, List, Any, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime

@dataclass
class DocumentCheckResult:
    """文档检查结果"""
    file_path: str
    status: str  # DRAFT, RC, FINAL
    completeness: float  # 0-1
    issues: List[str]
    suggestions: List[str]
    word_count: int
    has_references: bool
    has_examples: bool
    has_dsl: bool
    has_theory: bool

class DocumentChecker:
    """文档检查器"""
    
    def __init__(self, docs_root: str = "docs"):
        self.docs_root = Path(docs_root)
        self.results: List[DocumentCheckResult] = []
        
        # 必需章节
        self.required_sections = [
            "概述", "理论基础", "核心结构", "形式化规范",
            "行业应用对齐", "验证框架", "与L2/L4映射"
        ]
        
        # 质量关键词
        self.quality_keywords = {
            "has_references": ["参考文献", "References", "引用", "参考"],
            "has_examples": ["示例", "Example", "案例", "Case"],
            "has_dsl": ["DSL", "dsl", "领域特定语言"],
            "has_theory": ["理论", "Theory", "形式化", "formal"]
        }
        
        # 问题关键词
        self.issue_keywords = [
            "TODO", "FIXME", "占位", "placeholder", "待补充", "待完善",
            "待实现", "待开发", "待添加", "待更新"
        ]

    def check_document(self, file_path: Path) -> DocumentCheckResult:
        """检查单个文档"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return DocumentCheckResult(
                file_path=str(file_path),
                status="ERROR",
                completeness=0.0,
                issues=[f"无法读取文件: {e}"],
                suggestions=["检查文件编码和权限"],
                word_count=0,
                has_references=False,
                has_examples=False,
                has_dsl=False,
                has_theory=False
            )

        # 基本信息
        word_count = len(content.split())
        
        # 检查问题关键词
        issues = []
        for keyword in self.issue_keywords:
            if keyword in content:
                issues.append(f"包含占位符: {keyword}")
        
        # 检查质量指标
        quality_checks = {}
        for check_name, keywords in self.quality_keywords.items():
            quality_checks[check_name] = any(keyword in content for keyword in keywords)
        
        # 检查必需章节
        missing_sections = []
        for section in self.required_sections:
            if section not in content:
                missing_sections.append(section)
        
        # 计算完成度
        completeness = self._calculate_completeness(
            content, missing_sections, quality_checks, issues
        )
        
        # 确定状态
        status = self._determine_status(completeness, issues, missing_sections)
        
        # 生成建议
        suggestions = self._generate_suggestions(
            missing_sections, quality_checks, issues, completeness
        )
        
        return DocumentCheckResult(
            file_path=str(file_path),
            status=status,
            completeness=completeness,
            issues=issues,
            suggestions=suggestions,
            word_count=word_count,
            **quality_checks
        )

    def _calculate_completeness(self, content: str, missing_sections: List[str], 
                              quality_checks: Dict[str, bool], issues: List[str]) -> float:
        """计算文档完成度"""
        score = 0.0
        
        # 基础结构 (40%)
        section_score = (len(self.required_sections) - len(missing_sections)) / len(self.required_sections)
        score += section_score * 0.4
        
        # 质量指标 (30%)
        quality_score = sum(quality_checks.values()) / len(quality_checks)
        score += quality_score * 0.3
        
        # 内容长度 (20%)
        if len(content.split()) > 1000:
            length_score = 1.0
        elif len(content.split()) > 500:
            length_score = 0.7
        elif len(content.split()) > 200:
            length_score = 0.4
        else:
            length_score = 0.1
        score += length_score * 0.2
        
        # 问题扣分 (10%)
        issue_penalty = min(len(issues) * 0.1, 0.1)
        score -= issue_penalty
        
        return max(0.0, min(1.0, score))

    def _determine_status(self, completeness: float, issues: List[str], 
                         missing_sections: List[str]) -> str:
        """确定文档状态"""
        if completeness >= 0.8 and len(issues) == 0 and len(missing_sections) <= 1:
            return "FINAL"
        elif completeness >= 0.6 and len(issues) <= 2:
            return "RC"
        else:
            return "DRAFT"

    def _generate_suggestions(self, missing_sections: List[str], 
                            quality_checks: Dict[str, bool], issues: List[str],
                            completeness: float) -> List[str]:
        """生成改进建议"""
        suggestions = []
        
        if missing_sections:
            suggestions.append(f"补充缺失章节: {', '.join(missing_sections)}")
        
        for check_name, has_feature in quality_checks.items():
            if not has_feature:
                feature_name = {
                    "has_references": "参考文献",
                    "has_examples": "示例案例",
                    "has_dsl": "DSL设计",
                    "has_theory": "理论说明"
                }.get(check_name, check_name)
                suggestions.append(f"补充{feature_name}内容")
        
        if issues:
            suggestions.append("清理占位符和待办事项")
        
        if completeness < 0.6:
            suggestions.append("大幅扩充文档内容")
        elif completeness < 0.8:
            suggestions.append("完善文档结构和内容")
        
        return suggestions

    def check_all_documents(self) -> List[DocumentCheckResult]:
        """检查所有文档"""
        results = []
        
        # 遍历所有markdown文件
        for md_file in self.docs_root.rglob("*.md"):
            if md_file.name.startswith("."):
                continue
                
            result = self.check_document(md_file)
            results.append(result)
        
        self.results = results
        return results

    def generate_report(self, output_file: str = "document_check_report.json"):
        """生成检查报告"""
        if not self.results:
            self.check_all_documents()
        
        # 统计信息
        total_docs = len(self.results)
        status_counts = {}
        completeness_stats = {"min": 1.0, "max": 0.0, "avg": 0.0}
        
        for result in self.results:
            status_counts[result.status] = status_counts.get(result.status, 0) + 1
            completeness_stats["min"] = min(completeness_stats["min"], result.completeness)
            completeness_stats["max"] = max(completeness_stats["max"], result.completeness)
            completeness_stats["avg"] += result.completeness
        
        completeness_stats["avg"] /= total_docs
        
        # 生成报告
        report = {
            "timestamp": datetime.now().isoformat(),
            "summary": {
                "total_documents": total_docs,
                "status_distribution": status_counts,
                "completeness_statistics": completeness_stats
            },
            "documents": [asdict(result) for result in self.results]
        }
        
        # 保存报告
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        
        return report

    def generate_markdown_report(self, output_file: str = "document_check_report.md"):
        """生成Markdown格式报告"""
        if not self.results:
            self.check_all_documents()
        
        # 统计信息
        total_docs = len(self.results)
        status_counts = {}
        completeness_stats = {"min": 1.0, "max": 0.0, "avg": 0.0}
        
        for result in self.results:
            status_counts[result.status] = status_counts.get(result.status, 0) + 1
            completeness_stats["min"] = min(completeness_stats["min"], result.completeness)
            completeness_stats["max"] = max(completeness_stats["max"], result.completeness)
            completeness_stats["avg"] += result.completeness
        
        completeness_stats["avg"] /= total_docs
        
        # 生成Markdown报告
        md_content = f"""# 文档完成度检查报告

## 检查时间
{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 总体统计

- **总文档数**: {total_docs}
- **平均完成度**: {completeness_stats['avg']:.1%}
- **最高完成度**: {completeness_stats['max']:.1%}
- **最低完成度**: {completeness_stats['min']:.1%}

## 状态分布

| 状态 | 数量 | 比例 |
|------|------|------|
"""
        
        for status, count in status_counts.items():
            percentage = count / total_docs * 100
            md_content += f"| {status} | {count} | {percentage:.1f}% |\n"
        
        md_content += "\n## 详细结果\n\n"
        
        # 按状态分组
        for status in ["FINAL", "RC", "DRAFT", "ERROR"]:
            status_docs = [r for r in self.results if r.status == status]
            if not status_docs:
                continue
                
            md_content += f"### {status} 状态文档 ({len(status_docs)}个)\n\n"
            
            for result in sorted(status_docs, key=lambda x: x.completeness, reverse=True):
                md_content += f"#### {result.file_path}\n\n"
                md_content += f"- **完成度**: {result.completeness:.1%}\n"
                md_content += f"- **字数**: {result.word_count}\n"
                md_content += f"- **质量指标**: "
                
                quality_items = []
                if result.has_references:
                    quality_items.append("✓ 参考文献")
                if result.has_examples:
                    quality_items.append("✓ 示例案例")
                if result.has_dsl:
                    quality_items.append("✓ DSL设计")
                if result.has_theory:
                    quality_items.append("✓ 理论说明")
                
                md_content += ", ".join(quality_items) if quality_items else "无"
                md_content += "\n"
                
                if result.issues:
                    md_content += f"- **问题**: {', '.join(result.issues)}\n"
                
                if result.suggestions:
                    md_content += f"- **建议**: {', '.join(result.suggestions)}\n"
                
                md_content += "\n"
        
        # 保存报告
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(md_content)
        
        return md_content

def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description="文档完成度检查工具")
    parser.add_argument("--docs-root", default="docs", help="文档根目录")
    parser.add_argument("--output", default="document_check_report", help="输出文件名前缀")
    parser.add_argument("--format", choices=["json", "md", "both"], default="both", help="输出格式")
    
    args = parser.parse_args()
    
    # 创建检查器
    checker = DocumentChecker(args.docs_root)
    
    # 执行检查
    print("开始检查文档...")
    results = checker.check_all_documents()
    print(f"检查完成，共检查 {len(results)} 个文档")
    
    # 生成报告
    if args.format in ["json", "both"]:
        json_report = checker.generate_report(f"{args.output}.json")
        print(f"JSON报告已生成: {args.output}.json")
    
    if args.format in ["md", "both"]:
        md_report = checker.generate_markdown_report(f"{args.output}.md")
        print(f"Markdown报告已生成: {args.output}.md")
    
    # 打印摘要
    total_docs = len(results)
    status_counts = {}
    avg_completeness = 0.0
    
    for result in results:
        status_counts[result.status] = status_counts.get(result.status, 0) + 1
        avg_completeness += result.completeness
    
    avg_completeness /= total_docs
    
    print("\n=== 检查摘要 ===")
    print(f"总文档数: {total_docs}")
    print(f"平均完成度: {avg_completeness:.1%}")
    print("状态分布:")
    for status, count in status_counts.items():
        print(f"  {status}: {count} ({count/total_docs*100:.1f}%)")

if __name__ == "__main__":
    main()
