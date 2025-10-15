#!/usr/bin/env python3
"""
质量度量指标系统
用于评估文档质量和完整性
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Set, Tuple
from datetime import datetime
from dataclasses import dataclass
from enum import Enum

class QualityLevel(Enum):
    """质量等级"""
    EXCELLENT = "excellent"
    GOOD = "good"
    FAIR = "fair"
    POOR = "poor"
    INCOMPLETE = "incomplete"

@dataclass
class QualityMetrics:
    """质量度量指标"""
    completeness_score: float
    consistency_score: float
    clarity_score: float
    accuracy_score: float
    usability_score: float
    overall_score: float
    quality_level: QualityLevel
    issues: List[str]
    recommendations: List[str]

class QualityMetricsSystem:
    def __init__(self, docs_root: str = "docs"):
        self.docs_root = Path(docs_root)
        self.quality_metrics: Dict[str, QualityMetrics] = {}
    
    def analyze_document_quality(self, file_path: Path) -> QualityMetrics:
        """分析文档质量"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"读取文件失败 {file_path}: {e}")
            return self.create_empty_metrics()
        
        # 计算各项指标
        completeness_score = self.calculate_completeness(content)
        consistency_score = self.calculate_consistency(content)
        clarity_score = self.calculate_clarity(content)
        accuracy_score = self.calculate_accuracy(content)
        usability_score = self.calculate_usability(content)
        
        # 计算总体得分
        overall_score = (
            completeness_score * 0.3 +
            consistency_score * 0.25 +
            clarity_score * 0.2 +
            accuracy_score * 0.15 +
            usability_score * 0.1
        )
        
        # 确定质量等级
        quality_level = self.determine_quality_level(overall_score)
        
        # 识别问题和建议
        issues = self.identify_issues(content, completeness_score, consistency_score, 
                                    clarity_score, accuracy_score, usability_score)
        recommendations = self.generate_recommendations(issues)
        
        return QualityMetrics(
            completeness_score=completeness_score,
            consistency_score=consistency_score,
            clarity_score=clarity_score,
            accuracy_score=accuracy_score,
            usability_score=usability_score,
            overall_score=overall_score,
            quality_level=quality_level,
            issues=issues,
            recommendations=recommendations
        )
    
    def calculate_completeness(self, content: str) -> float:
        """计算完整性得分"""
        score = 0.0
        max_score = 100.0
        
        # 检查基本结构
        if "## 1." in content:
            score += 10
        if "## 2." in content:
            score += 10
        if "## 3." in content:
            score += 10
        
        # 检查元数据
        if "---" in content and "title:" in content:
            score += 10
        if "version:" in content:
            score += 5
        if "status:" in content:
            score += 5
        
        # 检查内容长度
        word_count = len(content.split())
        if word_count > 1000:
            score += 20
        elif word_count > 500:
            score += 15
        elif word_count > 200:
            score += 10
        elif word_count > 100:
            score += 5
        
        # 检查代码块
        code_blocks = len(re.findall(r'```', content)) // 2
        if code_blocks > 0:
            score += min(code_blocks * 5, 20)
        
        # 检查表格
        tables = len(re.findall(r'\|.*\|', content))
        if tables > 0:
            score += min(tables * 3, 15)
        
        # 检查链接
        links = len(re.findall(r'\[([^\]]+)\]\([^)]+\)', content))
        if links > 0:
            score += min(links * 2, 10)
        
        return min(score, max_score)
    
    def calculate_consistency(self, content: str) -> float:
        """计算一致性得分"""
        score = 0.0
        max_score = 100.0
        
        # 检查标题格式一致性
        headings = re.findall(r'^(#{1,6})\s+(.+)$', content, re.MULTILINE)
        if headings:
            # 检查标题层级是否合理
            levels = [len(h[0]) for h in headings]
            if len(set(levels)) <= 4:  # 最多4个层级
                score += 20
            
            # 检查标题格式是否一致
            consistent_format = True
            for level, text in headings:
                if not text.strip():
                    consistent_format = False
                    break
            if consistent_format:
                score += 20
        
        # 检查列表格式一致性
        list_items = re.findall(r'^[\s]*[-*+]\s+', content, re.MULTILINE)
        if list_items:
            score += 15
        
        # 检查代码块格式一致性
        code_blocks = re.findall(r'```(\w+)?', content)
        if code_blocks:
            score += 15
        
        # 检查链接格式一致性
        links = re.findall(r'\[([^\]]+)\]\([^)]+\)', content)
        if links:
            score += 15
        
        # 检查表格格式一致性
        table_rows = re.findall(r'\|.*\|', content)
        if table_rows:
            score += 15
        
        return min(score, max_score)
    
    def calculate_clarity(self, content: str) -> float:
        """计算清晰度得分"""
        score = 0.0
        max_score = 100.0
        
        # 检查标题清晰度
        headings = re.findall(r'^(#{1,6})\s+(.+)$', content, re.MULTILINE)
        if headings:
            clear_headings = 0
            for level, text in headings:
                if len(text.strip()) > 0 and len(text.strip()) < 100:
                    clear_headings += 1
            score += (clear_headings / len(headings)) * 30
        
        # 检查段落长度
        paragraphs = [p.strip() for p in content.split('\n\n') if p.strip()]
        if paragraphs:
            good_paragraphs = 0
            for para in paragraphs:
                if 50 <= len(para) <= 500:
                    good_paragraphs += 1
            score += (good_paragraphs / len(paragraphs)) * 25
        
        # 检查句子长度
        sentences = re.findall(r'[^.!?]+[.!?]', content)
        if sentences:
            good_sentences = 0
            for sentence in sentences:
                if 10 <= len(sentence.split()) <= 30:
                    good_sentences += 1
            score += (good_sentences / len(sentences)) * 25
        
        # 检查专业术语使用
        technical_terms = len(re.findall(r'\b[A-Z]{2,}\b', content))
        if technical_terms > 0:
            score += min(technical_terms * 2, 20)
        
        return min(score, max_score)
    
    def calculate_accuracy(self, content: str) -> float:
        """计算准确性得分"""
        score = 0.0
        max_score = 100.0
        
        # 检查引用格式
        references = re.findall(r'\[([^\]]+)\]\([^)]+\)', content)
        if references:
            score += min(len(references) * 5, 30)
        
        # 检查证据条目引用
        evidence_refs = re.findall(r'evidence:([A-Z]+-[A-Z]+-\d+)', content)
        if evidence_refs:
            score += min(len(evidence_refs) * 10, 40)
        
        # 检查版本信息
        if "version:" in content:
            score += 10
        
        # 检查日期信息
        if re.search(r'\d{4}-\d{2}-\d{2}', content):
            score += 10
        
        # 检查作者信息
        if "author:" in content:
            score += 10
        
        return min(score, max_score)
    
    def calculate_usability(self, content: str) -> float:
        """计算可用性得分"""
        score = 0.0
        max_score = 100.0
        
        # 检查目录结构
        if "## 目录" in content or "## Table of Contents" in content:
            score += 20
        
        # 检查导航链接
        nav_links = len(re.findall(r'\[([^\]]+)\]\(#[^)]+\)', content))
        if nav_links > 0:
            score += min(nav_links * 3, 25)
        
        # 检查示例代码
        code_blocks = len(re.findall(r'```', content)) // 2
        if code_blocks > 0:
            score += min(code_blocks * 5, 25)
        
        # 检查图表
        images = len(re.findall(r'!\[([^\]]*)\]\([^)]+\)', content))
        if images > 0:
            score += min(images * 5, 15)
        
        # 检查最佳实践
        if "最佳实践" in content or "best practice" in content.lower():
            score += 15
        
        return min(score, max_score)
    
    def determine_quality_level(self, overall_score: float) -> QualityLevel:
        """确定质量等级"""
        if overall_score >= 90:
            return QualityLevel.EXCELLENT
        elif overall_score >= 75:
            return QualityLevel.GOOD
        elif overall_score >= 60:
            return QualityLevel.FAIR
        elif overall_score >= 40:
            return QualityLevel.POOR
        else:
            return QualityLevel.INCOMPLETE
    
    def identify_issues(self, content: str, completeness: float, consistency: float,
                       clarity: float, accuracy: float, usability: float) -> List[str]:
        """识别问题"""
        issues = []
        
        if completeness < 60:
            issues.append("文档内容不完整，缺少重要章节或信息")
        if consistency < 60:
            issues.append("文档格式不一致，需要统一格式规范")
        if clarity < 60:
            issues.append("文档表达不够清晰，需要改进语言表达")
        if accuracy < 60:
            issues.append("文档准确性不足，需要补充引用和验证")
        if usability < 60:
            issues.append("文档可用性较差，需要改进导航和示例")
        
        # 检查具体问题
        if len(content.split()) < 200:
            issues.append("文档内容过短，需要补充更多详细信息")
        
        if not re.search(r'## 1\.', content):
            issues.append("缺少标准化的章节结构")
        
        if not re.search(r'evidence:', content):
            issues.append("缺少证据条目引用")
        
        if not re.search(r'\[([^\]]+)\]\([^)]+\)', content):
            issues.append("缺少外部链接引用")
        
        return issues
    
    def generate_recommendations(self, issues: List[str]) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        issue_keywords = {
            "不完整": "补充缺失的内容和章节",
            "不一致": "统一文档格式和风格",
            "不清晰": "改进语言表达和结构组织",
            "不准确": "补充引用和验证信息",
            "可用性": "添加导航链接和示例代码",
            "过短": "扩展文档内容，添加更多详细信息",
            "缺少": "补充缺失的章节和引用"
        }
        
        for issue in issues:
            for keyword, recommendation in issue_keywords.items():
                if keyword in issue:
                    recommendations.append(recommendation)
                    break
        
        # 通用建议
        if not recommendations:
            recommendations.append("文档质量良好，继续保持")
        
        return list(set(recommendations))  # 去重
    
    def create_empty_metrics(self) -> QualityMetrics:
        """创建空的质量指标"""
        return QualityMetrics(
            completeness_score=0.0,
            consistency_score=0.0,
            clarity_score=0.0,
            accuracy_score=0.0,
            usability_score=0.0,
            overall_score=0.0,
            quality_level=QualityLevel.INCOMPLETE,
            issues=["无法读取文件"],
            recommendations=["检查文件路径和权限"]
        )
    
    def analyze_all_documents(self):
        """分析所有文档"""
        print("开始分析文档质量...")
        
        for md_file in self.docs_root.rglob("*.md"):
            if md_file.name.startswith("."):
                continue
            
            relative_path = md_file.relative_to(self.docs_root)
            metrics = self.analyze_document_quality(md_file)
            self.quality_metrics[str(relative_path)] = metrics
        
        print(f"分析了 {len(self.quality_metrics)} 个文档")
    
    def generate_quality_report(self) -> str:
        """生成质量报告"""
        report = []
        report.append("# 文档质量评估报告")
        report.append(f"生成时间: {datetime.now().isoformat()}")
        report.append("")
        
        # 整体统计
        total_docs = len(self.quality_metrics)
        if total_docs == 0:
            return "# 文档质量评估报告\n\n没有找到可分析的文档。"
        
        # 质量等级分布
        quality_distribution = {}
        for metrics in self.quality_metrics.values():
            level = metrics.quality_level.value
            if level not in quality_distribution:
                quality_distribution[level] = 0
            quality_distribution[level] += 1
        
        # 平均得分
        avg_completeness = sum(m.completeness_score for m in self.quality_metrics.values()) / total_docs
        avg_consistency = sum(m.consistency_score for m in self.quality_metrics.values()) / total_docs
        avg_clarity = sum(m.clarity_score for m in self.quality_metrics.values()) / total_docs
        avg_accuracy = sum(m.accuracy_score for m in self.quality_metrics.values()) / total_docs
        avg_usability = sum(m.usability_score for m in self.quality_metrics.values()) / total_docs
        avg_overall = sum(m.overall_score for m in self.quality_metrics.values()) / total_docs
        
        report.append("## 整体统计")
        report.append(f"- 总文档数: {total_docs}")
        report.append(f"- 平均完整性得分: {avg_completeness:.1f}")
        report.append(f"- 平均一致性得分: {avg_consistency:.1f}")
        report.append(f"- 平均清晰度得分: {avg_clarity:.1f}")
        report.append(f"- 平均准确性得分: {avg_accuracy:.1f}")
        report.append(f"- 平均可用性得分: {avg_usability:.1f}")
        report.append(f"- 平均总体得分: {avg_overall:.1f}")
        report.append("")
        
        # 质量等级分布
        report.append("## 质量等级分布")
        for level, count in quality_distribution.items():
            percentage = count / total_docs * 100
            report.append(f"- {level}: {count} ({percentage:.1f}%)")
        report.append("")
        
        # 详细报告
        report.append("## 详细质量报告")
        for doc_path, metrics in sorted(self.quality_metrics.items()):
            report.append(f"### {doc_path}")
            report.append(f"- 总体得分: {metrics.overall_score:.1f}")
            report.append(f"- 质量等级: {metrics.quality_level.value}")
            report.append(f"- 完整性: {metrics.completeness_score:.1f}")
            report.append(f"- 一致性: {metrics.consistency_score:.1f}")
            report.append(f"- 清晰度: {metrics.clarity_score:.1f}")
            report.append(f"- 准确性: {metrics.accuracy_score:.1f}")
            report.append(f"- 可用性: {metrics.usability_score:.1f}")
            
            if metrics.issues:
                report.append(f"- 问题: {', '.join(metrics.issues)}")
            
            if metrics.recommendations:
                report.append(f"- 建议: {', '.join(metrics.recommendations)}")
            
            report.append("")
        
        return "\n".join(report)
    
    def save_quality_data(self, output_file: str = "quality_metrics.json"):
        """保存质量数据到JSON文件"""
        quality_data = {}
        for doc_path, metrics in self.quality_metrics.items():
            quality_data[doc_path] = {
                "completeness_score": metrics.completeness_score,
                "consistency_score": metrics.consistency_score,
                "clarity_score": metrics.clarity_score,
                "accuracy_score": metrics.accuracy_score,
                "usability_score": metrics.usability_score,
                "overall_score": metrics.overall_score,
                "quality_level": metrics.quality_level.value,
                "issues": metrics.issues,
                "recommendations": metrics.recommendations
            }
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(quality_data, f, ensure_ascii=False, indent=2)
        print(f"质量数据已保存到 {output_file}")
    
    def save_quality_report(self, output_file: str = "quality_report.md"):
        """保存质量报告到Markdown文件"""
        report = self.generate_quality_report()
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"质量报告已保存到 {output_file}")
    
    def run(self):
        """运行质量评估"""
        print("开始文档质量评估...")
        
        self.analyze_all_documents()
        self.save_quality_data()
        self.save_quality_report()
        
        print("文档质量评估完成！")

def main():
    system = QualityMetricsSystem()
    system.run()

if __name__ == "__main__":
    main()
