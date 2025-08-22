#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework 自动化质量检查工具

该工具提供内容质量、代码质量和文档质量的自动化检查功能，
支持批量检查和持续集成环境。

作者: Formal Framework Team
版本: 1.0.0
日期: 2025-02-10
"""

import os
import re
import json
import yaml
import argparse
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict
from datetime import datetime
import logging

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


@dataclass
class QualityMetrics:
    """质量指标数据类"""
    accuracy: float = 0.0
    completeness: float = 0.0
    readability: float = 0.0
    usefulness: float = 0.0
    consistency: float = 0.0
    overall_score: float = 0.0


@dataclass
class QualityIssue:
    """质量问题数据类"""
    file_path: str
    line_number: Optional[int]
    issue_type: str
    severity: str  # 'error', 'warning', 'info'
    message: str
    suggestion: Optional[str] = None


@dataclass
class QualityReport:
    """质量报告数据类"""
    file_path: str
    file_type: str
    metrics: QualityMetrics
    issues: List[QualityIssue]
    check_time: datetime
    status: str  # 'pass', 'fail', 'warning'


class ContentQualityChecker:
    """内容质量检查器"""
    
    def __init__(self, config: Dict = None):
        self.config = config or self._load_default_config()
        self.quality_rules = self._load_quality_rules()
    
    def _load_default_config(self) -> Dict:
        """加载默认配置"""
        return {
            "min_accuracy_score": 0.7,
            "min_completeness_score": 0.8,
            "min_readability_score": 0.75,
            "min_usefulness_score": 0.7,
            "min_overall_score": 0.75,
            "max_issues_per_file": 10
        }
    
    def _load_quality_rules(self) -> Dict:
        """加载质量检查规则"""
        return {
            "technical_accuracy": {
                "code_blocks": r"```[\w]*\n.*?```",
                "technical_terms": r"\b[A-Z][a-zA-Z0-9]*\b",
                "version_references": r"v?\d+\.\d+(\.\d+)?",
                "url_patterns": r"https?://[^\s]+"
            },
            "completeness": {
                "required_sections": [
                    "## 概述", "## 概念定义", "## 理论基础", 
                    "## 应用场景", "## 总结"
                ],
                "min_content_length": 500,
                "required_links": 3
            },
            "readability": {
                "max_sentence_length": 100,
                "max_paragraph_length": 300,
                "heading_structure": r"^#{1,6}\s+",
                "code_block_ratio": 0.3
            },
            "usefulness": {
                "example_patterns": [r"示例", r"Example", r"例子"],
                "best_practice_patterns": [r"最佳实践", r"Best Practice"],
                "implementation_patterns": [r"实现", r"Implementation"]
            }
        }
    
    def check_content_quality(self, file_path: str) -> QualityReport:
        """检查内容质量"""
        logger.info(f"检查内容质量: {file_path}")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            logger.error(f"无法读取文件 {file_path}: {e}")
            return self._create_error_report(file_path, str(e))
        
        issues = []
        metrics = QualityMetrics()
        
        # 检查技术准确性
        accuracy_score, accuracy_issues = self._check_technical_accuracy(content, file_path)
        metrics.accuracy = accuracy_score
        issues.extend(accuracy_issues)
        
        # 检查完整性
        completeness_score, completeness_issues = self._check_completeness(content, file_path)
        metrics.completeness = completeness_score
        issues.extend(completeness_issues)
        
        # 检查可读性
        readability_score, readability_issues = self._check_readability(content, file_path)
        metrics.readability = readability_score
        issues.extend(readability_issues)
        
        # 检查实用性
        usefulness_score, usefulness_issues = self._check_usefulness(content, file_path)
        metrics.usefulness = usefulness_score
        issues.extend(usefulness_issues)
        
        # 检查一致性
        consistency_score, consistency_issues = self._check_consistency(content, file_path)
        metrics.consistency = consistency_score
        issues.extend(consistency_issues)
        
        # 计算总体分数
        metrics.overall_score = (
            metrics.accuracy * 0.25 +
            metrics.completeness * 0.25 +
            metrics.readability * 0.2 +
            metrics.usefulness * 0.2 +
            metrics.consistency * 0.1
        )
        
        # 确定状态
        status = self._determine_status(metrics, issues)
        
        return QualityReport(
            file_path=file_path,
            file_type="markdown",
            metrics=metrics,
            issues=issues[:self.config["max_issues_per_file"]],
            check_time=datetime.now(),
            status=status
        )
    
    def _check_technical_accuracy(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查技术准确性"""
        score = 1.0
        issues = []
        
        # 检查代码块
        code_blocks = re.findall(self.quality_rules["technical_accuracy"]["code_blocks"], content, re.DOTALL)
        if not code_blocks:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="technical_accuracy",
                severity="warning",
                message="文档缺少代码示例",
                suggestion="添加相关的代码示例来提高技术准确性"
            ))
            score -= 0.1
        
        # 检查技术术语
        technical_terms = re.findall(self.quality_rules["technical_accuracy"]["technical_terms"], content)
        if len(technical_terms) < 5:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="technical_accuracy",
                severity="info",
                message="技术术语使用较少",
                suggestion="增加技术术语的使用以提高专业性"
            ))
            score -= 0.05
        
        return max(0.0, score), issues
    
    def _check_completeness(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查完整性"""
        score = 1.0
        issues = []
        
        # 检查必需章节
        missing_sections = []
        for section in self.quality_rules["completeness"]["required_sections"]:
            if section not in content:
                missing_sections.append(section)
        
        if missing_sections:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="completeness",
                severity="warning",
                message=f"缺少必需章节: {', '.join(missing_sections)}",
                suggestion="添加缺少的章节以提高文档完整性"
            ))
            score -= 0.2 * len(missing_sections)
        
        # 检查内容长度
        if len(content) < self.quality_rules["completeness"]["min_content_length"]:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="completeness",
                severity="warning",
                message="文档内容过短",
                suggestion="增加文档内容以提高完整性"
            ))
            score -= 0.15
        
        return max(0.0, score), issues
    
    def _check_readability(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查可读性"""
        score = 1.0
        issues = []
        
        lines = content.split('\n')
        long_sentences = 0
        
        for i, line in enumerate(lines):
            if len(line) > self.quality_rules["readability"]["max_sentence_length"]:
                long_sentences += 1
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=i + 1,
                    issue_type="readability",
                    severity="info",
                    message="句子过长",
                    suggestion="将长句子分解为多个短句子"
                ))
        
        if long_sentences > 5:
            score -= 0.1
        
        # 检查标题结构
        headings = re.findall(self.quality_rules["readability"]["heading_structure"], content, re.MULTILINE)
        if len(headings) < 3:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="readability",
                severity="warning",
                message="标题结构不清晰",
                suggestion="添加更多标题来改善文档结构"
            ))
            score -= 0.1
        
        return max(0.0, score), issues
    
    def _check_usefulness(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查实用性"""
        score = 1.0
        issues = []
        
        # 检查示例
        has_examples = any(re.search(pattern, content) for pattern in self.quality_rules["usefulness"]["example_patterns"])
        if not has_examples:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="usefulness",
                severity="warning",
                message="缺少实际示例",
                suggestion="添加实际示例来提高实用性"
            ))
            score -= 0.15
        
        # 检查最佳实践
        has_best_practices = any(re.search(pattern, content) for pattern in self.quality_rules["usefulness"]["best_practice_patterns"])
        if not has_best_practices:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="usefulness",
                severity="info",
                message="缺少最佳实践指导",
                suggestion="添加最佳实践指导"
            ))
            score -= 0.1
        
        return max(0.0, score), issues
    
    def _check_consistency(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查一致性"""
        score = 1.0
        issues = []
        
        # 检查格式一致性
        if content.count('```') % 2 != 0:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="consistency",
                severity="error",
                message="代码块格式不一致",
                suggestion="检查代码块的开始和结束标记"
            ))
            score -= 0.2
        
        # 检查标题级别一致性
        heading_levels = re.findall(r'^(#{1,6})\s+', content, re.MULTILINE)
        if heading_levels:
            levels = [len(level) for level in heading_levels]
            if max(levels) - min(levels) > 3:
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=None,
                    issue_type="consistency",
                    severity="warning",
                    message="标题级别跳跃过大",
                    suggestion="保持标题级别的连续性"
                ))
                score -= 0.1
        
        return max(0.0, score), issues
    
    def _determine_status(self, metrics: QualityMetrics, issues: List[QualityIssue]) -> str:
        """确定检查状态"""
        if metrics.overall_score >= self.config["min_overall_score"]:
            if any(issue.severity == "error" for issue in issues):
                return "warning"
            return "pass"
        return "fail"
    
    def _create_error_report(self, file_path: str, error_message: str) -> QualityReport:
        """创建错误报告"""
        return QualityReport(
            file_path=file_path,
            file_type="unknown",
            metrics=QualityMetrics(),
            issues=[QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="system_error",
                severity="error",
                message=error_message
            )],
            check_time=datetime.now(),
            status="fail"
        )


class CodeQualityChecker:
    """代码质量检查器"""
    
    def __init__(self, config: Dict = None):
        self.config = config or self._load_default_config()
    
    def _load_default_config(self) -> Dict:
        """加载默认配置"""
        return {
            "max_complexity": 10,
            "max_line_length": 120,
            "min_test_coverage": 0.8,
            "required_docstrings": True
        }
    
    def check_code_quality(self, file_path: str) -> QualityReport:
        """检查代码质量"""
        logger.info(f"检查代码质量: {file_path}")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            logger.error(f"无法读取文件 {file_path}: {e}")
            return self._create_error_report(file_path, str(e))
        
        issues = []
        metrics = QualityMetrics()
        
        # 检查代码风格
        style_score, style_issues = self._check_code_style(content, file_path)
        metrics.accuracy = style_score
        issues.extend(style_issues)
        
        # 检查复杂度
        complexity_score, complexity_issues = self._check_complexity(content, file_path)
        metrics.completeness = complexity_score
        issues.extend(complexity_issues)
        
        # 检查文档
        doc_score, doc_issues = self._check_documentation(content, file_path)
        metrics.readability = doc_score
        issues.extend(doc_issues)
        
        # 检查安全性
        security_score, security_issues = self._check_security(content, file_path)
        metrics.usefulness = security_score
        issues.extend(security_issues)
        
        # 计算总体分数
        metrics.overall_score = (
            metrics.accuracy * 0.3 +
            metrics.completeness * 0.25 +
            metrics.readability * 0.25 +
            metrics.usefulness * 0.2
        )
        
        status = "pass" if metrics.overall_score >= 0.8 else "fail"
        
        return QualityReport(
            file_path=file_path,
            file_type="python",
            metrics=metrics,
            issues=issues,
            check_time=datetime.now(),
            status=status
        )
    
    def _check_code_style(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查代码风格"""
        score = 1.0
        issues = []
        
        lines = content.split('\n')
        long_lines = 0
        
        for i, line in enumerate(lines):
            if len(line) > self.config["max_line_length"]:
                long_lines += 1
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=i + 1,
                    issue_type="code_style",
                    severity="warning",
                    message="代码行过长",
                    suggestion="将长行分解为多行"
                ))
        
        if long_lines > 0:
            score -= 0.1 * min(long_lines / 10, 1.0)
        
        return max(0.0, score), issues
    
    def _check_complexity(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查代码复杂度"""
        score = 1.0
        issues = []
        
        # 简单的复杂度检查
        function_count = content.count('def ')
        if function_count > 20:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="complexity",
                severity="warning",
                message="函数数量过多",
                suggestion="考虑将代码分解为多个模块"
            ))
            score -= 0.1
        
        return max(0.0, score), issues
    
    def _check_documentation(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查文档"""
        score = 1.0
        issues = []
        
        if self.config["required_docstrings"]:
            functions = re.findall(r'def\s+(\w+)\s*\(', content)
            docstrings = re.findall(r'""".*?"""', content, re.DOTALL)
            
            if len(functions) > len(docstrings):
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=None,
                    issue_type="documentation",
                    severity="warning",
                    message="缺少函数文档字符串",
                    suggestion="为所有函数添加文档字符串"
                ))
                score -= 0.2
        
        return max(0.0, score), issues
    
    def _check_security(self, content: str, file_path: str) -> Tuple[float, List[QualityIssue]]:
        """检查安全性"""
        score = 1.0
        issues = []
        
        # 检查潜在的安全问题
        security_patterns = [
            (r'eval\s*\(', "使用eval函数存在安全风险"),
            (r'exec\s*\(', "使用exec函数存在安全风险"),
            (r'input\s*\(', "直接使用input可能存在安全风险"),
        ]
        
        for pattern, message in security_patterns:
            if re.search(pattern, content):
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=None,
                    issue_type="security",
                    severity="warning",
                    message=message,
                    suggestion="考虑使用更安全的替代方案"
                ))
                score -= 0.1
        
        return max(0.0, score), issues
    
    def _create_error_report(self, file_path: str, error_message: str) -> QualityReport:
        """创建错误报告"""
        return QualityReport(
            file_path=file_path,
            file_type="unknown",
            metrics=QualityMetrics(),
            issues=[QualityIssue(
                file_path=file_path,
                line_number=None,
                issue_type="system_error",
                severity="error",
                message=error_message
            )],
            check_time=datetime.now(),
            status="fail"
        )


class QualityChecker:
    """主质量检查器"""
    
    def __init__(self, config_path: Optional[str] = None):
        self.config = self._load_config(config_path)
        self.content_checker = ContentQualityChecker(self.config.get("content", {}))
        self.code_checker = CodeQualityChecker(self.config.get("code", {}))
    
    def _load_config(self, config_path: Optional[str]) -> Dict:
        """加载配置文件"""
        if config_path and os.path.exists(config_path):
            try:
                with open(config_path, 'r', encoding='utf-8') as f:
                    return yaml.safe_load(f)
            except Exception as e:
                logger.warning(f"无法加载配置文件 {config_path}: {e}")
        
        return {}
    
    def check_file(self, file_path: str) -> QualityReport:
        """检查单个文件"""
        file_ext = Path(file_path).suffix.lower()
        
        if file_ext in ['.md', '.markdown']:
            return self.content_checker.check_content_quality(file_path)
        elif file_ext in ['.py', '.js', '.java', '.cpp', '.c']:
            return self.code_checker.check_code_quality(file_path)
        else:
            logger.warning(f"不支持的文件类型: {file_ext}")
            return QualityReport(
                file_path=file_path,
                file_type="unknown",
                metrics=QualityMetrics(),
                issues=[],
                check_time=datetime.now(),
                status="skip"
            )
    
    def check_directory(self, directory_path: str, recursive: bool = True) -> List[QualityReport]:
        """检查目录中的所有文件"""
        reports = []
        directory = Path(directory_path)
        
        if recursive:
            files = directory.rglob('*')
        else:
            files = directory.glob('*')
        
        for file_path in files:
            if file_path.is_file():
                report = self.check_file(str(file_path))
                reports.append(report)
        
        return reports
    
    def generate_summary_report(self, reports: List[QualityReport]) -> Dict:
        """生成汇总报告"""
        if not reports:
            return {"error": "没有检查报告"}
        
        total_files = len(reports)
        passed_files = sum(1 for r in reports if r.status == "pass")
        failed_files = sum(1 for r in reports if r.status == "fail")
        warning_files = sum(1 for r in reports if r.status == "warning")
        
        total_issues = sum(len(r.issues) for r in reports)
        error_issues = sum(1 for r in reports for issue in r.issues if issue.severity == "error")
        warning_issues = sum(1 for r in reports for issue in r.issues if issue.severity == "warning")
        
        avg_overall_score = sum(r.metrics.overall_score for r in reports) / total_files
        
        return {
            "summary": {
                "total_files": total_files,
                "passed_files": passed_files,
                "failed_files": failed_files,
                "warning_files": warning_files,
                "pass_rate": passed_files / total_files if total_files > 0 else 0,
                "total_issues": total_issues,
                "error_issues": error_issues,
                "warning_issues": warning_issues,
                "average_score": avg_overall_score
            },
            "reports": [asdict(report) for report in reports]
        }
    
    def save_report(self, report_data: Dict, output_path: str):
        """保存报告到文件"""
        try:
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(report_data, f, indent=2, ensure_ascii=False, default=str)
            logger.info(f"报告已保存到: {output_path}")
        except Exception as e:
            logger.error(f"保存报告失败: {e}")


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description="Formal Framework 质量检查工具")
    parser.add_argument("path", help="要检查的文件或目录路径")
    parser.add_argument("--config", "-c", help="配置文件路径")
    parser.add_argument("--output", "-o", help="输出报告文件路径")
    parser.add_argument("--recursive", "-r", action="store_true", help="递归检查目录")
    parser.add_argument("--verbose", "-v", action="store_true", help="详细输出")
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    checker = QualityChecker(args.config)
    
    if os.path.isfile(args.path):
        reports = [checker.check_file(args.path)]
    elif os.path.isdir(args.path):
        reports = checker.check_directory(args.path, args.recursive)
    else:
        logger.error(f"路径不存在: {args.path}")
        return 1
    
    summary = checker.generate_summary_report(reports)
    
    if args.output:
        checker.save_report(summary, args.output)
    else:
        print(json.dumps(summary, indent=2, ensure_ascii=False, default=str))
    
    # 返回适当的退出码
    if summary["summary"]["failed_files"] > 0:
        return 1
    elif summary["summary"]["warning_files"] > 0:
        return 2
    return 0


if __name__ == "__main__":
    exit(main())
