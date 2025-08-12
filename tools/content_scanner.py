#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework 内容扫描工具

自动检测项目文档的空白点、薄弱点和质量评估
"""

import os
import yaml
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime
import argparse


@dataclass
class FileAnalysis:
    """文件分析结果"""
    path: str
    size: int
    sections: List[str]
    code_blocks: int
    links: int
    quality_score: float
    issues: List[str]
    suggestions: List[str]


@dataclass
class ScanResult:
    """扫描结果"""
    total_files: int
    analyzed_files: int
    missing_files: List[str]
    low_quality_files: List[FileAnalysis]
    suggestions: List[str]
    quality_report: Dict


class ContentScanner:
    """内容扫描器"""
    
    def __init__(self, config_path: str = "config/automation_config.yaml"):
        """初始化扫描器"""
        self.config = self._load_config(config_path)
        self.project_root = Path(".")
        
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
            'content_scanner': {
                'required_files': ['theory.md', 'dsl-draft.md'],
                'quality_threshold': 0.7,
                'scan_patterns': ['*.md'],
                'exclude_patterns': ['**/temp/**', '**/draft/**', '**/.git/**'],
                'min_file_size': 100,
                'required_sections': ['概念定义', '理论基础', '应用案例', '最佳实践']
            },
            'quality_assessor': {
                'weights': {
                    'completeness': 0.3,
                    'consistency': 0.3,
                    'readability': 0.4
                },
                'thresholds': {
                    'warning': 0.6,
                    'error': 0.4
                }
            }
        }
    
    def scan_project(self) -> ScanResult:
        """扫描整个项目"""
        print("开始扫描项目内容...")
        
        # 获取所有需要扫描的文件
        all_files = self._get_all_files()
        required_files = self._get_required_files()
        
        # 分析文件
        analyzed_files = []
        missing_files = []
        
        for file_path in all_files:
            if self._should_analyze_file(file_path):
                analysis = self._analyze_file(file_path)
                analyzed_files.append(analysis)
                
                if analysis.quality_score < self.config['content_scanner']['quality_threshold']:
                    analyzed_files.append(analysis)
        
        # 检查缺失的必需文件
        missing_files = self._find_missing_files(required_files)
        
        # 生成建议
        suggestions = self._generate_suggestions(analyzed_files, missing_files)
        
        # 生成质量报告
        quality_report = self._generate_quality_report(analyzed_files)
        
        return ScanResult(
            total_files=len(all_files),
            analyzed_files=len(analyzed_files),
            missing_files=missing_files,
            low_quality_files=[f for f in analyzed_files if f.quality_score < self.config['content_scanner']['quality_threshold']],
            suggestions=suggestions,
            quality_report=quality_report
        )
    
    def _get_all_files(self) -> List[Path]:
        """获取所有需要扫描的文件"""
        files = []
        scan_patterns = self.config['content_scanner']['scan_patterns']
        exclude_patterns = self.config['content_scanner']['exclude_patterns']
        
        for pattern in scan_patterns:
            for file_path in self.project_root.rglob(pattern):
                # 检查是否在排除列表中
                if not any(self._matches_pattern(file_path, exclude_pattern) for exclude_pattern in exclude_patterns):
                    files.append(file_path)
        
        return files
    
    def _matches_pattern(self, file_path: Path, pattern: str) -> bool:
        """检查文件路径是否匹配模式"""
        try:
            return file_path.match(pattern)
        except:
            return False
    
    def _get_required_files(self) -> List[str]:
        """获取必需的配置文件列表"""
        required_files = []
        docs_dir = self.project_root / "docs"
        
        if docs_dir.exists():
            # 遍历docs目录，查找需要theory.md和dsl-draft.md的子目录
            for subdir in docs_dir.rglob("*"):
                if subdir.is_dir():
                    theory_file = subdir / "theory.md"
                    dsl_file = subdir / "dsl-draft.md"
                    
                    if theory_file.exists() or dsl_file.exists():
                        # 这个目录应该有这些文件
                        if not theory_file.exists():
                            required_files.append(str(theory_file))
                        if not dsl_file.exists():
                            required_files.append(str(dsl_file))
        
        return required_files
    
    def _should_analyze_file(self, file_path: Path) -> bool:
        """判断是否应该分析文件"""
        # 检查文件大小
        if file_path.stat().st_size < self.config['content_scanner']['min_file_size']:
            return False
        
        # 检查文件类型
        if file_path.suffix.lower() not in ['.md']:
            return False
        
        return True
    
    def _analyze_file(self, file_path: Path) -> FileAnalysis:
        """分析单个文件"""
        print(f"分析文件: {file_path}")
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return FileAnalysis(
                path=str(file_path),
                size=0,
                sections=[],
                code_blocks=0,
                links=0,
                quality_score=0.0,
                issues=[f"文件读取错误: {e}"],
                suggestions=["检查文件编码和权限"]
            )
        
        # 分析文件内容
        sections = self._extract_sections(content)
        code_blocks = self._count_code_blocks(content)
        links = self._count_links(content)
        quality_score = self._calculate_quality_score(content, sections, code_blocks, links)
        issues = self._identify_issues(content, sections, code_blocks, links)
        suggestions = self._generate_file_suggestions(content, sections, code_blocks, links)
        
        return FileAnalysis(
            path=str(file_path),
            size=len(content),
            sections=sections,
            code_blocks=code_blocks,
            links=links,
            quality_score=quality_score,
            issues=issues,
            suggestions=suggestions
        )
    
    def _extract_sections(self, content: str) -> List[str]:
        """提取文档章节"""
        sections = []
        lines = content.split('\n')
        
        for line in lines:
            if line.strip().startswith('#'):
                # 提取标题
                title = line.strip().lstrip('#').strip()
                if title:
                    sections.append(title)
        
        return sections
    
    def _count_code_blocks(self, content: str) -> int:
        """统计代码块数量"""
        # 匹配 ``` 代码块
        code_block_pattern = r'```[\w]*\n.*?\n```'
        matches = re.findall(code_block_pattern, content, re.DOTALL)
        return len(matches)
    
    def _count_links(self, content: str) -> int:
        """统计链接数量"""
        # 匹配Markdown链接
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        matches = re.findall(link_pattern, content)
        return len(matches)
    
    def _calculate_quality_score(self, content: str, sections: List[str], code_blocks: int, links: int) -> float:
        """计算质量分数"""
        weights = self.config['quality_assessor']['weights']
        
        # 完整性评分
        completeness = self._calculate_completeness(content, sections, code_blocks, links)
        
        # 一致性评分
        consistency = self._calculate_consistency(content, sections)
        
        # 可读性评分
        readability = self._calculate_readability(content, sections)
        
        # 综合评分
        total_score = (
            completeness * weights['completeness'] +
            consistency * weights['consistency'] +
            readability * weights['readability']
        )
        
        return round(total_score, 2)
    
    def _calculate_completeness(self, content: str, sections: List[str], code_blocks: int, links: int) -> float:
        """计算完整性分数"""
        score = 0.0
        
        # 内容长度
        if len(content) >= 500:
            score += 0.3
        elif len(content) >= 200:
            score += 0.2
        else:
            score += 0.1
        
        # 章节数量
        if len(sections) >= 4:
            score += 0.3
        elif len(sections) >= 2:
            score += 0.2
        else:
            score += 0.1
        
        # 代码示例
        if code_blocks >= 2:
            score += 0.2
        elif code_blocks >= 1:
            score += 0.15
        else:
            score += 0.05
        
        # 链接数量
        if links >= 3:
            score += 0.2
        elif links >= 1:
            score += 0.15
        else:
            score += 0.05
        
        return min(score, 1.0)
    
    def _calculate_consistency(self, content: str, sections: List[str]) -> float:
        """计算一致性分数"""
        score = 0.0
        
        # 检查章节结构一致性
        if len(sections) >= 2:
            # 检查是否有逻辑顺序
            required_sections = self.config['content_scanner']['required_sections']
            found_sections = [s for s in sections if any(req in s for req in required_sections)]
            
            if len(found_sections) >= len(required_sections) * 0.5:
                score += 0.5
            
            # 检查章节层次结构
            if self._check_section_hierarchy(sections):
                score += 0.5
        
        return score
    
    def _calculate_readability(self, content: str, sections: List[str]) -> float:
        """计算可读性分数"""
        score = 0.0
        
        # 检查段落结构
        paragraphs = [p for p in content.split('\n\n') if p.strip()]
        if len(paragraphs) >= 3:
            score += 0.3
        
        # 检查列表使用
        if re.search(r'^\s*[-*+]\s+', content, re.MULTILINE):
            score += 0.2
        
        # 检查表格使用
        if re.search(r'\|.*\|', content):
            score += 0.2
        
        # 检查代码块格式
        if re.search(r'```[\w]*\n', content):
            score += 0.3
        
        return min(score, 1.0)
    
    def _check_section_hierarchy(self, sections: List[str]) -> bool:
        """检查章节层次结构"""
        if len(sections) < 2:
            return False
        
        # 简单的层次检查：确保有主标题和子标题
        main_sections = [s for s in sections if not s.startswith('  ')]
        sub_sections = [s for s in sections if s.startswith('  ')]
        
        return len(main_sections) > 0
    
    def _identify_issues(self, content: str, sections: List[str], code_blocks: int, links: int) -> List[str]:
        """识别问题"""
        issues = []
        
        # 内容长度问题
        if len(content) < 200:
            issues.append("内容过短，建议增加更多详细信息")
        
        # 章节问题
        if len(sections) < 2:
            issues.append("章节结构不完整，建议添加更多章节")
        
        # 代码示例问题
        if code_blocks == 0:
            issues.append("缺少代码示例，建议添加相关代码")
        
        # 链接问题
        if links < 2:
            issues.append("缺少相关链接，建议添加内部或外部链接")
        
        # 检查必需章节
        required_sections = self.config['content_scanner']['required_sections']
        missing_sections = []
        for req_section in required_sections:
            if not any(req_section in section for section in sections):
                missing_sections.append(req_section)
        
        if missing_sections:
            issues.append(f"缺少必需章节: {', '.join(missing_sections)}")
        
        return issues
    
    def _generate_file_suggestions(self, content: str, sections: List[str], code_blocks: int, links: int) -> List[str]:
        """生成文件改进建议"""
        suggestions = []
        
        # 内容长度建议
        if len(content) < 500:
            suggestions.append("增加内容长度，提供更详细的说明")
        
        # 章节建议
        if len(sections) < 4:
            suggestions.append("添加更多章节，完善文档结构")
        
        # 代码示例建议
        if code_blocks < 2:
            suggestions.append("添加更多代码示例，提高实用性")
        
        # 链接建议
        if links < 3:
            suggestions.append("添加更多相关链接，增强文档关联性")
        
        return suggestions
    
    def _find_missing_files(self, required_files: List[str]) -> List[str]:
        """查找缺失的必需文件"""
        missing = []
        for file_path in required_files:
            if not Path(file_path).exists():
                missing.append(file_path)
        return missing
    
    def _generate_suggestions(self, analyzed_files: List[FileAnalysis], missing_files: List[str]) -> List[str]:
        """生成整体改进建议"""
        suggestions = []
        
        # 缺失文件建议
        if missing_files:
            suggestions.append(f"需要创建 {len(missing_files)} 个缺失文件")
        
        # 低质量文件建议
        low_quality_count = len([f for f in analyzed_files if f.quality_score < self.config['content_scanner']['quality_threshold']])
        if low_quality_count > 0:
            suggestions.append(f"有 {low_quality_count} 个文件质量较低，需要改进")
        
        # 整体结构建议
        if len(analyzed_files) < 10:
            suggestions.append("文档数量较少，建议增加更多内容")
        
        return suggestions
    
    def _generate_quality_report(self, analyzed_files: List[FileAnalysis]) -> Dict:
        """生成质量报告"""
        if not analyzed_files:
            return {"error": "没有可分析的文件"}
        
        scores = [f.quality_score for f in analyzed_files]
        avg_score = sum(scores) / len(scores)
        
        return {
            "total_files": len(analyzed_files),
            "average_score": round(avg_score, 2),
            "score_distribution": {
                "excellent": len([s for s in scores if s >= 0.8]),
                "good": len([s for s in scores if 0.6 <= s < 0.8]),
                "fair": len([s for s in scores if 0.4 <= s < 0.6]),
                "poor": len([s for s in scores if s < 0.4])
            },
            "top_issues": self._get_top_issues(analyzed_files)
        }
    
    def _get_top_issues(self, analyzed_files: List[FileAnalysis]) -> List[str]:
        """获取最常见的问题"""
        all_issues = []
        for file_analysis in analyzed_files:
            all_issues.extend(file_analysis.issues)
        
        # 统计问题频率
        issue_counts = {}
        for issue in all_issues:
            issue_counts[issue] = issue_counts.get(issue, 0) + 1
        
        # 返回最常见的问题
        sorted_issues = sorted(issue_counts.items(), key=lambda x: x[1], reverse=True)
        return [issue for issue, count in sorted_issues[:5]]
    
    def generate_report(self, result: ScanResult, output_path: str = None) -> str:
        """生成扫描报告"""
        if output_path is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_path = f"reports/content_scan_report_{timestamp}.md"
        
        report_content = f"""# Formal Framework 内容扫描报告

**生成时间**: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

## 扫描概览

- **总文件数**: {result.total_files}
- **已分析文件数**: {result.analyzed_files}
- **缺失文件数**: {len(result.missing_files)}
- **低质量文件数**: {len(result.low_quality_files)}

## 质量评估

### 整体质量分数
- **平均质量分数**: {result.quality_report.get('average_score', 'N/A')}

### 质量分布
"""
        
        if 'score_distribution' in result.quality_report:
            dist = result.quality_report['score_distribution']
            report_content += f"""
- **优秀** (≥0.8): {dist.get('excellent', 0)} 个文件
- **良好** (0.6-0.8): {dist.get('good', 0)} 个文件
- **一般** (0.4-0.6): {dist.get('fair', 0)} 个文件
- **较差** (<0.4): {dist.get('poor', 0)} 个文件
"""
        
        # 缺失文件
        if result.missing_files:
            report_content += "\n## 缺失文件\n\n"
            for file_path in result.missing_files:
                report_content += f"- `{file_path}`\n"
        
        # 低质量文件
        if result.low_quality_files:
            report_content += "\n## 需要改进的文件\n\n"
            for file_analysis in result.low_quality_files:
                report_content += f"### {file_analysis.path}\n"
                report_content += f"- **质量分数**: {file_analysis.quality_score}\n"
                report_content += f"- **文件大小**: {file_analysis.size} 字符\n"
                report_content += f"- **章节数**: {len(file_analysis.sections)}\n"
                report_content += f"- **代码块数**: {file_analysis.code_blocks}\n"
                report_content += f"- **链接数**: {file_analysis.links}\n"
                
                if file_analysis.issues:
                    report_content += "- **问题**:\n"
                    for issue in file_analysis.issues:
                        report_content += f"  - {issue}\n"
                
                if file_analysis.suggestions:
                    report_content += "- **建议**:\n"
                    for suggestion in file_analysis.suggestions:
                        report_content += f"  - {suggestion}\n"
                
                report_content += "\n"
        
        # 常见问题
        if 'top_issues' in result.quality_report and result.quality_report['top_issues']:
            report_content += "\n## 常见问题\n\n"
            for issue in result.quality_report['top_issues']:
                report_content += f"- {issue}\n"
        
        # 改进建议
        if result.suggestions:
            report_content += "\n## 改进建议\n\n"
            for suggestion in result.suggestions:
                report_content += f"- {suggestion}\n"
        
        # 保存报告
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report_content)
        
        print(f"报告已保存到: {output_path}")
        return output_path


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Formal Framework 内容扫描工具')
    parser.add_argument('--config', default='config/automation_config.yaml', help='配置文件路径')
    parser.add_argument('--output', help='输出报告路径')
    parser.add_argument('--verbose', action='store_true', help='详细输出')
    
    args = parser.parse_args()
    
    # 创建扫描器
    scanner = ContentScanner(args.config)
    
    # 执行扫描
    result = scanner.scan_project()
    
    # 生成报告
    report_path = scanner.generate_report(result, args.output)
    
    # 输出摘要
    print(f"\n扫描完成!")
    print(f"总文件数: {result.total_files}")
    print(f"已分析文件数: {result.analyzed_files}")
    print(f"缺失文件数: {len(result.missing_files)}")
    print(f"低质量文件数: {len(result.low_quality_files)}")
    print(f"报告已保存到: {report_path}")


if __name__ == "__main__":
    main() 