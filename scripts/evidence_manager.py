#!/usr/bin/env python3
"""
证据条目管理工具
用于管理证据条目的创建、验证和更新
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Set, Optional
from datetime import datetime
from dataclasses import dataclass

@dataclass
class EvidenceEntry:
    """证据条目数据类"""
    id: str
    title: str
    version: str
    status: str
    category: str
    source: str
    credibility: str
    created_at: str
    updated_at: str
    file_path: str
    
    # 对齐维度
    terminology_alignment: List[str]
    structure_alignment: List[str]
    constraint_alignment: List[str]
    metric_alignment: List[str]
    
    # 映射关系
    l2_mappings: List[str]
    l3_mappings: List[str]
    l4_mappings: List[str]
    
    # 引用信息
    references: Dict[str, str]
    
    # 评审信息
    reviewers: List[str]
    conclusion: str
    notes: str

class EvidenceManager:
    def __init__(self, evidence_dir: str = "docs/evidence"):
        self.evidence_dir = Path(evidence_dir)
        self.evidence_entries: Dict[str, EvidenceEntry] = {}
        self.load_evidence_entries()
    
    def load_evidence_entries(self):
        """加载所有证据条目"""
        print("加载证据条目...")
        
        if not self.evidence_dir.exists():
            print(f"证据目录不存在: {self.evidence_dir}")
            return
        
        for md_file in self.evidence_dir.glob("*.md"):
            evidence = self.parse_evidence_file(md_file)
            if evidence:
                self.evidence_entries[evidence.id] = evidence
        
        print(f"加载了 {len(self.evidence_entries)} 个证据条目")
    
    def parse_evidence_file(self, file_path: Path) -> Optional[EvidenceEntry]:
        """解析证据条目文件"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"读取文件失败 {file_path}: {e}")
            return None
        
        # 提取YAML前置元数据
        metadata = self.extract_metadata(content)
        if not metadata:
            return None
        
        # 提取对齐维度
        terminology_alignment = self.extract_alignment(content, "术语对齐")
        structure_alignment = self.extract_alignment(content, "结构/接口对齐")
        constraint_alignment = self.extract_alignment(content, "约束/不变式对齐")
        metric_alignment = self.extract_alignment(content, "度量/指标对齐")
        
        # 提取映射关系
        l2_mappings = self.extract_mappings(content, "L2映射")
        l3_mappings = self.extract_mappings(content, "L3映射")
        l4_mappings = self.extract_mappings(content, "L4映射")
        
        # 提取引用信息
        references = self.extract_references(content)
        
        # 提取评审信息
        reviewers = self.extract_reviewers(content)
        conclusion = self.extract_conclusion(content)
        notes = self.extract_notes(content)
        
        return EvidenceEntry(
            id=metadata.get("id", ""),
            title=metadata.get("title", ""),
            version=metadata.get("version", ""),
            status=metadata.get("status", ""),
            category=metadata.get("category", ""),
            source=metadata.get("source", ""),
            credibility=metadata.get("credibility", ""),
            created_at=metadata.get("created_at", ""),
            updated_at=metadata.get("updated_at", ""),
            file_path=str(file_path),
            terminology_alignment=terminology_alignment,
            structure_alignment=structure_alignment,
            constraint_alignment=constraint_alignment,
            metric_alignment=metric_alignment,
            l2_mappings=l2_mappings,
            l3_mappings=l3_mappings,
            l4_mappings=l4_mappings,
            references=references,
            reviewers=reviewers,
            conclusion=conclusion,
            notes=notes
        )
    
    def extract_metadata(self, content: str) -> Dict:
        """提取YAML前置元数据"""
        metadata = {}
        
        yaml_match = re.match(r'^---\n(.*?)\n---\n', content, re.DOTALL)
        if yaml_match:
            yaml_content = yaml_match.group(1)
            for line in yaml_content.split('\n'):
                if ':' in line:
                    key, value = line.split(':', 1)
                    metadata[key.strip()] = value.strip().strip('"\'')
        
        return metadata
    
    def extract_alignment(self, content: str, section_name: str) -> List[str]:
        """提取对齐维度"""
        alignments = []
        
        # 匹配对齐部分
        pattern = rf'### 3\.\d+\s+{re.escape(section_name)}.*?\n(.*?)(?=\n###|\n##|\Z)'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            section_content = match.group(1)
            # 提取列表项
            for line in section_content.split('\n'):
                if line.strip().startswith('- '):
                    alignments.append(line.strip()[2:])
        
        return alignments
    
    def extract_mappings(self, content: str, mapping_type: str) -> List[str]:
        """提取映射关系"""
        mappings = []
        
        # 匹配映射部分
        pattern = rf'### 4\.\d+\s+{re.escape(mapping_type)}.*?\n(.*?)(?=\n###|\n##|\Z)'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            section_content = match.group(1)
            # 提取列表项
            for line in section_content.split('\n'):
                if line.strip().startswith('- '):
                    mappings.append(line.strip()[2:])
        
        return mappings
    
    def extract_references(self, content: str) -> Dict[str, str]:
        """提取引用信息"""
        references = {}
        
        # 匹配引用部分
        pattern = r'## 5\.\s+引用.*?\n(.*?)(?=\n##|\Z)'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            section_content = match.group(1)
            
            # 提取原文链接
            link_pattern = r'### 5\.\d+\s+原文链接.*?\n(.*?)(?=\n###|\n##|\Z)'
            link_match = re.search(link_pattern, section_content, re.DOTALL)
            if link_match:
                link_content = link_match.group(1)
                for line in link_content.split('\n'):
                    if line.strip().startswith('- '):
                        # 解析链接格式
                        link_match = re.match(r'- \*\*([^*]+)\*\*：(.+)', line.strip())
                        if link_match:
                            references[link_match.group(1)] = link_match.group(2)
        
        return references
    
    def extract_reviewers(self, content: str) -> List[str]:
        """提取评审人信息"""
        reviewers = []
        
        # 匹配评审部分
        pattern = r'## 6\.\s+评审.*?\n(.*?)(?=\n##|\Z)'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            section_content = match.group(1)
            
            # 提取评审人
            reviewer_pattern = r'### 6\.\d+\s+评审人.*?\n(.*?)(?=\n###|\n##|\Z)'
            reviewer_match = re.search(reviewer_pattern, section_content, re.DOTALL)
            if reviewer_match:
                reviewer_content = reviewer_match.group(1)
                for line in reviewer_content.split('\n'):
                    if line.strip().startswith('- '):
                        reviewers.append(line.strip()[2:])
        
        return reviewers
    
    def extract_conclusion(self, content: str) -> str:
        """提取评审结论"""
        # 匹配结论部分
        pattern = r'### 6\.\d+\s+结论.*?\n(.*?)(?=\n###|\n##|\Z)'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            return match.group(1).strip()
        
        return ""
    
    def extract_notes(self, content: str) -> str:
        """提取备注信息"""
        # 匹配备注部分
        pattern = r'### 6\.\d+\s+备注.*?\n(.*?)(?=\n###|\n##|\Z)'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            return match.group(1).strip()
        
        return ""
    
    def validate_evidence_entry(self, evidence: EvidenceEntry) -> List[str]:
        """验证证据条目"""
        issues = []
        
        # 检查必需字段
        if not evidence.id:
            issues.append("缺少证据ID")
        if not evidence.title:
            issues.append("缺少标题")
        if not evidence.source:
            issues.append("缺少来源")
        if not evidence.credibility:
            issues.append("缺少可信度")
        
        # 检查对齐维度
        if not evidence.terminology_alignment:
            issues.append("缺少术语对齐")
        if not evidence.structure_alignment:
            issues.append("缺少结构对齐")
        if not evidence.constraint_alignment:
            issues.append("缺少约束对齐")
        if not evidence.metric_alignment:
            issues.append("缺少度量对齐")
        
        # 检查映射关系
        if not evidence.l2_mappings:
            issues.append("缺少L2映射")
        if not evidence.l3_mappings:
            issues.append("缺少L3映射")
        if not evidence.l4_mappings:
            issues.append("缺少L4映射")
        
        # 检查引用信息
        if not evidence.references:
            issues.append("缺少引用信息")
        
        # 检查评审信息
        if not evidence.reviewers:
            issues.append("缺少评审人信息")
        if not evidence.conclusion:
            issues.append("缺少评审结论")
        
        return issues
    
    def generate_evidence_report(self) -> str:
        """生成证据条目报告"""
        report = []
        report.append("# 证据条目管理报告")
        report.append(f"生成时间: {datetime.now().isoformat()}")
        report.append("")
        
        # 统计信息
        total_entries = len(self.evidence_entries)
        valid_entries = 0
        invalid_entries = 0
        
        for evidence in self.evidence_entries.values():
            issues = self.validate_evidence_entry(evidence)
            if not issues:
                valid_entries += 1
            else:
                invalid_entries += 1
        
        report.append("## 统计信息")
        report.append(f"- 总证据条目数: {total_entries}")
        report.append(f"- 有效条目数: {valid_entries}")
        report.append(f"- 无效条目数: {invalid_entries}")
        report.append(f"- 完整性: {valid_entries/total_entries*100:.1f}%")
        report.append("")
        
        # 按类别统计
        categories = {}
        for evidence in self.evidence_entries.values():
            category = evidence.category
            if category not in categories:
                categories[category] = 0
            categories[category] += 1
        
        report.append("## 按类别统计")
        for category, count in categories.items():
            report.append(f"- {category}: {count}")
        report.append("")
        
        # 按可信度统计
        credibility_levels = {}
        for evidence in self.evidence_entries.values():
            credibility = evidence.credibility
            if credibility not in credibility_levels:
                credibility_levels[credibility] = 0
            credibility_levels[credibility] += 1
        
        report.append("## 按可信度统计")
        for credibility, count in credibility_levels.items():
            report.append(f"- {credibility}: {count}")
        report.append("")
        
        # 详细列表
        report.append("## 证据条目详细列表")
        for evidence_id, evidence in sorted(self.evidence_entries.items()):
            report.append(f"### {evidence.title}")
            report.append(f"- ID: {evidence.id}")
            report.append(f"- 版本: {evidence.version}")
            report.append(f"- 状态: {evidence.status}")
            report.append(f"- 类别: {evidence.category}")
            report.append(f"- 来源: {evidence.source}")
            report.append(f"- 可信度: {evidence.credibility}")
            report.append(f"- 文件路径: `{evidence.file_path}`")
            
            # 验证结果
            issues = self.validate_evidence_entry(evidence)
            if issues:
                report.append(f"- 问题: {', '.join(issues)}")
            else:
                report.append("- 状态: ✅ 完整")
            
            report.append("")
        
        return "\n".join(report)
    
    def save_evidence_data(self, output_file: str = "evidence_data.json"):
        """保存证据条目数据到JSON文件"""
        evidence_data = {}
        for evidence_id, evidence in self.evidence_entries.items():
            evidence_data[evidence_id] = {
                "id": evidence.id,
                "title": evidence.title,
                "version": evidence.version,
                "status": evidence.status,
                "category": evidence.category,
                "source": evidence.source,
                "credibility": evidence.credibility,
                "created_at": evidence.created_at,
                "updated_at": evidence.updated_at,
                "file_path": evidence.file_path,
                "terminology_alignment": evidence.terminology_alignment,
                "structure_alignment": evidence.structure_alignment,
                "constraint_alignment": evidence.constraint_alignment,
                "metric_alignment": evidence.metric_alignment,
                "l2_mappings": evidence.l2_mappings,
                "l3_mappings": evidence.l3_mappings,
                "l4_mappings": evidence.l4_mappings,
                "references": evidence.references,
                "reviewers": evidence.reviewers,
                "conclusion": evidence.conclusion,
                "notes": evidence.notes
            }
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(evidence_data, f, ensure_ascii=False, indent=2)
        print(f"证据条目数据已保存到 {output_file}")
    
    def save_evidence_report(self, output_file: str = "evidence_report.md"):
        """保存证据条目报告到Markdown文件"""
        report = self.generate_evidence_report()
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"证据条目报告已保存到 {output_file}")
    
    def run(self):
        """运行证据条目管理"""
        print("开始管理证据条目...")
        
        self.save_evidence_data()
        self.save_evidence_report()
        
        print("证据条目管理完成！")

def main():
    manager = EvidenceManager()
    manager.run()

if __name__ == "__main__":
    main()
