#!/usr/bin/env python3
"""
文档索引生成工具
用于自动生成文档索引、交叉引用和导航
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Set
from datetime import datetime

class DocumentIndexGenerator:
    def __init__(self, docs_root: str = "docs"):
        self.docs_root = Path(docs_root)
        self.index_data = {
            "generated_at": datetime.now().isoformat(),
            "documents": {},
            "cross_references": {},
            "evidence_entries": {},
            "statistics": {}
        }
    
    def scan_documents(self):
        """扫描所有文档文件"""
        print("扫描文档文件...")
        
        for md_file in self.docs_root.rglob("*.md"):
            if md_file.name.startswith("."):
                continue
            
            relative_path = md_file.relative_to(self.docs_root)
            doc_info = self.analyze_document(md_file)
            
            if doc_info:
                self.index_data["documents"][str(relative_path)] = doc_info
        
        print(f"扫描完成，共找到 {len(self.index_data['documents'])} 个文档")
    
    def analyze_document(self, file_path: Path) -> Dict:
        """分析单个文档"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"读取文件失败 {file_path}: {e}")
            return None
        
        # 提取元数据
        metadata = self.extract_metadata(content)
        
        # 提取标题结构
        headings = self.extract_headings(content)
        
        # 提取交叉引用
        cross_refs = self.extract_cross_references(content)
        
        # 提取证据条目
        evidence_refs = self.extract_evidence_references(content)
        
        # 计算统计信息
        stats = self.calculate_statistics(content)
        
        return {
            "metadata": metadata,
            "headings": headings,
            "cross_references": cross_refs,
            "evidence_references": evidence_refs,
            "statistics": stats,
            "file_size": file_path.stat().st_size,
            "last_modified": datetime.fromtimestamp(file_path.stat().st_mtime).isoformat()
        }
    
    def extract_metadata(self, content: str) -> Dict:
        """提取YAML前置元数据"""
        metadata = {}
        
        # 匹配YAML前置元数据
        yaml_match = re.match(r'^---\n(.*?)\n---\n', content, re.DOTALL)
        if yaml_match:
            yaml_content = yaml_match.group(1)
            for line in yaml_content.split('\n'):
                if ':' in line:
                    key, value = line.split(':', 1)
                    metadata[key.strip()] = value.strip().strip('"\'')
        
        return metadata
    
    def extract_headings(self, content: str) -> List[Dict]:
        """提取标题结构"""
        headings = []
        
        # 匹配Markdown标题
        heading_pattern = r'^(#{1,6})\s+(.+)$'
        for match in re.finditer(heading_pattern, content, re.MULTILINE):
            level = len(match.group(1))
            text = match.group(2).strip()
            
            # 生成锚点链接
            anchor = re.sub(r'[^\w\s-]', '', text.lower())
            anchor = re.sub(r'[-\s]+', '-', anchor)
            
            headings.append({
                "level": level,
                "text": text,
                "anchor": anchor
            })
        
        return headings
    
    def extract_cross_references(self, content: str) -> List[str]:
        """提取交叉引用"""
        cross_refs = []
        
        # 匹配文档引用格式
        ref_patterns = [
            r'`([^`]+\.md)`',  # `文档名.md`
            r'\[([^\]]+)\]\(([^)]+\.md)\)',  # [文本](文档.md)
            r'L[23]_D\d+_[^`]+\.md',  # L3_D01_交互标准模型.md
        ]
        
        for pattern in ref_patterns:
            for match in re.finditer(pattern, content):
                if match.groups():
                    cross_refs.append(match.group(1) if match.group(1) else match.group(0))
                else:
                    cross_refs.append(match.group(0))
        
        return list(set(cross_refs))  # 去重
    
    def extract_evidence_references(self, content: str) -> List[str]:
        """提取证据条目引用"""
        evidence_refs = []
        
        # 匹配证据条目格式
        evidence_pattern = r'evidence:([A-Z]+-[A-Z]+-\d+)'
        for match in re.finditer(evidence_pattern, content):
            evidence_refs.append(match.group(1))
        
        return list(set(evidence_refs))  # 去重
    
    def calculate_statistics(self, content: str) -> Dict:
        """计算文档统计信息"""
        lines = content.split('\n')
        words = content.split()
        
        return {
            "line_count": len(lines),
            "word_count": len(words),
            "char_count": len(content),
            "heading_count": len(re.findall(r'^#{1,6}\s+', content, re.MULTILINE)),
            "link_count": len(re.findall(r'\[([^\]]+)\]\([^)]+\)', content)),
            "code_block_count": len(re.findall(r'```', content)) // 2,
            "table_count": len(re.findall(r'\|.*\|', content))
        }
    
    def build_cross_reference_map(self):
        """构建交叉引用映射"""
        print("构建交叉引用映射...")
        
        for doc_path, doc_info in self.index_data["documents"].items():
            for ref in doc_info["cross_references"]:
                if ref not in self.index_data["cross_references"]:
                    self.index_data["cross_references"][ref] = []
                self.index_data["cross_references"][ref].append(doc_path)
    
    def build_evidence_map(self):
        """构建证据条目映射"""
        print("构建证据条目映射...")
        
        for doc_path, doc_info in self.index_data["documents"].items():
            for evidence in doc_info["evidence_references"]:
                if evidence not in self.index_data["evidence_entries"]:
                    self.index_data["evidence_entries"][evidence] = []
                self.index_data["evidence_entries"][evidence].append(doc_path)
    
    def calculate_overall_statistics(self):
        """计算整体统计信息"""
        print("计算整体统计信息...")
        
        total_docs = len(self.index_data["documents"])
        total_words = sum(doc["statistics"]["word_count"] for doc in self.index_data["documents"].values())
        total_lines = sum(doc["statistics"]["line_count"] for doc in self.index_data["documents"].values())
        
        # 按类型分类
        doc_types = {}
        for doc_path, doc_info in self.index_data["documents"].items():
            doc_type = self.classify_document(doc_path)
            if doc_type not in doc_types:
                doc_types[doc_type] = 0
            doc_types[doc_type] += 1
        
        self.index_data["statistics"] = {
            "total_documents": total_docs,
            "total_words": total_words,
            "total_lines": total_lines,
            "document_types": doc_types,
            "cross_references_count": len(self.index_data["cross_references"]),
            "evidence_entries_count": len(self.index_data["evidence_entries"])
        }
    
    def classify_document(self, doc_path: str) -> str:
        """分类文档类型"""
        if "L2_" in doc_path:
            return "L2_元模型"
        elif "L3_" in doc_path:
            return "L3_标准模型"
        elif "L4_" in doc_path:
            return "L4_行业索引"
        elif "evidence/" in doc_path:
            return "证据条目"
        elif "industry-model/" in doc_path:
            return "行业模型"
        elif "formal-model/" in doc_path:
            return "形式化模型"
        else:
            return "其他文档"
    
    def generate_index_report(self) -> str:
        """生成索引报告"""
        report = []
        report.append("# 文档索引报告")
        report.append(f"生成时间: {self.index_data['generated_at']}")
        report.append("")
        
        # 统计信息
        stats = self.index_data["statistics"]
        report.append("## 统计信息")
        report.append(f"- 总文档数: {stats['total_documents']}")
        report.append(f"- 总字数: {stats['total_words']:,}")
        report.append(f"- 总行数: {stats['total_lines']:,}")
        report.append(f"- 交叉引用数: {stats['cross_references_count']}")
        report.append(f"- 证据条目数: {stats['evidence_entries_count']}")
        report.append("")
        
        # 文档类型分布
        report.append("## 文档类型分布")
        for doc_type, count in stats["document_types"].items():
            report.append(f"- {doc_type}: {count}")
        report.append("")
        
        # 文档列表
        report.append("## 文档列表")
        for doc_path, doc_info in sorted(self.index_data["documents"].items()):
            metadata = doc_info["metadata"]
            title = metadata.get("title", doc_path)
            status = metadata.get("status", "unknown")
            
            report.append(f"### {title}")
            report.append(f"- 路径: `{doc_path}`")
            report.append(f"- 状态: {status}")
            report.append(f"- 字数: {doc_info['statistics']['word_count']:,}")
            report.append(f"- 行数: {doc_info['statistics']['line_count']:,}")
            report.append(f"- 标题数: {doc_info['statistics']['heading_count']}")
            report.append(f"- 交叉引用: {len(doc_info['cross_references'])}")
            report.append(f"- 证据引用: {len(doc_info['evidence_references'])}")
            report.append("")
        
        return "\n".join(report)
    
    def save_index_data(self, output_file: str = "docs_index.json"):
        """保存索引数据到JSON文件"""
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(self.index_data, f, ensure_ascii=False, indent=2)
        print(f"索引数据已保存到 {output_file}")
    
    def save_index_report(self, output_file: str = "docs_index_report.md"):
        """保存索引报告到Markdown文件"""
        report = self.generate_index_report()
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"索引报告已保存到 {output_file}")
    
    def run(self):
        """运行索引生成"""
        print("开始生成文档索引...")
        
        self.scan_documents()
        self.build_cross_reference_map()
        self.build_evidence_map()
        self.calculate_overall_statistics()
        
        self.save_index_data()
        self.save_index_report()
        
        print("文档索引生成完成！")

def main():
    generator = DocumentIndexGenerator()
    generator.run()

if __name__ == "__main__":
    main()
