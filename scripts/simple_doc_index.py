#!/usr/bin/env python3
"""
简化的文档索引生成器
用于快速生成文档索引和统计信息
"""

import os
import re
from pathlib import Path
from datetime import datetime

def generate_simple_index():
    """生成简化的文档索引"""
    docs_root = Path("docs")
    
    if not docs_root.exists():
        print("文档目录不存在")
        return
    
    # 统计信息
    total_docs = 0
    total_words = 0
    total_lines = 0
    
    # 文档分类
    doc_types = {
        "L2_元模型": 0,
        "L3_标准模型": 0,
        "L4_行业索引": 0,
        "证据条目": 0,
        "行业模型": 0,
        "形式化模型": 0,
        "其他文档": 0
    }
    
    # 文档列表
    documents = []
    
    # 扫描文档
    for md_file in docs_root.rglob("*.md"):
        if md_file.name.startswith("."):
            continue
        
        total_docs += 1
        relative_path = md_file.relative_to(docs_root)
        
        try:
            with open(md_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"读取文件失败 {md_file}: {e}")
            continue
        
        # 统计信息
        words = len(content.split())
        lines = len(content.splitlines())
        total_words += words
        total_lines += lines
        
        # 分类文档
        doc_type = classify_document(str(relative_path))
        doc_types[doc_type] += 1
        
        # 提取基本信息
        title = extract_title(content)
        status = extract_status(content)
        
        documents.append({
            "path": str(relative_path),
            "title": title,
            "type": doc_type,
            "status": status,
            "words": words,
            "lines": lines,
            "size": md_file.stat().st_size
        })
    
    # 生成报告
    report = generate_report(total_docs, total_words, total_lines, doc_types, documents)
    
    # 保存报告
    with open("simple_doc_index.md", 'w', encoding='utf-8') as f:
        f.write(report)
    
    print(f"文档索引已生成: simple_doc_index.md")
    print(f"总文档数: {total_docs}")
    print(f"总字数: {total_words:,}")
    print(f"总行数: {total_lines:,}")

def classify_document(doc_path):
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

def extract_title(content):
    """提取文档标题"""
    # 从YAML元数据中提取
    yaml_match = re.match(r'^---\n(.*?)\n---\n', content, re.DOTALL)
    if yaml_match:
        yaml_content = yaml_match.group(1)
        for line in yaml_content.split('\n'):
            if line.startswith('title:'):
                return line.split(':', 1)[1].strip().strip('"\'')
    
    # 从第一个标题中提取
    heading_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
    if heading_match:
        return heading_match.group(1).strip()
    
    return "未知标题"

def extract_status(content):
    """提取文档状态"""
    yaml_match = re.match(r'^---\n(.*?)\n---\n', content, re.DOTALL)
    if yaml_match:
        yaml_content = yaml_match.group(1)
        for line in yaml_content.split('\n'):
            if line.startswith('status:'):
                return line.split(':', 1)[1].strip().strip('"\'')
    
    return "未知状态"

def generate_report(total_docs, total_words, total_lines, doc_types, documents):
    """生成报告"""
    report = []
    report.append("# 文档索引报告")
    report.append(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    report.append("")
    
    # 统计信息
    report.append("## 统计信息")
    report.append(f"- 总文档数: {total_docs}")
    report.append(f"- 总字数: {total_words:,}")
    report.append(f"- 总行数: {total_lines:,}")
    report.append(f"- 平均每文档字数: {total_words//total_docs if total_docs > 0 else 0:,}")
    report.append("")
    
    # 文档类型分布
    report.append("## 文档类型分布")
    for doc_type, count in doc_types.items():
        if count > 0:
            percentage = count / total_docs * 100
            report.append(f"- {doc_type}: {count} ({percentage:.1f}%)")
    report.append("")
    
    # 文档列表
    report.append("## 文档列表")
    
    # 按类型分组
    for doc_type in doc_types.keys():
        type_docs = [doc for doc in documents if doc["type"] == doc_type]
        if not type_docs:
            continue
        
        report.append(f"### {doc_type}")
        for doc in sorted(type_docs, key=lambda x: x["words"], reverse=True):
            report.append(f"- **{doc['title']}**")
            report.append(f"  - 路径: `{doc['path']}`")
            report.append(f"  - 状态: {doc['status']}")
            report.append(f"  - 字数: {doc['words']:,}")
            report.append(f"  - 行数: {doc['lines']:,}")
            report.append("")
    
    return "\n".join(report)

if __name__ == "__main__":
    generate_simple_index()
