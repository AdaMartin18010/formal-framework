#!/usr/bin/env python3
"""
快速文档检查脚本
用于快速检查文档的基本完成度
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple

def check_document_quick(file_path: Path) -> Dict:
    """快速检查单个文档"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return {
            "file": str(file_path),
            "status": "ERROR",
            "error": str(e)
        }
    
    # 基本信息
    word_count = len(content.split())
    line_count = len(content.splitlines())
    
    # 检查问题
    issues = []
    problem_keywords = ["TODO", "FIXME", "占位", "placeholder", "待补充", "待完善"]
    for keyword in problem_keywords:
        if keyword in content:
            issues.append(keyword)
    
    # 检查质量指标
    has_references = any(kw in content for kw in ["参考文献", "References", "引用"])
    has_examples = any(kw in content for kw in ["示例", "Example", "案例"])
    has_dsl = "DSL" in content or "dsl" in content
    has_theory = any(kw in content for kw in ["理论", "Theory", "形式化"])
    
    # 检查必需章节
    required_sections = ["概述", "理论基础", "核心结构", "形式化规范"]
    missing_sections = [s for s in required_sections if s not in content]
    
    # 计算完成度
    completeness = 0.0
    if word_count > 1000:
        completeness += 0.3
    elif word_count > 500:
        completeness += 0.2
    elif word_count > 200:
        completeness += 0.1
    
    if not issues:
        completeness += 0.2
    elif len(issues) <= 2:
        completeness += 0.1
    
    quality_score = sum([has_references, has_examples, has_dsl, has_theory]) / 4
    completeness += quality_score * 0.3
    
    section_score = (len(required_sections) - len(missing_sections)) / len(required_sections)
    completeness += section_score * 0.2
    
    # 确定状态
    if completeness >= 0.8 and not issues:
        status = "FINAL"
    elif completeness >= 0.6:
        status = "RC"
    else:
        status = "DRAFT"
    
    return {
        "file": str(file_path),
        "status": status,
        "completeness": round(completeness, 2),
        "word_count": word_count,
        "line_count": line_count,
        "issues": issues,
        "missing_sections": missing_sections,
        "has_references": has_references,
        "has_examples": has_examples,
        "has_dsl": has_dsl,
        "has_theory": has_theory
    }

def main():
    """主函数"""
    docs_root = Path("docs")
    
    if not docs_root.exists():
        print(f"错误: 文档目录 {docs_root} 不存在")
        return
    
    print("快速文档检查...")
    print("=" * 60)
    
    results = []
    
    # 检查所有markdown文件
    for md_file in docs_root.rglob("*.md"):
        if md_file.name.startswith("."):
            continue
        
        result = check_document_quick(md_file)
        results.append(result)
    
    # 按状态分组
    status_groups = {}
    for result in results:
        status = result["status"]
        if status not in status_groups:
            status_groups[status] = []
        status_groups[status].append(result)
    
    # 打印结果
    total_docs = len(results)
    avg_completeness = sum(r["completeness"] for r in results) / total_docs
    
    print(f"总文档数: {total_docs}")
    print(f"平均完成度: {avg_completeness:.1%}")
    print()
    
    for status in ["FINAL", "RC", "DRAFT", "ERROR"]:
        if status not in status_groups:
            continue
        
        docs = status_groups[status]
        print(f"{status} 状态 ({len(docs)}个):")
        
        for doc in sorted(docs, key=lambda x: x["completeness"], reverse=True):
            print(f"  {doc['file']}")
            print(f"    完成度: {doc['completeness']:.1%}, 字数: {doc['word_count']}")
            
            if doc["issues"]:
                print(f"    问题: {', '.join(doc['issues'])}")
            
            if doc["missing_sections"]:
                print(f"    缺失章节: {', '.join(doc['missing_sections'])}")
            
            quality_items = []
            if doc["has_references"]:
                quality_items.append("参考文献")
            if doc["has_examples"]:
                quality_items.append("示例")
            if doc["has_dsl"]:
                quality_items.append("DSL")
            if doc["has_theory"]:
                quality_items.append("理论")
            
            if quality_items:
                print(f"    质量指标: {', '.join(quality_items)}")
            
            print()
    
    # 统计信息
    print("=" * 60)
    print("统计信息:")
    
    for status, docs in status_groups.items():
        percentage = len(docs) / total_docs * 100
        print(f"  {status}: {len(docs)} ({percentage:.1f}%)")
    
    # 问题文档
    problem_docs = [r for r in results if r["issues"] or r["completeness"] < 0.6]
    if problem_docs:
        print(f"\n需要关注的文档 ({len(problem_docs)}个):")
        for doc in sorted(problem_docs, key=lambda x: x["completeness"]):
            print(f"  {doc['file']} (完成度: {doc['completeness']:.1%})")

if __name__ == "__main__":
    main()
