#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
from pathlib import Path
from datetime import datetime

class DocumentCleaner:
    def __init__(self, docs_dir="docs"):
        self.docs_dir = Path(docs_dir)
        self.cleaned_files = []
        self.removed_files = []
        self.errors = []
        self.templates_dir = self.docs_dir / "templates"
        self.templates_dir.mkdir(exist_ok=True)
    
    def clean_all_documents(self):
        """清理所有文档"""
        print("🧹 开始清理无实质内容的文档...")
        
        # 识别需要清理的文档
        candidates = self.identify_cleanup_candidates()
        
        # 执行清理操作
        self.execute_cleanup(candidates)
        
        # 生成清理报告
        self.generate_cleanup_report()
        
        print(f"✅ 清理完成！处理了 {len(candidates)} 个文档")
    
    def identify_cleanup_candidates(self):
        """识别需要清理的文档"""
        cleanup_candidates = []
        
        for md_file in self.docs_dir.rglob("*.md"):
            try:
                with open(md_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # 检查文档类型
                if self.is_template_document(content):
                    cleanup_candidates.append((md_file, "template", "模板文档"))
                elif self.is_empty_document(content):
                    cleanup_candidates.append((md_file, "empty", "空文档"))
                elif self.is_placeholder_document(content):
                    cleanup_candidates.append((md_file, "placeholder", "占位符文档"))
                elif self.is_duplicate_document(content, md_file):
                    cleanup_candidates.append((md_file, "duplicate", "重复文档"))
                    
            except Exception as e:
                self.errors.append(f"Error processing {md_file}: {e}")
        
        return cleanup_candidates
    
    def is_template_document(self, content):
        """检查是否为模板文档"""
        # 更精确的模板检测逻辑
        template_patterns = [
            r'id:\s*evidence:PLACEHOLDER',  # 证据条目模板
            r'PLACEHOLDER.*?待填写',  # 明确的占位符
            r'模板.*?待补充',  # 模板待补充
            r'示例.*?待填写',  # 示例待填写
        ]
        
        # 检查是否主要是模板结构
        placeholder_count = len(re.findall(r'PLACEHOLDER|待填写|待补充|占位', content, re.IGNORECASE))
        total_lines = len(content.split('\n'))
        
        # 如果占位符数量超过总行数的30%，认为是模板文档
        if placeholder_count > total_lines * 0.3:
            return True
            
        # 检查特定的模板模式
        for pattern in template_patterns:
            if re.search(pattern, content, re.IGNORECASE):
                return True
                
        return False
    
    def is_empty_document(self, content):
        """检查是否为空文档"""
        # 移除空白字符和标题
        clean_content = re.sub(r'^#+\s*.*$', '', content, flags=re.MULTILINE)
        clean_content = re.sub(r'\s+', '', clean_content)
        
        return len(clean_content) < 100
    
    def is_duplicate_document(self, content, file_path):
        """检查是否为重复文档"""
        # 简化的重复检测逻辑
        # 检查是否包含重复的内容模式
        lines = content.split('\n')
        if len(lines) < 10:
            return False
        
        # 检查是否有大量重复的行
        line_counts = {}
        for line in lines:
            line = line.strip()
            if line and len(line) > 10:
                line_counts[line] = line_counts.get(line, 0) + 1
        
        # 如果有超过30%的行是重复的，认为是重复文档
        if line_counts:
            max_repeat = max(line_counts.values())
            if max_repeat > len(lines) * 0.3:
                return True
        
        return False
    
    def is_placeholder_document(self, content):
        """检查是否为占位符文档"""
        placeholder_count = len(re.findall(r'TODO|FIXME|PLACEHOLDER|待办|待补充', content, re.IGNORECASE))
        return placeholder_count > 5
    
    def execute_cleanup(self, candidates):
        """执行清理操作"""
        for file_path, doc_type, description in candidates:
            try:
                print(f"🔧 处理 {doc_type}: {file_path}")
                
                if doc_type == "template":
                    self.handle_template_document(file_path)
                elif doc_type == "empty":
                    self.handle_empty_document(file_path)
                elif doc_type == "duplicate":
                    self.handle_duplicate_document(file_path)
                elif doc_type == "placeholder":
                    self.handle_placeholder_document(file_path)
                    
            except Exception as e:
                self.errors.append(f"Error cleaning {file_path}: {e}")
    
    def handle_template_document(self, file_path):
        """处理模板文档"""
        # 移动到templates目录
        new_path = self.templates_dir / file_path.name
        file_path.rename(new_path)
        self.cleaned_files.append(f"Moved template: {file_path} -> {new_path}")
        print(f"  📁 移动到模板目录: {new_path}")
    
    def handle_empty_document(self, file_path):
        """处理空文档"""
        # 删除空文档
        file_path.unlink()
        self.removed_files.append(f"Removed empty document: {file_path}")
        print(f"  🗑️ 删除空文档: {file_path}")
    
    def handle_duplicate_document(self, file_path):
        """处理重复文档"""
        # 删除重复文档
        file_path.unlink()
        self.removed_files.append(f"Removed duplicate document: {file_path}")
        print(f"  🗑️ 删除重复文档: {file_path}")
    
    def handle_placeholder_document(self, file_path):
        """处理占位符文档"""
        # 尝试修复或删除
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 移除占位符
        cleaned_content = re.sub(r'TODO.*?\n', '', content, flags=re.IGNORECASE)
        cleaned_content = re.sub(r'FIXME.*?\n', '', cleaned_content, flags=re.IGNORECASE)
        cleaned_content = re.sub(r'PLACEHOLDER.*?\n', '', cleaned_content, flags=re.IGNORECASE)
        cleaned_content = re.sub(r'待办.*?\n', '', cleaned_content, flags=re.IGNORECASE)
        cleaned_content = re.sub(r'待补充.*?\n', '', cleaned_content, flags=re.IGNORECASE)
        
        if len(cleaned_content.strip()) > 100:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(cleaned_content)
            self.cleaned_files.append(f"Cleaned placeholder document: {file_path}")
            print(f"  ✨ 清理占位符: {file_path}")
        else:
            file_path.unlink()
            self.removed_files.append(f"Removed placeholder document: {file_path}")
            print(f"  🗑️ 删除占位符文档: {file_path}")
    
    def generate_cleanup_report(self):
        """生成清理报告"""
        report = f"""# 文档清理报告

## 清理概述

- **清理时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
- **清理文件数**: {len(self.cleaned_files)}
- **删除文件数**: {len(self.removed_files)}
- **错误数**: {len(self.errors)}

## 清理文件列表

"""
        
        if self.cleaned_files:
            report += "### 已清理文件\n\n"
            for file_path in self.cleaned_files:
                report += f"- {file_path}\n"
        
        if self.removed_files:
            report += "\n### 已删除文件\n\n"
            for file_path in self.removed_files:
                report += f"- {file_path}\n"
        
        if self.errors:
            report += "\n### 错误列表\n\n"
            for error in self.errors:
                report += f"- {error}\n"
        
        # 保存报告
        report_path = self.docs_dir / "DOCUMENT_CLEANUP_REPORT.md"
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"📄 清理报告已保存到: {report_path}")

def main():
    """主函数"""
    import argparse
    parser = argparse.ArgumentParser(description="Clean up documents with no substantial content.")
    parser.add_argument("--root", type=str, default="docs", help="Root directory to scan for Markdown files.")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be cleaned without actually doing it.")
    args = parser.parse_args()
    
    cleaner = DocumentCleaner(args.root)
    
    if args.dry_run:
        print("🔍 预览模式 - 显示将要清理的文档:")
        candidates = cleaner.identify_cleanup_candidates()
        for file_path, doc_type, description in candidates:
            print(f"  {doc_type}: {file_path}")
        print(f"\n总共找到 {len(candidates)} 个需要清理的文档")
    else:
        cleaner.clean_all_documents()

if __name__ == "__main__":
    main()
