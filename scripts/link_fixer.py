#!/usr/bin/env python3
"""
链接修复器 - 修复文档中的无效链接
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple
import argparse

class LinkFixer:
    def __init__(self, root_dir: str = "docs"):
        self.root_dir = Path(root_dir)
        self.fixed_links = []
        self.failed_fixes = []
        
    def find_markdown_files(self) -> List[Path]:
        """查找所有Markdown文件"""
        markdown_files = []
        for file_path in self.root_dir.rglob("*.md"):
            if file_path.is_file():
                markdown_files.append(file_path)
        return markdown_files
    
    def extract_links_from_file(self, file_path: Path) -> List[Tuple[str, str, int]]:
        """从文件中提取所有链接"""
        links = []
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
                
                # 匹配Markdown链接格式 [text](url)
                link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
                
                for line_num, line in enumerate(lines, 1):
                    matches = re.finditer(link_pattern, line)
                    for match in matches:
                        link_text = match.group(1)
                        link_url = match.group(2)
                        links.append((link_text, link_url, line_num))
                        
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            
        return links
    
    def is_internal_link(self, link_url: str) -> bool:
        """判断是否为内部链接"""
        return not (link_url.startswith('http://') or 
                   link_url.startswith('https://') or 
                   link_url.startswith('mailto:'))
    
    def resolve_internal_link(self, link_url: str, source_file: Path) -> Path:
        """解析内部链接路径"""
        # 移除锚点部分
        clean_url = link_url.split('#')[0]
        
        if clean_url.startswith('/'):
            # 绝对路径
            return self.root_dir / clean_url[1:]
        else:
            # 相对路径
            return source_file.parent / clean_url
    
    def check_internal_link(self, link_url: str, source_file: Path) -> bool:
        """检查内部链接是否存在"""
        target_path = self.resolve_internal_link(link_url, source_file)
        return target_path.exists()
    
    def find_similar_files(self, target_name: str, source_file: Path) -> List[Path]:
        """查找相似的文件名"""
        similar_files = []
        target_lower = target_name.lower()
        
        # 在源文件所在目录查找
        for file_path in source_file.parent.glob("*.md"):
            if target_lower in file_path.name.lower():
                similar_files.append(file_path)
        
        # 在根目录查找
        for file_path in self.root_dir.glob("*.md"):
            if target_lower in file_path.name.lower():
                similar_files.append(file_path)
        
        # 递归查找
        for file_path in self.root_dir.rglob("*.md"):
            if target_lower in file_path.name.lower():
                similar_files.append(file_path)
        
        return similar_files
    
    def suggest_fix(self, link_url: str, source_file: Path) -> str:
        """建议修复方案"""
        # 移除锚点部分
        clean_url = link_url.split('#')[0]
        
        # 提取文件名
        if '/' in clean_url:
            target_name = clean_url.split('/')[-1]
        else:
            target_name = clean_url
        
        # 移除扩展名
        if target_name.endswith('.md'):
            target_name = target_name[:-3]
        
        # 查找相似文件
        similar_files = self.find_similar_files(target_name, source_file)
        
        if similar_files:
            # 选择最相似的文件
            best_match = similar_files[0]
            relative_path = best_match.relative_to(source_file.parent)
            return str(relative_path)
        
        return None
    
    def fix_links_in_file(self, file_path: Path) -> Dict:
        """修复文件中的无效链接"""
        results = {
            'file': str(file_path),
            'total_links': 0,
            'fixed_links': 0,
            'failed_fixes': 0,
            'fixes': []
        }
        
        links = self.extract_links_from_file(file_path)
        internal_links = [(text, url, line) for text, url, line in links if self.is_internal_link(url)]
        results['total_links'] = len(internal_links)
        
        # 读取文件内容
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            return results
        
        # 修复无效链接
        for link_text, link_url, line_num in internal_links:
            if not self.check_internal_link(link_url, file_path):
                suggested_fix = self.suggest_fix(link_url, file_path)
                if suggested_fix:
                    # 修复链接
                    old_link = f"[{link_text}]({link_url})"
                    new_link = f"[{link_text}]({suggested_fix})"
                    content = content.replace(old_link, new_link)
                    
                    results['fixed_links'] += 1
                    results['fixes'].append({
                        'line': line_num,
                        'old': old_link,
                        'new': new_link
                    })
                    self.fixed_links.append({
                        'file': str(file_path),
                        'line': line_num,
                        'old': old_link,
                        'new': new_link
                    })
                else:
                    results['failed_fixes'] += 1
                    self.failed_fixes.append({
                        'file': str(file_path),
                        'line': line_num,
                        'link': f"[{link_text}]({link_url})"
                    })
        
        # 保存修复后的文件
        if results['fixed_links'] > 0:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                print(f"✅ {file_path.name}: 修复了 {results['fixed_links']} 个链接")
            except Exception as e:
                print(f"❌ 保存文件 {file_path} 时出错: {e}")
        
        return results
    
    def fix_all_links(self) -> Dict:
        """修复所有文档中的无效链接"""
        print("🔧 开始修复所有文档中的无效链接...")
        
        markdown_files = self.find_markdown_files()
        print(f"📁 找到 {len(markdown_files)} 个Markdown文件")
        
        all_results = {
            'total_files': len(markdown_files),
            'total_links': 0,
            'fixed_links': 0,
            'failed_fixes': 0,
            'file_results': []
        }
        
        # 逐个处理文件
        for i, file_path in enumerate(markdown_files, 1):
            print(f"📄 处理文件 {i}/{len(markdown_files)}: {file_path.name}")
            
            try:
                result = self.fix_links_in_file(file_path)
                all_results['file_results'].append(result)
                
                all_results['total_links'] += result['total_links']
                all_results['fixed_links'] += result['fixed_links']
                all_results['failed_fixes'] += result['failed_fixes']
                    
            except Exception as e:
                print(f"❌ 处理 {file_path} 时出错: {e}")
        
        return all_results
    
    def generate_report(self, results: Dict) -> str:
        """生成修复报告"""
        report = []
        report.append("# 🔧 链接修复报告")
        report.append("")
        
        # 总体统计
        report.append("## 📊 总体统计")
        report.append("")
        report.append(f"- **总文件数**: {results['total_files']}")
        report.append(f"- **总链接数**: {results['total_links']}")
        report.append(f"- **修复链接数**: {results['fixed_links']}")
        report.append(f"- **修复失败数**: {results['failed_fixes']}")
        report.append("")
        
        # 修复统计
        if results['total_links'] > 0:
            fix_rate = (results['fixed_links'] / results['total_links']) * 100
            report.append(f"- **修复成功率**: {fix_rate:.1f}%")
        report.append("")
        
        # 按文件分类的详细结果
        report.append("## 📋 按文件分类的详细结果")
        report.append("")
        
        for file_result in results['file_results']:
            if file_result['fixed_links'] > 0 or file_result['failed_fixes'] > 0:
                report.append(f"### {file_result['file']}")
                report.append("")
                report.append(f"- **总链接数**: {file_result['total_links']}")
                report.append(f"- **修复链接数**: {file_result['fixed_links']}")
                report.append(f"- **修复失败数**: {file_result['failed_fixes']}")
                report.append("")
                
                if file_result['fixes']:
                    report.append("**修复的链接**:")
                    for fix in file_result['fixes']:
                        report.append(f"- 第{fix['line']}行: {fix['old']} → {fix['new']}")
                    report.append("")
        
        # 修复失败汇总
        if self.failed_fixes:
            report.append("## 🚨 修复失败汇总")
            report.append("")
            
            for failed_fix in self.failed_fixes:
                report.append(f"- [{failed_fix['file']}]({failed_fix['file']}) 第{failed_fix['line']}行: {failed_fix['link']}")
            report.append("")
        
        return "\n".join(report)
    
    def save_report(self, results: Dict, output_file: str = "link_fix_report.md"):
        """保存修复报告"""
        report = self.generate_report(results)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"📄 修复报告已保存到: {output_file}")

def main():
    parser = argparse.ArgumentParser(description='修复文档中的无效链接')
    parser.add_argument('--root', default='docs', help='文档根目录 (默认: docs)')
    parser.add_argument('--output', default='link_fix_report.md', help='输出报告文件')
    
    args = parser.parse_args()
    
    fixer = LinkFixer(args.root)
    results = fixer.fix_all_links()
    fixer.save_report(results, args.output)
    
    # 打印简要统计
    print("\n" + "="*50)
    print("📊 修复完成统计:")
    print(f"总文件数: {results['total_files']}")
    print(f"总链接数: {results['total_links']}")
    print(f"修复链接数: {results['fixed_links']}")
    print(f"修复失败数: {results['failed_fixes']}")
    
    if results['total_links'] > 0:
        fix_rate = (results['fixed_links'] / results['total_links']) * 100
        print(f"修复成功率: {fix_rate:.1f}%")
    
    if results['fixed_links'] > 0:
        print(f"\n✅ 成功修复了 {results['fixed_links']} 个链接！")
    
    if results['failed_fixes'] > 0:
        print(f"\n⚠️  有 {results['failed_fixes']} 个链接修复失败，请查看详细报告")
        return 1
    else:
        print("\n🎉 所有链接修复完成！")
        return 0

if __name__ == "__main__":
    sys.exit(main())
