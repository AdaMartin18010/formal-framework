#!/usr/bin/env python3
"""
内部链接检查器 - 专门检查内部链接的有效性
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple
import argparse

class InternalLinkChecker:
    def __init__(self, root_dir: str = "docs"):
        self.root_dir = Path(root_dir)
        self.broken_links = []
        self.valid_links = []
        
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
    
    def validate_links_in_file(self, file_path: Path) -> Dict:
        """验证文件中的所有内部链接"""
        results = {
            'file': str(file_path),
            'total_internal_links': 0,
            'valid_links': 0,
            'broken_links': []
        }
        
        links = self.extract_links_from_file(file_path)
        internal_links = [(text, url, line) for text, url, line in links if self.is_internal_link(url)]
        results['total_internal_links'] = len(internal_links)
        
        for link_text, link_url, line_num in internal_links:
            link_info = {
                'text': link_text,
                'url': link_url,
                'line': line_num
            }
            
            if self.check_internal_link(link_url, file_path):
                results['valid_links'] += 1
                self.valid_links.append(link_info)
            else:
                results['broken_links'].append(link_info)
                self.broken_links.append(link_info)
        
        return results
    
    def validate_all_links(self) -> Dict:
        """验证所有文档中的内部链接"""
        print("🔍 开始验证所有文档中的内部链接...")
        
        markdown_files = self.find_markdown_files()
        print(f"📁 找到 {len(markdown_files)} 个Markdown文件")
        
        all_results = {
            'total_files': len(markdown_files),
            'total_internal_links': 0,
            'valid_links': 0,
            'broken_links': 0,
            'file_results': []
        }
        
        # 逐个处理文件
        for i, file_path in enumerate(markdown_files, 1):
            print(f"📄 处理文件 {i}/{len(markdown_files)}: {file_path.name}")
            
            try:
                result = self.validate_links_in_file(file_path)
                all_results['file_results'].append(result)
                
                all_results['total_internal_links'] += result['total_internal_links']
                all_results['valid_links'] += result['valid_links']
                all_results['broken_links'] += len(result['broken_links'])
                
                if result['broken_links']:
                    print(f"❌ {file_path.name}: {result['valid_links']}/{result['total_internal_links']} 内部链接有效 ({len(result['broken_links'])} 个无效)")
                else:
                    print(f"✅ {file_path.name}: {result['valid_links']}/{result['total_internal_links']} 内部链接有效")
                    
            except Exception as e:
                print(f"❌ 处理 {file_path} 时出错: {e}")
        
        return all_results
    
    def generate_report(self, results: Dict) -> str:
        """生成验证报告"""
        report = []
        report.append("# 🔗 内部链接验证报告")
        report.append("")
        
        # 总体统计
        report.append("## 📊 总体统计")
        report.append("")
        report.append(f"- **总文件数**: {results['total_files']}")
        report.append(f"- **总内部链接数**: {results['total_internal_links']}")
        report.append(f"- **有效链接数**: {results['valid_links']}")
        report.append(f"- **无效链接数**: {results['broken_links']}")
        report.append("")
        
        # 有效性统计
        if results['total_internal_links'] > 0:
            validity_rate = (results['valid_links'] / results['total_internal_links']) * 100
            report.append(f"- **链接有效性**: {validity_rate:.1f}%")
        report.append("")
        
        # 按文件分类的详细结果
        report.append("## 📋 按文件分类的详细结果")
        report.append("")
        
        for file_result in results['file_results']:
            if file_result['broken_links']:
                report.append(f"### ❌ {file_result['file']}")
                report.append("")
                report.append(f"- **总内部链接数**: {file_result['total_internal_links']}")
                report.append(f"- **有效链接数**: {file_result['valid_links']}")
                report.append(f"- **无效链接数**: {len(file_result['broken_links'])}")
                report.append("")
                
                report.append("**无效链接**:")
                for broken_link in file_result['broken_links']:
                    report.append(f"- 第{broken_link['line']}行: [{broken_link['text']}]({broken_link['url']})")
                report.append("")
        
        # 无效链接汇总
        if self.broken_links:
            report.append("## 🚨 无效链接汇总")
            report.append("")
            
            for link in self.broken_links:
                report.append(f"- [{link['text']}]({link['url']}) (第{link['line']}行)")
            report.append("")
        
        return "\n".join(report)
    
    def save_report(self, results: Dict, output_file: str = "internal_link_validation_report.md"):
        """保存验证报告"""
        report = self.generate_report(results)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"📄 验证报告已保存到: {output_file}")

def main():
    parser = argparse.ArgumentParser(description='验证文档中的内部链接有效性')
    parser.add_argument('--root', default='docs', help='文档根目录 (默认: docs)')
    parser.add_argument('--output', default='internal_link_validation_report.md', help='输出报告文件')
    
    args = parser.parse_args()
    
    checker = InternalLinkChecker(args.root)
    results = checker.validate_all_links()
    checker.save_report(results, args.output)
    
    # 打印简要统计
    print("\n" + "="*50)
    print("📊 验证完成统计:")
    print(f"总文件数: {results['total_files']}")
    print(f"总内部链接数: {results['total_internal_links']}")
    print(f"有效链接数: {results['valid_links']}")
    print(f"无效链接数: {results['broken_links']}")
    
    if results['total_internal_links'] > 0:
        validity_rate = (results['valid_links'] / results['total_internal_links']) * 100
        print(f"链接有效性: {validity_rate:.1f}%")
    
    if results['broken_links'] > 0:
        print(f"\n⚠️  发现 {results['broken_links']} 个无效内部链接，请查看详细报告")
        return 1
    else:
        print("\n✅ 所有内部链接都有效！")
        return 0

if __name__ == "__main__":
    sys.exit(main())
