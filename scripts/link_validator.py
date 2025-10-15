#!/usr/bin/env python3
"""
链接验证器 - 验证所有文档中的链接有效性
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple, Set
import argparse
from urllib.parse import urlparse
import requests
from concurrent.futures import ThreadPoolExecutor, as_completed
import time

class LinkValidator:
    def __init__(self, root_dir: str = "docs"):
        self.root_dir = Path(root_dir)
        self.broken_links = []
        self.valid_links = []
        self.external_links = []
        self.internal_links = []
        self.anchor_links = []
        
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
    
    def classify_link(self, link_url: str, source_file: Path) -> str:
        """分类链接类型"""
        if link_url.startswith('http://') or link_url.startswith('https://'):
            return 'external'
        elif link_url.startswith('#'):
            return 'anchor'
        elif link_url.startswith('mailto:'):
            return 'email'
        else:
            return 'internal'
    
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
    
    def check_anchor_link(self, link_url: str, source_file: Path) -> bool:
        """检查锚点链接是否存在"""
        if not link_url.startswith('#'):
            return False
            
        anchor = link_url[1:]
        target_path = self.resolve_internal_link(link_url, source_file)
        
        if not target_path.exists():
            return False
            
        try:
            with open(target_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
                # 检查标题锚点
                title_pattern = rf'^#+\s+{re.escape(anchor)}$'
                if re.search(title_pattern, content, re.MULTILINE):
                    return True
                    
                # 检查HTML锚点
                html_anchor_pattern = rf'<[^>]+id=["\']{re.escape(anchor)}["\'][^>]*>'
                if re.search(html_anchor_pattern, content):
                    return True
                    
                # 检查通用锚点格式
                generic_anchor_pattern = rf'<a[^>]+name=["\']{re.escape(anchor)}["\'][^>]*>'
                if re.search(generic_anchor_pattern, content):
                    return True
                    
        except Exception as e:
            print(f"Error checking anchor in {target_path}: {e}")
            
        return False
    
    def check_external_link(self, url: str) -> bool:
        """检查外部链接是否可访问"""
        try:
            response = requests.head(url, timeout=10, allow_redirects=True)
            return response.status_code < 400
        except:
            try:
                response = requests.get(url, timeout=10, allow_redirects=True)
                return response.status_code < 400
            except:
                return False
    
    def validate_links_in_file(self, file_path: Path) -> Dict:
        """验证文件中的所有链接"""
        results = {
            'file': str(file_path),
            'total_links': 0,
            'valid_links': 0,
            'broken_links': [],
            'external_links': [],
            'internal_links': [],
            'anchor_links': []
        }
        
        links = self.extract_links_from_file(file_path)
        results['total_links'] = len(links)
        
        for link_text, link_url, line_num in links:
            link_type = self.classify_link(link_url, file_path)
            link_info = {
                'text': link_text,
                'url': link_url,
                'line': line_num,
                'type': link_type
            }
            
            is_valid = False
            
            if link_type == 'external':
                results['external_links'].append(link_info)
                is_valid = self.check_external_link(link_url)
            elif link_type == 'internal':
                results['internal_links'].append(link_info)
                is_valid = self.check_internal_link(link_url, file_path)
            elif link_type == 'anchor':
                results['anchor_links'].append(link_info)
                is_valid = self.check_anchor_link(link_url, file_path)
            elif link_type == 'email':
                is_valid = True  # 邮件链接通常有效
            
            if is_valid:
                results['valid_links'] += 1
                self.valid_links.append(link_info)
            else:
                results['broken_links'].append(link_info)
                self.broken_links.append(link_info)
        
        return results
    
    def validate_all_links(self, max_workers: int = 10) -> Dict:
        """验证所有文档中的链接"""
        print("🔍 开始验证所有文档中的链接...")
        
        markdown_files = self.find_markdown_files()
        print(f"📁 找到 {len(markdown_files)} 个Markdown文件")
        
        all_results = {
            'total_files': len(markdown_files),
            'total_links': 0,
            'valid_links': 0,
            'broken_links': 0,
            'external_links': 0,
            'internal_links': 0,
            'anchor_links': 0,
            'file_results': []
        }
        
        # 使用线程池并行处理
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            future_to_file = {
                executor.submit(self.validate_links_in_file, file_path): file_path 
                for file_path in markdown_files
            }
            
            for future in as_completed(future_to_file):
                file_path = future_to_file[future]
                try:
                    result = future.result()
                    all_results['file_results'].append(result)
                    
                    all_results['total_links'] += result['total_links']
                    all_results['valid_links'] += result['valid_links']
                    all_results['broken_links'] += len(result['broken_links'])
                    all_results['external_links'] += len(result['external_links'])
                    all_results['internal_links'] += len(result['internal_links'])
                    all_results['anchor_links'] += len(result['anchor_links'])
                    
                    print(f"✅ {file_path.name}: {result['valid_links']}/{result['total_links']} 链接有效")
                    
                except Exception as e:
                    print(f"❌ 处理 {file_path} 时出错: {e}")
        
        return all_results
    
    def generate_report(self, results: Dict) -> str:
        """生成验证报告"""
        report = []
        report.append("# 🔗 链接验证报告")
        report.append("")
        report.append(f"**验证时间**: {time.strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("")
        
        # 总体统计
        report.append("## 📊 总体统计")
        report.append("")
        report.append(f"- **总文件数**: {results['total_files']}")
        report.append(f"- **总链接数**: {results['total_links']}")
        report.append(f"- **有效链接数**: {results['valid_links']}")
        report.append(f"- **无效链接数**: {results['broken_links']}")
        report.append(f"- **外部链接数**: {results['external_links']}")
        report.append(f"- **内部链接数**: {results['internal_links']}")
        report.append(f"- **锚点链接数**: {results['anchor_links']}")
        report.append("")
        
        # 有效性统计
        if results['total_links'] > 0:
            validity_rate = (results['valid_links'] / results['total_links']) * 100
            report.append(f"- **链接有效性**: {validity_rate:.1f}%")
        report.append("")
        
        # 按文件分类的详细结果
        report.append("## 📋 按文件分类的详细结果")
        report.append("")
        
        for file_result in results['file_results']:
            if file_result['broken_links']:
                report.append(f"### ❌ {file_result['file']}")
                report.append("")
                report.append(f"- **总链接数**: {file_result['total_links']}")
                report.append(f"- **有效链接数**: {file_result['valid_links']}")
                report.append(f"- **无效链接数**: {len(file_result['broken_links'])}")
                report.append("")
                
                report.append("**无效链接**:")
                for broken_link in file_result['broken_links']:
                    report.append(f"- 第{broken_link['line']}行: [{broken_link['text']}]({broken_link['url']}) ({broken_link['type']})")
                report.append("")
        
        # 无效链接汇总
        if self.broken_links:
            report.append("## 🚨 无效链接汇总")
            report.append("")
            
            # 按类型分组
            by_type = {}
            for link in self.broken_links:
                link_type = link['type']
                if link_type not in by_type:
                    by_type[link_type] = []
                by_type[link_type].append(link)
            
            for link_type, links in by_type.items():
                report.append(f"### {link_type.upper()} 链接")
                report.append("")
                for link in links:
                    report.append(f"- [{link['text']}]({link['url']}) (第{link['line']}行)")
                report.append("")
        
        return "\n".join(report)
    
    def save_report(self, results: Dict, output_file: str = "link_validation_report.md"):
        """保存验证报告"""
        report = self.generate_report(results)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"📄 验证报告已保存到: {output_file}")

def main():
    parser = argparse.ArgumentParser(description='验证文档中的链接有效性')
    parser.add_argument('--root', default='docs', help='文档根目录 (默认: docs)')
    parser.add_argument('--output', default='link_validation_report.md', help='输出报告文件')
    parser.add_argument('--workers', type=int, default=10, help='并发工作线程数')
    
    args = parser.parse_args()
    
    validator = LinkValidator(args.root)
    results = validator.validate_all_links(args.workers)
    validator.save_report(results, args.output)
    
    # 打印简要统计
    print("\n" + "="*50)
    print("📊 验证完成统计:")
    print(f"总文件数: {results['total_files']}")
    print(f"总链接数: {results['total_links']}")
    print(f"有效链接数: {results['valid_links']}")
    print(f"无效链接数: {results['broken_links']}")
    
    if results['total_links'] > 0:
        validity_rate = (results['valid_links'] / results['total_links']) * 100
        print(f"链接有效性: {validity_rate:.1f}%")
    
    if results['broken_links'] > 0:
        print(f"\n⚠️  发现 {results['broken_links']} 个无效链接，请查看详细报告")
        sys.exit(1)
    else:
        print("\n✅ 所有链接都有效！")
        sys.exit(0)

if __name__ == "__main__":
    main()
