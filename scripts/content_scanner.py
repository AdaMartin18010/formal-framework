#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework 内容扫描与空白检测脚本

功能：
1. 扫描所有模型目录，检测缺失的 dsl-draft.md 和 theory.md 文件
2. 检测文档内容空白和薄弱点
3. 生成内容补全任务清单
4. 支持自动化生成基础模板

使用方法：
python scripts/content_scanner.py
"""

import os
import json
import re
from pathlib import Path
from typing import Dict, List, Set, Tuple

class ContentScanner:
    def __init__(self, root_dir: str = "docs"):
        self.root_dir = Path(root_dir)
        self.missing_files = []
        self.empty_files = []
        self.weak_content = []
        
    def scan_missing_files(self) -> List[str]:
        """扫描缺失的 dsl-draft.md 和 theory.md 文件"""
        missing = []
        
        # 扫描 formal-model 目录
        formal_model_dir = self.root_dir / "formal-model"
        if formal_model_dir.exists():
            missing.extend(self._scan_model_directory(formal_model_dir))
            
        # 扫描 industry-model 目录
        industry_model_dir = self.root_dir / "industry-model"
        if industry_model_dir.exists():
            missing.extend(self._scan_model_directory(industry_model_dir))
            
        self.missing_files = missing
        return missing
    
    def _scan_model_directory(self, model_dir: Path) -> List[str]:
        """扫描模型目录下的缺失文件"""
        missing = []
        
        for item in model_dir.rglob("*"):
            if item.is_dir():
                # 检查是否应该有 dsl-draft.md 和 theory.md
                dsl_file = item / "dsl-draft.md"
                theory_file = item / "theory.md"
                
                # 如果目录包含其他 .md 文件，说明这是一个模型目录
                has_md_files = any(item.glob("*.md"))
                
                if has_md_files:
                    if not dsl_file.exists():
                        missing.append(str(dsl_file))
                    if not theory_file.exists():
                        missing.append(str(theory_file))
        
        return missing
    
    def scan_empty_content(self) -> List[Dict]:
        """扫描内容空白的文件"""
        empty_files = []
        
        for md_file in self.root_dir.rglob("*.md"):
            if md_file.name in ["dsl-draft.md", "theory.md"]:
                try:
                    with open(md_file, 'r', encoding='utf-8') as f:
                        content = f.read().strip()
                    
                    # 检查内容是否为空或只有标题
                    if not content or len(content) < 100:
                        empty_files.append({
                            "file": str(md_file),
                            "size": len(content),
                            "type": "empty" if not content else "weak"
                        })
                except Exception as e:
                    print(f"Error reading {md_file}: {e}")
        
        self.empty_files = empty_files
        return empty_files
    
    def scan_weak_content(self) -> List[Dict]:
        """扫描内容薄弱的文件"""
        weak_files = []
        
        for md_file in self.root_dir.rglob("*.md"):
            if md_file.name in ["dsl-draft.md", "theory.md"]:
                try:
                    with open(md_file, 'r', encoding='utf-8') as f:
                        content = f.read()
                    
                    # 检查是否包含关键内容
                    has_dsl = "dsl" in content.lower() or "yaml" in content.lower()
                    has_theory = "理论" in content or "theory" in content.lower()
                    has_example = "示例" in content or "example" in content.lower()
                    has_code = "```" in content
                    
                    if not (has_dsl or has_theory or has_example or has_code):
                        weak_files.append({
                            "file": str(md_file),
                            "missing": {
                                "dsl": not has_dsl,
                                "theory": not has_theory,
                                "example": not has_example,
                                "code": not has_code
                            }
                        })
                except Exception as e:
                    print(f"Error reading {md_file}: {e}")
        
        self.weak_content = weak_files
        return weak_files
    
    def generate_tasks(self) -> List[Dict]:
        """生成内容补全任务"""
        tasks = []
        
        # 为缺失文件生成任务
        for file_path in self.missing_files:
            relative_path = Path(file_path).relative_to(self.root_dir)
            model_name = relative_path.parent.name
            file_type = "DSL草案" if "dsl-draft" in file_path else "理论说明"
            
            tasks.append({
                "type": "missing_file",
                "priority": "high",
                "target": f"创建 {relative_path}",
                "description": f"为 {model_name} 模型创建 {file_type}",
                "file_path": file_path,
                "template": "dsl_draft" if "dsl-draft" in file_path else "theory"
            })
        
        # 为空白文件生成任务
        for file_info in self.empty_files:
            relative_path = Path(file_info["file"]).relative_to(self.root_dir)
            model_name = relative_path.parent.name
            
            tasks.append({
                "type": "empty_content",
                "priority": "high",
                "target": f"补充 {relative_path} 内容",
                "description": f"为 {model_name} 模型补充 {file_info['type']} 内容",
                "file_path": file_info["file"],
                "template": "dsl_draft" if "dsl-draft" in file_info["file"] else "theory"
            })
        
        # 为薄弱内容生成任务
        for file_info in self.weak_content:
            relative_path = Path(file_info["file"]).relative_to(self.root_dir)
            model_name = relative_path.parent.name
            missing_items = [k for k, v in file_info["missing"].items() if v]
            
            tasks.append({
                "type": "weak_content",
                "priority": "medium",
                "target": f"完善 {relative_path} 内容",
                "description": f"为 {model_name} 模型补充缺失内容: {', '.join(missing_items)}",
                "file_path": file_info["file"],
                "missing_items": missing_items
            })
        
        return tasks
    
    def generate_report(self) -> Dict:
        """生成扫描报告"""
        return {
            "scan_time": str(Path.cwd()),
            "missing_files": len(self.missing_files),
            "empty_files": len(self.empty_files),
            "weak_content": len(self.weak_content),
            "total_tasks": len(self.generate_tasks()),
            "details": {
                "missing_files": self.missing_files,
                "empty_files": self.empty_files,
                "weak_content": self.weak_content,
                "tasks": self.generate_tasks()
            }
        }
    
    def save_report(self, output_file: str = "content_gap_report.json"):
        """保存扫描报告"""
        report = self.generate_report()
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        print(f"报告已保存到: {output_file}")
    
    def generate_template(self, template_type: str, model_name: str) -> str:
        """生成基础模板"""
        if template_type == "dsl_draft":
            return f"""# {model_name} DSL 草案

## 1. 结构定义

```yaml
# {model_name} 模型结构
{model_name.lower()}:
  # 顶层对象定义
  # 子对象/递归结构
```

## 2. 字段说明

- 字段1：类型、约束、说明
- 字段2：类型、约束、说明

## 3. 示例

```yaml
# {model_name} 示例
```

## 4. 自动化推理伪代码

```python
def generate_{model_name.lower()}_code(model):
    # 伪代码内容
    pass
```

## 5. 行业映射

- 通用模型映射
- 行业特定扩展
- 最佳实践案例

---
"""
        elif template_type == "theory":
            return f"""# {model_name} 理论说明

## 1. 递归建模思想

- 递归分层、组合、映射
- AST结构与类型推理
- 自动化校验与补偿机制

## 2. 行业映射关系

- 通用模型 → 行业模型
- 最佳实践与案例
- 自动化推理流程

## 3. 推理与自动化生成流程

- 步骤1：模型定义
- 步骤2：类型推理
- 步骤3：代码生成
- 步骤4：验证测试

## 4. 典型案例

- 案例描述
- 伪代码/流程图
- 行业应用

## 5. 最佳实践与常见陷阱

- 实践建议
- 常见误区
- 解决方案

---
"""
        else:
            return ""

def main():
    """主函数"""
    print("开始扫描 Formal Framework 内容...")
    
    scanner = ContentScanner()
    
    # 扫描缺失文件
    print("扫描缺失文件...")
    missing_files = scanner.scan_missing_files()
    print(f"发现 {len(missing_files)} 个缺失文件")
    
    # 扫描空白内容
    print("扫描空白内容...")
    empty_files = scanner.scan_empty_content()
    print(f"发现 {len(empty_files)} 个空白/薄弱文件")
    
    # 扫描薄弱内容
    print("扫描薄弱内容...")
    weak_content = scanner.scan_weak_content()
    print(f"发现 {len(weak_content)} 个内容薄弱文件")
    
    # 生成任务
    tasks = scanner.generate_tasks()
    print(f"生成 {len(tasks)} 个补全任务")
    
    # 保存报告
    scanner.save_report()
    
    # 打印任务摘要
    print("\n=== 任务摘要 ===")
    for i, task in enumerate(tasks[:10], 1):  # 只显示前10个任务
        print(f"{i}. {task['target']} ({task['priority']})")
    
    if len(tasks) > 10:
        print(f"... 还有 {len(tasks) - 10} 个任务")
    
    print("\n扫描完成！详细报告请查看 content_gap_report.json")

if __name__ == "__main__":
    main() 