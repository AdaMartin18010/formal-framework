# 交叉引用优化指南 (Cross-Reference Enhancement Guide)

## 概述

本文档提供交叉引用系统的优化指南，确保所有文档的相关概念部分都采用统一的三分类格式。

## 标准格式

所有文档的"相关概念"部分应遵循以下格式：

```markdown
## 相关概念

### 核心概念关联

- [概念A](./concept-a.md) - 提供理论基础，是当前概念的形式化基础
- [概念B](./concept-b.md) - 相关理论，用于解决相似问题

### 应用领域关联

- [领域模型X](../domain-models/model-x.md) - 应用当前概念的具体领域
- [行业案例Y](../industry-model/industry-y.md) - 实际应用案例

### 行业应用关联

- [云原生架构](../industry-model/cloud-native-architecture/) - 在云原生中的应用
- [金融架构](../industry-model/finance-architecture/) - 在金融系统中的应用
```

## 分类说明

### 核心概念关联

**定义**：与当前概念在理论层面直接相关的基础概念。

**特点**：
- 提供理论基础
- 是当前概念的前置知识
- 属于同一理论体系

**示例**：
- 形式化建模 → 形式化验证（理论基础）
- 抽象语法树 → 代码生成（数据结构基础）

### 应用领域关联

**定义**：在当前概念的应用领域中使用的相关模型或方法。

**特点**：
- 属于同一应用领域
- 解决相关问题
- 可以组合使用

**示例**：
- 数据模型 → 功能模型（都在系统建模领域）
- 交互模型 → 运行时模型（都在系统架构领域）

### 行业应用关联

**定义**：当前概念在具体行业中的实际应用。

**特点**：
- 具体的行业案例
- 实际应用场景
- 行业特定实践

**示例**：
- 形式化验证 → 金融架构（金融系统验证）
- 时序逻辑 → IoT架构（实时系统验证）

## 优化检查清单

### 文档检查

- [ ] 是否有"相关概念"部分？
- [ ] 是否分为三个子分类？
- [ ] 每个链接是否有说明文字？
- [ ] 链接路径是否正确？
- [ ] 分类是否准确？

### 内容检查

- [ ] 核心概念关联是否包含理论基础？
- [ ] 应用领域关联是否包含相关模型？
- [ ] 行业应用关联是否包含实际案例？
- [ ] 说明文字是否清晰准确？

## 批量更新脚本

可以使用以下Python脚本批量更新文档：

```python
#!/usr/bin/env python3
import re
import os
from pathlib import Path

def update_cross_references(doc_path):
    """更新文档的交叉引用部分"""
    with open(doc_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 检查是否已有三分类格式
    if "### 核心概念关联" in content and "### 应用领域关联" in content:
        return False  # 已更新
    
    # 查找相关概念部分
    pattern = r'## 相关概念\n\n(.*?)(?=\n## |$)'
    match = re.search(pattern, content, re.DOTALL)
    
    if match:
        # 替换为三分类格式
        new_section = """## 相关概念

### 核心概念关联

- [相关概念1](./related-concept1.md) - 提供理论基础，是当前概念的形式化基础
- [相关概念2](./related-concept2.md) - 相关理论，用于解决相似问题

### 应用领域关联

- [领域模型X](../domain-models/model-x.md) - 应用当前概念的具体领域
- [行业案例Y](../industry-model/industry-y.md) - 实际应用案例

### 行业应用关联

- [云原生架构](../industry-model/cloud-native-architecture/) - 在云原生中的应用
- [金融架构](../industry-model/finance-architecture/) - 在金融系统中的应用"""
        
        content = content[:match.start()] + new_section + content[match.end():]
        
        with open(doc_path, 'w', encoding='utf-8') as f:
            f.write(content)
        return True
    
    return False

# 批量处理
docs_dir = Path('docs/formal-model/core-concepts')
for md_file in docs_dir.glob('*.md'):
    if update_cross_references(md_file):
        print(f"Updated: {md_file}")
```

## 相关文档

- [概念索引](./concept-index/CONCEPT_INDEX.md)
- [概念关系图谱](./concept-maps/CONCEPT_MAPS.md)
- [术语表](./glossary/GLOSSARY.md)

---

**维护说明**：本指南应定期更新，确保交叉引用格式的统一性和准确性。
