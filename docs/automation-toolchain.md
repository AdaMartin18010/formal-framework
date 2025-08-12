# Formal Framework 自动化工具链使用指南

## 概述

Formal Framework 自动化工具链是一套完整的工具集，用于自动检测、评估、补全和可视化项目文档。工具链包含以下核心组件：

1. **内容扫描工具** - 自动检测文档空白和薄弱点
2. **AI辅助补全工具** - 基于AI自动补全理论内容
3. **知识图谱生成工具** - 自动分析项目文档并生成知识图谱
4. **CI/CD集成** - GitHub Actions自动化工作流

## 快速开始

### 环境准备

```bash
# 克隆项目
git clone https://github.com/your-org/formal-framework.git
cd formal-framework

# 安装依赖
pip install -r requirements.txt
```

### 基本使用

#### 1. 内容扫描

```bash
# 扫描整个项目
python tools/content_scanner.py --verbose

# 生成详细报告
python tools/content_scanner.py --output reports/my_scan_report.md

# 使用自定义配置
python tools/content_scanner.py --config my_config.yaml
```

#### 2. AI辅助补全

```bash
# 设置OpenAI API密钥
export OPENAI_API_KEY="your-api-key"

# 补全单个文件
python tools/ai_completer.py --file docs/formal-model/interaction-model/theory.md

# 批量补全
python tools/ai_completer.py --pattern "**/theory.md" "**/dsl-draft.md"

# 指定输出目录
python tools/ai_completer.py --pattern "**/theory.md" --output-dir reports/ai_completed
```

#### 3. 知识图谱生成

```bash
# 生成知识图谱
python tools/knowledge_graph_generator.py --visualize --export-data --report

# 指定文档目录
python tools/knowledge_graph_generator.py --docs-dir docs --visualize

# 只生成数据文件
python tools/knowledge_graph_generator.py --export-data
```

## 配置说明

### 配置文件结构

工具链使用统一的配置文件 `config/automation_config.yaml`：

```yaml
# 内容扫描配置
content_scanner:
  required_files: 
    - "theory.md"
    - "dsl-draft.md"
  quality_threshold: 0.7
  scan_patterns: 
    - "*.md"
  exclude_patterns:
    - "**/temp/**"
    - "**/draft/**"
  min_file_size: 100
  required_sections:
    - "概念定义"
    - "理论基础"
    - "应用案例"
    - "最佳实践"

# 质量评估配置
quality_assessor:
  weights:
    completeness: 0.3
    consistency: 0.3
    readability: 0.4
  thresholds:
    warning: 0.6
    error: 0.4

# AI辅助配置
ai_completer:
  model: "gpt-4"
  max_tokens: 2000
  temperature: 0.7
  enabled: false  # 需要设置API密钥后启用

# 知识图谱配置
knowledge_graph:
  layout: "spring"
  node_size: 1000
  font_size: 8
  output_format: "png"
  include_weights: true
```

### 自定义配置

创建自定义配置文件 `my_config.yaml`：

```yaml
content_scanner:
  quality_threshold: 0.8  # 提高质量阈值
  required_sections:
    - "概念定义"
    - "理论基础"
    - "应用案例"
    - "最佳实践"
    - "开源项目映射"  # 添加新的必需章节

ai_completer:
  model: "gpt-3.5-turbo"  # 使用不同的模型
  max_tokens: 1500
  temperature: 0.5
  enabled: true
```

## 使用场景

### 1. 项目质量检查

定期运行内容扫描工具，检查项目文档质量：

```bash
# 每周运行一次质量检查
python tools/content_scanner.py --output reports/weekly_quality_report.md
```

### 2. 新内容开发

在开发新内容时，使用工具检查质量：

```bash
# 检查特定目录
python tools/content_scanner.py --config config/dev_config.yaml
```

### 3. 贡献者指南

为贡献者提供质量检查工具：

```bash
# 贡献者在提交前运行检查
python tools/content_scanner.py --verbose
```

### 4. AI辅助开发

使用AI工具辅助内容开发：

```bash
# 补全理论文档
python tools/ai_completer.py --file docs/formal-model/data-model/theory.md

# 批量补全DSL文档
python tools/ai_completer.py --pattern "**/dsl-draft.md" --output-dir reports/ai_completed
```

### 5. 知识图谱分析

生成和分析项目知识结构：

```bash
# 生成完整的知识图谱
python tools/knowledge_graph_generator.py --visualize --export-data --report

# 分析特定领域
python tools/knowledge_graph_generator.py --docs-dir docs/formal-model --visualize
```

## CI/CD集成

### GitHub Actions

项目已配置GitHub Actions工作流，自动执行：

1. **质量检查** - 每次PR和推送时运行
2. **知识图谱生成** - 自动生成和上传图谱
3. **AI自动补全** - 每周自动运行并创建PR

### 本地开发集成

在开发环境中集成质量检查：

```bash
# 在提交前运行检查
#!/bin/bash
# pre-commit hook
python tools/content_scanner.py --verbose
if [ $? -ne 0 ]; then
    echo "质量检查未通过，请修复问题后重新提交"
    exit 1
fi
```

## 报告格式

### 内容扫描报告

扫描工具生成的报告包含：

1. **扫描概览** - 总文件数、已分析文件数、缺失文件数等
2. **质量评估** - 整体质量分数和质量分布
3. **缺失文件** - 列出所有缺失的必需文件
4. **需要改进的文件** - 详细分析低质量文件的问题和建议
5. **常见问题** - 统计最常见的问题类型
6. **改进建议** - 整体改进建议

### AI补全报告

AI补全工具生成的报告包含：

1. **补全概览** - 成功补全的文件数和平均质量分数
2. **补全详情** - 每个文件的补全结果和改进建议
3. **质量评估** - 补全质量分数和内容增长情况

### 知识图谱报告

知识图谱工具生成的报告包含：

1. **图谱概览** - 概念总数、关系总数、类型分布
2. **核心概念** - 基于度中心性的核心概念分析
3. **社区结构** - 社区检测结果和概念分组
4. **概念详情** - 每个概念的详细信息和关联关系

## 高级用法

### 1. 自定义扫描规则

在 `content_scanner.py` 中添加新的分析规则：

```python
def _custom_analysis(self, content: str) -> Dict:
    """自定义分析规则"""
    result = {}
    
    # 添加你的分析逻辑
    # 例如：检查特定格式、统计特定内容等
    
    return result
```

### 2. 自定义质量指标

在质量评估中添加新的指标：

```python
def _calculate_custom_score(self, content: str) -> float:
    """计算自定义质量分数"""
    # 实现你的评分逻辑
    return score
```

### 3. 扩展AI提示词

自定义AI补全的提示词模板：

```yaml
completion_templates:
  custom:
    sections: ['自定义章节1', '自定义章节2']
    prompt_template: '自定义提示词模板：{missing_sections}'
```

## 故障排除

### 常见问题

1. **配置文件不存在**

   ```text
   警告: 配置文件 config/automation_config.yaml 不存在，使用默认配置
   ```

   解决方案：创建配置文件或使用 `--config` 参数指定配置文件

2. **AI功能未启用**

   ```text
   AI功能已禁用，请在配置文件中启用
   ```

   解决方案：设置 `OPENAI_API_KEY` 环境变量并在配置中启用AI功能

3. **依赖包缺失**

   ```text
   ModuleNotFoundError: No module named 'networkx'
   ```

   解决方案：安装缺失的依赖包 `pip install networkx matplotlib`

4. **文件编码错误**

   ```text
   文件读取错误: 'utf-8' codec can't decode byte
   ```

   解决方案：检查文件编码，确保使用UTF-8编码

### 调试模式

使用详细输出模式进行调试：

```bash
python tools/content_scanner.py --verbose
python tools/ai_completer.py --verbose
python tools/knowledge_graph_generator.py --verbose
```

## 性能优化

### 1. 并行处理

对于大型项目，可以启用并行处理：

```yaml
advanced:
  parallel_processing: true
  max_workers: 4
```

### 2. 缓存配置

启用缓存以提高性能：

```yaml
advanced:
  cache_enabled: true
  cache_ttl_hours: 24
```

### 3. 内存优化

对于内存受限的环境：

```yaml
advanced:
  memory_limit_mb: 512
  batch_size: 100
```

## 扩展开发

### 1. 添加新工具

在 `tools/` 目录下创建新的工具：

```python
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
新工具描述
"""

import argparse
from pathlib import Path

def main():
    parser = argparse.ArgumentParser(description='新工具描述')
    # 添加参数
    args = parser.parse_args()
    
    # 实现工具逻辑
    pass

if __name__ == "__main__":
    main()
```

### 2. 集成新功能

将新功能集成到现有工具中：

1. 在工具类中添加新方法
2. 更新配置文件支持新参数
3. 添加命令行参数
4. 更新文档和示例

### 3. 贡献指南

1. Fork项目仓库
2. 创建功能分支
3. 实现新功能
4. 添加测试用例
5. 更新文档
6. 提交Pull Request

## 最佳实践

### 1. 配置管理

- 使用版本控制的配置文件
- 为不同环境创建不同的配置
- 定期更新配置以适应项目变化

### 2. 质量检查

- 在每次提交前运行质量检查
- 定期生成质量报告
- 根据报告结果持续改进

### 3. AI辅助

- 合理使用AI补全功能
- 人工审核AI生成的内容
- 结合AI和人工智慧

### 4. 知识图谱

- 定期生成知识图谱
- 分析概念关联关系
- 识别知识空白和重复

## 总结

Formal Framework 自动化工具链为项目提供了完整的质量保证和内容管理能力。通过合理使用这些工具，可以：

- 提高文档质量和一致性
- 加速内容开发和维护
- 发现知识空白和改进机会
- 建立可视化的知识结构
- 实现自动化的质量监控

工具链的设计遵循了可扩展、可配置、易使用的原则，支持根据项目需求进行定制和扩展。
