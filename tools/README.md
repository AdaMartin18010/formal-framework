# Formal Framework 自动化工具链

本目录包含 Formal Framework 项目的自动化工具，用于内容扫描、质量评估、AI辅助补全等功能。

## 工具列表

### 1. 内容扫描工具 (content_scanner.py)

自动检测项目文档的空白点、薄弱点和质量评估。

**功能特性：**

- 自动扫描项目中的所有 Markdown 文件
- 分析文件内容质量（完整性、一致性、可读性）
- 检测缺失的必需文件（theory.md, dsl-draft.md）
- 生成详细的质量报告和改进建议
- 支持自定义配置和扫描规则

**使用方法：**

```bash
# 使用默认配置扫描
python tools/content_scanner.py

# 使用自定义配置文件
python tools/content_scanner.py --config my_config.yaml

# 指定输出报告路径
python tools/content_scanner.py --output reports/my_report.md

# 详细输出模式
python tools/content_scanner.py --verbose
```

**输出示例：**

```text
开始扫描项目内容...
分析文件: docs/formal-model/interaction-model/theory.md
分析文件: docs/formal-model/data-model/theory.md
...

扫描完成!
总文件数: 45
已分析文件数: 42
缺失文件数: 3
低质量文件数: 8
报告已保存到: reports/content_scan_report_20241201_143022.md
```

### 2. AI辅助补全工具 (ai_completer.py) - 开发中

基于AI自动补全理论内容，生成相关案例和最佳实践。

**计划功能：**

- 基于现有内容智能补全缺失部分
- 生成相关代码示例和最佳实践
- 提供内容改进建议
- 支持多种AI模型（OpenAI GPT、本地模型等）

### 3. 知识图谱生成工具 (knowledge_graph_generator.py) - 开发中

自动分析项目文档，生成知识图谱和概念关联关系。

**计划功能：**

- 自动分析文档中的概念和关系
- 生成可视化知识图谱
- 提供概念导航和关联查询
- 支持多种图谱布局算法

### 4. 质量评估工具 (quality_assessor.py) - 开发中

评估文档质量，生成质量报告和改进建议。

**计划功能：**

- 多维度质量评估（完整性、准确性、一致性）
- 生成详细的质量报告
- 提供改进建议和最佳实践
- 支持自定义评估标准

## 配置说明

### 配置文件 (config/automation_config.yaml)

工具链使用统一的配置文件，包含以下主要配置项：

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
  enabled: false
```

### 自定义配置

你可以创建自定义配置文件来调整工具行为：

```yaml
# my_config.yaml
content_scanner:
  quality_threshold: 0.8  # 提高质量阈值
  required_sections:
    - "概念定义"
    - "理论基础"
    - "应用案例"
    - "最佳实践"
    - "开源项目映射"  # 添加新的必需章节

quality_assessor:
  weights:
    completeness: 0.4
    consistency: 0.3
    readability: 0.3
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

## 报告格式

### 内容扫描报告

扫描工具生成的报告包含以下部分：

1. **扫描概览**：总文件数、已分析文件数、缺失文件数等
2. **质量评估**：整体质量分数和质量分布
3. **缺失文件**：列出所有缺失的必需文件
4. **需要改进的文件**：详细分析低质量文件的问题和建议
5. **常见问题**：统计最常见的问题类型
6. **改进建议**：整体改进建议

### 报告示例

```markdown
# Formal Framework 内容扫描报告

**生成时间**: 2024-12-01 14:30:22

## 扫描概览

- **总文件数**: 45
- **已分析文件数**: 42
- **缺失文件数**: 3
- **低质量文件数**: 8

## 质量评估

### 整体质量分数
- **平均质量分数**: 0.72

### 质量分布
- **优秀** (≥0.8): 15 个文件
- **良好** (0.6-0.8): 18 个文件
- **一般** (0.4-0.6): 7 个文件
- **较差** (<0.4): 2 个文件

## 缺失文件

- `docs/formal-model/testing-model/theory.md`
- `docs/formal-model/testing-model/dsl-draft.md`
- `docs/industry-model/healthcare-architecture/theory.md`

## 需要改进的文件

### docs/formal-model/monitoring-model/theory.md
- **质量分数**: 0.45
- **文件大小**: 234 字符
- **章节数**: 1
- **代码块数**: 0
- **链接数**: 1
- **问题**:
  - 内容过短，建议增加更多详细信息
  - 缺少代码示例，建议添加相关代码
  - 缺少必需章节: 概念定义, 理论基础, 应用案例, 最佳实践
- **建议**:
  - 增加内容长度，提供更详细的说明
  - 添加更多章节，完善文档结构
  - 添加更多代码示例，提高实用性
```

## 集成到CI/CD

### GitHub Actions 集成

```yaml
# .github/workflows/quality-check.yml
name: Quality Check
on: [push, pull_request]

jobs:
  quality-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Set up Python
        uses: actions/setup-python@v3
        with:
          python-version: '3.9'
      
      - name: Install dependencies
        run: |
          pip install pyyaml
      
      - name: Run content scanner
        run: python tools/content_scanner.py --output reports/ci_report.md
      
      - name: Upload report
        uses: actions/upload-artifact@v3
        with:
          name: quality-report
          path: reports/ci_report.md
```

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

## 扩展开发

### 添加新的扫描规则

在 `content_scanner.py` 中添加新的分析规则：

```python
def _custom_analysis(self, content: str) -> Dict:
    """自定义分析规则"""
    result = {}
    
    # 添加你的分析逻辑
    # 例如：检查特定格式、统计特定内容等
    
    return result
```

### 添加新的质量指标

在质量评估中添加新的指标：

```python
def _calculate_custom_score(self, content: str) -> float:
    """计算自定义质量分数"""
    # 实现你的评分逻辑
    return score
```

## 故障排除

### 常见问题

1. **配置文件不存在**

   ```text
   警告: 配置文件 config/automation_config.yaml 不存在，使用默认配置
   ```

   解决方案：创建配置文件或使用 `--config` 参数指定配置文件

2. **文件编码错误**

   ```text
   文件读取错误: 'utf-8' codec can't decode byte
   ```

   解决方案：检查文件编码，确保使用UTF-8编码

3. **权限错误**

   ```text
   PermissionError: [Errno 13] Permission denied
   ```

   解决方案：检查文件权限，确保有读取权限

### 调试模式

使用详细输出模式进行调试：

```bash
python tools/content_scanner.py --verbose
```

## 贡献指南

### 开发新工具

1. 在 `tools/` 目录下创建新的工具文件
2. 遵循现有的代码风格和结构
3. 添加详细的文档和示例
4. 更新本README文件

### 改进现有工具

1. 创建功能分支
2. 实现改进功能
3. 添加测试用例
4. 更新文档
5. 提交Pull Request

## 许可证

本工具链遵循项目的MIT许可证。
