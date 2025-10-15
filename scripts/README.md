# 文档管理工具集

本目录包含了一系列用于管理形式化框架文档的工具脚本。

## 工具列表

### 1. 文档索引生成器 (`generate_doc_index.py`)

用于自动生成文档索引、交叉引用和导航。

**功能：**

- 扫描所有Markdown文档
- 提取文档元数据和结构
- 构建交叉引用映射
- 生成文档索引报告

**使用方法：**

```bash
python scripts/generate_doc_index.py
```

**输出文件：**

- `docs_index.json` - 文档索引数据
- `docs_index_report.md` - 文档索引报告

### 2. 证据条目管理器 (`evidence_manager.py`)

用于管理证据条目的创建、验证和更新。

**功能：**

- 解析证据条目文件
- 验证证据条目完整性
- 生成证据条目报告
- 管理证据条目数据

**使用方法：**

```bash
python scripts/evidence_manager.py
```

**输出文件：**

- `evidence_data.json` - 证据条目数据
- `evidence_report.md` - 证据条目报告

### 3. 质量度量系统 (`quality_metrics.py`)

用于评估文档质量和完整性。

**功能：**

- 分析文档质量指标
- 计算完整性、一致性、清晰度等得分
- 识别文档问题和改进建议
- 生成质量评估报告

**使用方法：**

```bash
python scripts/quality_metrics.py
```

**输出文件：**

- `quality_metrics.json` - 质量度量数据
- `quality_report.md` - 质量评估报告

### 4. 证据条目模板生成器 (`generate_evidence_template.py`)

用于生成标准化的证据条目模板。

**功能：**

- 生成标准化的证据条目模板
- 支持自定义参数
- 创建示例证据条目

**使用方法：**

```bash
# 生成示例证据条目
python scripts/generate_evidence_template.py

# 在代码中使用
from generate_evidence_template import EvidenceTemplateGenerator
generator = EvidenceTemplateGenerator()
generator.create_evidence_file("EVIDENCE-001", "标题", "应用", "来源", "A")
```

### 5. 文档管理综合工具 (`doc_manager.py`)

整合所有文档管理功能的综合工具。

**功能：**

- 整合所有文档管理功能
- 生成综合报告
- 提供命令行接口

**使用方法：**

```bash
# 运行所有功能
python scripts/doc_manager.py --all

# 生成文档索引
python scripts/doc_manager.py --index

# 管理证据条目
python scripts/doc_manager.py --evidence

# 评估文档质量
python scripts/doc_manager.py --quality

# 生成证据条目模板
python scripts/doc_manager.py --template

# 创建自定义证据条目
python scripts/doc_manager.py --create-evidence "EVIDENCE-001" "标题" "应用" "来源" "A"
```

## 质量指标说明

### 完整性得分 (Completeness Score)

- 检查文档基本结构
- 验证元数据完整性
- 评估内容长度
- 检查代码块和表格数量

### 一致性得分 (Consistency Score)

- 检查标题格式一致性
- 验证列表格式统一性
- 评估代码块格式
- 检查链接格式一致性

### 清晰度得分 (Clarity Score)

- 评估标题清晰度
- 检查段落长度合理性
- 验证句子长度
- 评估专业术语使用

### 准确性得分 (Accuracy Score)

- 检查引用格式
- 验证证据条目引用
- 评估版本信息
- 检查日期和作者信息

### 可用性得分 (Usability Score)

- 检查目录结构
- 评估导航链接
- 验证示例代码
- 检查图表和最佳实践

## 质量等级

- **Excellent (90-100分)**：优秀，文档质量很高
- **Good (75-89分)**：良好，文档质量较好
- **Fair (60-74分)**：一般，文档质量中等
- **Poor (40-59分)**：较差，文档质量需要改进
- **Incomplete (0-39分)**：不完整，文档严重缺失

## 使用建议

### 日常维护

1. 定期运行质量评估工具检查文档质量
2. 使用证据条目管理器维护证据条目
3. 通过文档索引生成器更新文档索引

### 新文档创建

1. 使用证据条目模板生成器创建标准化的证据条目
2. 运行质量评估工具检查新文档质量
3. 更新文档索引以包含新文档

### 质量改进

1. 根据质量报告识别需要改进的文档
2. 按照改进建议优化文档内容
3. 重新运行质量评估验证改进效果

## 输出文件说明

### JSON数据文件

- `docs_index.json` - 文档索引数据，包含所有文档的元数据和结构信息
- `evidence_data.json` - 证据条目数据，包含所有证据条目的详细信息
- `quality_metrics.json` - 质量度量数据，包含所有文档的质量评估结果

### Markdown报告文件

- `docs_index_report.md` - 文档索引报告，提供文档概览和统计信息
- `evidence_report.md` - 证据条目报告，提供证据条目管理和验证信息
- `quality_report.md` - 质量评估报告，提供文档质量分析和改进建议
- `comprehensive_report.md` - 综合报告，整合所有分析结果

## 扩展开发

### 添加新的质量指标

1. 在 `QualityMetricsSystem` 类中添加新的计算方法
2. 更新 `QualityMetrics` 数据类
3. 修改报告生成逻辑

### 添加新的文档类型支持

1. 更新文档分类逻辑
2. 添加新的解析规则
3. 扩展质量评估标准

### 集成CI/CD

1. 将工具集成到CI/CD流水线
2. 设置质量门禁
3. 自动生成和发布报告

## 故障排除

### 常见问题

1. **导入模块失败**：确保所有脚本都在同一目录下
2. **文件读取失败**：检查文件路径和权限
3. **编码问题**：确保所有文件使用UTF-8编码

### 调试建议

1. 使用 `--verbose` 参数获取详细输出
2. 检查生成的JSON文件了解数据结构
3. 查看错误日志定位问题

## 贡献指南

1. 遵循现有的代码风格和结构
2. 添加适当的文档和注释
3. 编写单元测试验证功能
4. 提交前运行所有工具确保兼容性
