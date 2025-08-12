# {{project_name}} 自动化报告

**报告类型**: {{report_type}}  
**生成时间**: {{timestamp}}  
**工具版本**: {{tool_version}}  
**配置版本**: {{config_version}}

## 执行摘要

{{executive_summary}}

## 详细结果

### 扫描统计

- **总文件数**: {{total_files}}
- **已分析文件数**: {{analyzed_files}}
- **成功处理**: {{success_count}}
- **警告数量**: {{warning_count}}
- **错误数量**: {{error_count}}

### 质量评估

#### 整体质量分数
- **平均质量分数**: {{average_quality_score}}
- **最高质量分数**: {{max_quality_score}}
- **最低质量分数**: {{min_quality_score}}

#### 质量分布
- **优秀** (≥0.8): {{excellent_count}} 个文件 ({{excellent_percentage}}%)
- **良好** (0.6-0.8): {{good_count}} 个文件 ({{good_percentage}}%)
- **一般** (0.4-0.6): {{fair_count}} 个文件 ({{fair_percentage}}%)
- **较差** (<0.4): {{poor_count}} 个文件 ({{poor_percentage}}%)

### 问题分析

#### 缺失文件
{{#missing_files}}
- `{{file_path}}`
{{/missing_files}}
{{^missing_files}}
- 无缺失文件
{{/missing_files}}

#### 需要改进的文件
{{#low_quality_files}}
### {{file_path}}
- **质量分数**: {{quality_score}}
- **文件大小**: {{file_size}} 字符
- **章节数**: {{section_count}}
- **代码块数**: {{code_block_count}}
- **链接数**: {{link_count}}

{{#issues}}
- **问题**:
{{#issue_list}}
  - {{issue}}
{{/issue_list}}
{{/issues}}

{{#suggestions}}
- **建议**:
{{#suggestion_list}}
  - {{suggestion}}
{{/suggestion_list}}
{{/suggestions}}

{{/low_quality_files}}

### 常见问题统计

{{#top_issues}}
1. **{{issue}}** - 出现 {{count}} 次
{{/top_issues}}

### 改进建议

{{#suggestions}}
- {{suggestion}}
{{/suggestions}}

## 配置信息

### 使用的配置
- **配置文件**: {{config_file}}
- **质量阈值**: {{quality_threshold}}
- **必需文件**: {{required_files}}
- **扫描模式**: {{scan_patterns}}

### 评估权重
- **完整性**: {{completeness_weight}}
- **一致性**: {{consistency_weight}}
- **可读性**: {{readability_weight}}

## 性能指标

### 执行时间
- **总执行时间**: {{total_execution_time}} 秒
- **平均文件处理时间**: {{avg_file_processing_time}} 秒
- **扫描速度**: {{scan_speed}} 文件/秒

### 资源使用
- **内存使用**: {{memory_usage}} MB
- **CPU使用**: {{cpu_usage}}%

## 趋势分析

{{#trend_analysis}}
### 与上次扫描对比
- **质量分数变化**: {{quality_score_change}}
- **文件数量变化**: {{file_count_change}}
- **问题数量变化**: {{issue_count_change}}
{{/trend_analysis}}

## 下一步行动

### 优先级任务
{{#priority_tasks}}
1. **{{priority}}**: {{task_description}}
{{/priority_tasks}}

### 长期改进计划
{{#long_term_plans}}
- {{plan}}
{{/long_term_plans}}

## 附录

### 完整文件列表
{{#all_files}}
- `{{file_path}}` (质量分数: {{quality_score}})
{{/all_files}}

### 详细错误日志
{{#error_logs}}
```
{{error_message}}
```
{{/error_logs}}

### 配置详情
```yaml
{{config_details}}
```

---

**报告生成工具**: {{tool_name}}  
**报告ID**: {{report_id}}  
**下次扫描建议**: {{next_scan_recommendation}} 