#!/usr/bin/env python3
"""
证据条目模板生成器
用于生成标准化的证据条目模板
"""

import os
from pathlib import Path
from datetime import datetime
from typing import Dict, List

class EvidenceTemplateGenerator:
    def __init__(self, evidence_dir: str = "docs/evidence"):
        self.evidence_dir = Path(evidence_dir)
        self.template = self.get_template()
    
    def get_template(self) -> str:
        """获取证据条目模板"""
        return """---
id: evidence:{evidence_id}
title: {title}
version: V1.0
status: draft
category: {category}
source: {source}
credibility: {credibility}
---

## 1. 基本信息

- **分类**：{category}
- **来源**：{source}
- **可信度**：{credibility}（{credibility_desc}）
- **版本**：{version}
- **发布日期**：{release_date}

## 2. 摘要

{summary}

## 3. 对齐维度

### 3.1 术语对齐

- **{term1}** ↔ `{model1}` {description1}
- **{term2}** ↔ `{model2}` {description2}
- **{term3}** ↔ `{model3}` {description3}
- **{term4}** ↔ `{model4}` {description4}
- **{term5}** ↔ `{model5}` {description5}

### 3.2 结构/接口对齐

- **{interface1}** ↔ `{model1}` {description1}
- **{interface2}** ↔ `{model2}` {description2}
- **{interface3}** ↔ `{model3}` {description3}
- **{interface4}** ↔ `{model4}` {description4}

### 3.3 约束/不变式对齐

- **{constraint1}** ↔ `{model1}` {description1}
- **{constraint2}** ↔ `{model2}` {description2}
- **{constraint3}** ↔ `{model3}` {description3}
- **{constraint4}** ↔ `{model4}` {description4}

### 3.4 度量/指标对齐

- **{metric1}** ↔ `{model1}` {description1}
- **{metric2}** ↔ `{model2}` {description2}
- **{metric3}** ↔ `{model3}` {description3}
- **{metric4}** ↔ `{model4}` {description4}

## 4. 映射

### 4.1 L2映射

- **{l2_model1}**：{l2_desc1}
- **{l2_model2}**：{l2_desc2}
- **{l2_model3}**：{l2_desc3}
- **{l2_model4}**：{l2_desc4}

### 4.2 L3映射

- **{l3_model1}**：{l3_desc1}
- **{l3_model2}**：{l3_desc2}
- **{l3_model3}**：{l3_desc3}
- **{l3_model4}**：{l3_desc4}

### 4.3 L4映射

- **{l4_model1}**：{l4_desc1}
- **{l4_model2}**：{l4_desc2}

## 5. 引用

### 5.1 原文链接

- **{source_name}**：<{source_url}>
- **{doc_name}**：<{doc_url}>
- **{ref_name}**：<{ref_url}>

### 5.2 版本/日期

- **{source_name}版本**：{source_version}
- **文档版本**：{doc_version}
- **最后更新**：{last_update}

### 5.3 其他参考

- **{ref1}**：{ref1_desc}
- **{ref2}**：{ref2_desc}
- **{ref3}**：{ref3_desc}

## 6. 评审

### 6.1 评审人

- **技术评审**：{tech_reviewer}
- **标准评审**：{standard_reviewer}
- **实践评审**：{practice_reviewer}

### 6.2 结论

**{conclusion}** - {conclusion_desc}

### 6.3 备注

- {note1}
- {note2}
- {note3}
"""
    
    def generate_evidence_template(self, evidence_id: str, title: str, category: str, 
                                 source: str, credibility: str = "A", **kwargs) -> str:
        """生成证据条目模板"""
        
        # 默认值
        defaults = {
            "evidence_id": evidence_id,
            "title": title,
            "category": category,
            "source": source,
            "credibility": credibility,
            "credibility_desc": self.get_credibility_desc(credibility),
            "version": "V1.0",
            "release_date": datetime.now().strftime("%Y-%m-%d"),
            "summary": f"{title}是{category}领域的典型应用案例，展示了相关技术的实施方法和最佳实践。",
            
            # 术语对齐
            "term1": "核心概念1",
            "model1": "L3_D01_交互标准模型.md",
            "description1": "概念描述1",
            "term2": "核心概念2",
            "model2": "L3_D02_数据标准模型.md",
            "description2": "概念描述2",
            "term3": "核心概念3",
            "model3": "L3_D03_功能标准模型.md",
            "description3": "概念描述3",
            "term4": "核心概念4",
            "model4": "L3_D04_运行时标准模型.md",
            "description4": "概念描述4",
            "term5": "核心概念5",
            "model5": "L3_D05_部署标准模型.md",
            "description5": "概念描述5",
            
            # 结构/接口对齐
            "interface1": "主要接口1",
            "interface2": "主要接口2",
            "interface3": "主要接口3",
            "interface4": "主要接口4",
            
            # 约束/不变式对齐
            "constraint1": "主要约束1",
            "constraint2": "主要约束2",
            "constraint3": "主要约束3",
            "constraint4": "主要约束4",
            
            # 度量/指标对齐
            "metric1": "关键指标1",
            "metric2": "关键指标2",
            "metric3": "关键指标3",
            "metric4": "关键指标4",
            
            # L2映射
            "l2_model1": "L2_D01_交互元模型.md",
            "l2_desc1": "交互相关概念和关系",
            "l2_model2": "L2_D02_数据元模型.md",
            "l2_desc2": "数据相关概念和关系",
            "l2_model3": "L2_D03_功能元模型.md",
            "l2_desc3": "功能相关概念和关系",
            "l2_model4": "L2_D04_运行时元模型.md",
            "l2_desc4": "运行时相关概念和关系",
            
            # L3映射
            "l3_model1": "L3_D01_交互标准模型.md",
            "l3_desc1": "交互标准和技术规范",
            "l3_model2": "L3_D02_数据标准模型.md",
            "l3_desc2": "数据标准和技术规范",
            "l3_model3": "L3_D03_功能标准模型.md",
            "l3_desc3": "功能标准和技术规范",
            "l3_model4": "L3_D04_运行时标准模型.md",
            "l3_desc4": "运行时标准和技术规范",
            
            # L4映射
            "l4_model1": "L4_D90_CN_行业索引与对标.md",
            "l4_desc1": "云原生行业标准对标",
            "l4_model2": "industry-model/cloud-native-architecture/README.md",
            "l4_desc2": "云原生架构案例",
            
            # 引用信息
            "source_name": "主要来源",
            "source_url": "https://example.com",
            "doc_name": "文档名称",
            "doc_url": "https://example.com/docs",
            "ref_name": "参考名称",
            "ref_url": "https://example.com/ref",
            "source_version": "1.0.0",
            "doc_version": datetime.now().strftime("%Y-%m-%d"),
            "last_update": datetime.now().strftime("%Y-%m-%d"),
            "ref1": "参考1",
            "ref1_desc": "参考1描述",
            "ref2": "参考2",
            "ref2_desc": "参考2描述",
            "ref3": "参考3",
            "ref3_desc": "参考3描述",
            
            # 评审信息
            "tech_reviewer": "技术专家",
            "standard_reviewer": "标准专家",
            "practice_reviewer": "实践专家",
            "conclusion": "通过",
            "conclusion_desc": "该案例完整展示了相关技术的实施方案，与形式化框架的L3标准模型高度对齐，为相关领域提供了重要的参考价值。",
            "note1": "案例涵盖了相关技术的核心功能，适合作为参考实现",
            "note2": "建议在实际应用中结合具体的业务场景进行定制化配置",
            "note3": "需要关注相关技术的要求和最佳实践"
        }
        
        # 合并用户提供的参数
        defaults.update(kwargs)
        
        # 生成模板
        return self.template.format(**defaults)
    
    def get_credibility_desc(self, credibility: str) -> str:
        """获取可信度描述"""
        credibility_descs = {
            "A": "权威官方标准",
            "B": "行业标准或知名开源项目",
            "C": "学术论文或研究报告",
            "D": "商业产品或服务",
            "E": "个人博客或非官方文档"
        }
        return credibility_descs.get(credibility, "未知")
    
    def create_evidence_file(self, evidence_id: str, title: str, category: str, 
                           source: str, credibility: str = "A", **kwargs) -> str:
        """创建证据条目文件"""
        
        # 确保证据目录存在
        self.evidence_dir.mkdir(parents=True, exist_ok=True)
        
        # 生成文件名
        filename = f"{evidence_id}.md"
        file_path = self.evidence_dir / filename
        
        # 生成模板内容
        content = self.generate_evidence_template(
            evidence_id, title, category, source, credibility, **kwargs
        )
        
        # 写入文件
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print(f"证据条目文件已创建: {file_path}")
        return str(file_path)
    
    def create_sample_evidence(self):
        """创建示例证据条目"""
        samples = [
            {
                "evidence_id": "SAMPLE-001",
                "title": "示例证据条目",
                "category": "应用",
                "source": "示例来源",
                "credibility": "A",
                "summary": "这是一个示例证据条目，展示了证据条目的标准格式和内容结构。"
            }
        ]
        
        for sample in samples:
            self.create_evidence_file(**sample)

def main():
    generator = EvidenceTemplateGenerator()
    
    # 创建示例证据条目
    generator.create_sample_evidence()
    
    print("证据条目模板生成器运行完成！")

if __name__ == "__main__":
    main()
