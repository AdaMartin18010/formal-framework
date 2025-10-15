# API文档

本文档描述了形式化框架项目的API接口，包括工具API、模型API、验证API等核心接口。

## 目录

- [1. API概述](#1-api概述)
- [2. 工具API](#2-工具api)
- [3. 模型API](#3-模型api)
- [4. 验证API](#4-验证api)
- [5. 数据API](#5-数据api)
- [6. 错误处理](#6-错误处理)

## 1. API概述

### 1.1 API架构

形式化框架采用RESTful API架构，提供统一的接口规范：

- **RESTful设计**：遵循REST架构原则
- **JSON格式**：使用JSON作为数据交换格式
- **HTTP方法**：使用标准HTTP方法
- **状态码**：使用标准HTTP状态码

### 1.2 基础信息

- **基础URL**：`https://api.formal-framework.org/v1`
- **认证方式**：API Key认证
- **数据格式**：JSON
- **字符编码**：UTF-8

### 1.3 通用参数

#### 1.3.1 请求头

```http
Content-Type: application/json
Authorization: Bearer <api_key>
Accept: application/json
User-Agent: FormalFramework-Client/1.0
```

#### 1.3.2 通用响应

```json
{
  "success": true,
  "data": {},
  "message": "操作成功",
  "timestamp": "2024-12-19T10:00:00Z",
  "request_id": "req_123456789"
}
```

## 2. 工具API

### 2.1 文档管理API

#### 2.1.1 生成文档索引

**接口**：`POST /tools/generate-doc-index`

**描述**：生成文档索引和交叉引用

**请求参数**：

```json
{
  "source_path": "docs/",
  "output_format": "json",
  "include_metadata": true,
  "generate_cross_references": true
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "index_file": "doc_index.json",
    "total_documents": 50,
    "total_words": 200000,
    "total_lines": 10000,
    "generation_time": "2024-12-19T10:00:00Z"
  },
  "message": "文档索引生成成功"
}
```

#### 2.1.2 检查文档质量

**接口**：`POST /tools/check-document-quality`

**描述**：检查文档质量和完整性

**请求参数**：

```json
{
  "document_path": "docs/README.md",
  "check_dimensions": ["completeness", "consistency", "clarity", "accuracy", "usability"],
  "quality_threshold": 0.8
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "document_path": "docs/README.md",
    "overall_score": 0.87,
    "quality_level": "Good",
    "dimension_scores": {
      "completeness": 0.85,
      "consistency": 0.90,
      "clarity": 0.80,
      "accuracy": 0.95,
      "usability": 0.85
    },
    "issues_found": 5,
    "recommendations": 3
  },
  "message": "文档质量检查完成"
}
```

#### 2.1.3 管理证据条目

**接口**：`POST /tools/manage-evidence`

**描述**：管理证据条目的创建、验证和更新

**请求参数**：

```json
{
  "action": "create",
  "evidence_data": {
    "id": "EVIDENCE-001",
    "title": "Kubernetes基础编排案例",
    "description": "Kubernetes集群编排的基础案例",
    "alignment_dimensions": {
      "terminology_alignment": "A",
      "structure_alignment": "A",
      "constraint_alignment": "A",
      "metric_alignment": "A"
    },
    "mapping": {
      "l2_mapping": ["L2_D04_运行时元模型"],
      "l3_mapping": ["L3_D04_运行时标准模型"],
      "l4_mapping": ["L4_D90_CN_行业索引与对标"]
    }
  }
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "evidence_id": "EVIDENCE-001",
    "status": "created",
    "validation_result": {
      "credibility_check": "passed",
      "alignment_check": "passed",
      "mapping_check": "passed",
      "review_check": "pending"
    },
    "created_at": "2024-12-19T10:00:00Z"
  },
  "message": "证据条目创建成功"
}
```

### 2.2 质量评估API

#### 2.2.1 评估文档质量

**接口**：`POST /tools/assess-quality`

**描述**：评估文档的多个质量维度

**请求参数**：

```json
{
  "document_path": "docs/README.md",
  "assessment_dimensions": ["completeness", "consistency", "clarity", "accuracy", "usability"],
  "quality_gates": {
    "completeness_gate": 0.85,
    "consistency_gate": 0.90,
    "clarity_gate": 0.80,
    "accuracy_gate": 0.95,
    "usability_gate": 0.85
  }
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "document_path": "docs/README.md",
    "overall_score": 0.87,
    "quality_level": "Good",
    "dimension_scores": {
      "completeness": 0.85,
      "consistency": 0.90,
      "clarity": 0.80,
      "accuracy": 0.95,
      "usability": 0.85
    },
    "gate_results": {
      "completeness_gate": "passed",
      "consistency_gate": "passed",
      "clarity_gate": "passed",
      "accuracy_gate": "passed",
      "usability_gate": "passed"
    },
    "issues": [
      {
        "type": "clarity",
        "severity": "medium",
        "description": "部分章节表达不够清晰",
        "suggestion": "建议使用更简洁的语言表达"
      }
    ],
    "recommendations": [
      {
        "type": "completeness",
        "priority": "high",
        "description": "补充缺失的章节内容",
        "action": "添加详细的实施指南"
      }
    ]
  },
  "message": "质量评估完成"
}
```

#### 2.2.2 生成质量报告

**接口**：`POST /tools/generate-quality-report`

**描述**：生成详细的质量评估报告

**请求参数**：

```json
{
  "report_type": "comprehensive",
  "document_paths": ["docs/README.md", "docs/CONTRIBUTING.md"],
  "include_recommendations": true,
  "include_metrics": true,
  "output_format": "json"
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "report_id": "QR-20241219-001",
    "report_type": "comprehensive",
    "generated_at": "2024-12-19T10:00:00Z",
    "summary": {
      "total_documents": 2,
      "average_score": 0.86,
      "quality_distribution": {
        "excellent": 0,
        "good": 2,
        "fair": 0,
        "poor": 0,
        "incomplete": 0
      }
    },
    "detailed_results": [
      {
        "document_path": "docs/README.md",
        "overall_score": 0.87,
        "quality_level": "Good",
        "dimension_scores": {
          "completeness": 0.85,
          "consistency": 0.90,
          "clarity": 0.80,
          "accuracy": 0.95,
          "usability": 0.85
        }
      }
    ],
    "recommendations": [
      {
        "priority": "high",
        "category": "completeness",
        "description": "补充缺失的章节内容",
        "affected_documents": ["docs/README.md"]
      }
    ],
    "metrics": {
      "total_words": 15000,
      "total_lines": 800,
      "average_words_per_document": 7500,
      "average_lines_per_document": 400
    }
  },
  "message": "质量报告生成成功"
}
```

## 3. 模型API

### 3.1 模型管理API

#### 3.1.1 获取模型列表

**接口**：`GET /models`

**描述**：获取所有可用模型的列表

**请求参数**：

```json
{
  "model_type": "all",
  "layer": "all",
  "industry": "all",
  "limit": 50,
  "offset": 0
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "models": [
      {
        "id": "L2_D01",
        "name": "交互元模型",
        "type": "meta_model",
        "layer": "L2",
        "description": "定义交互相关的核心概念和关系",
        "version": "1.0.0",
        "status": "active",
        "created_at": "2024-12-19T10:00:00Z",
        "updated_at": "2024-12-19T10:00:00Z"
      }
    ],
    "total_count": 23,
    "page_info": {
      "limit": 50,
      "offset": 0,
      "has_next": false,
      "has_previous": false
    }
  },
  "message": "模型列表获取成功"
}
```

#### 3.1.2 获取模型详情

**接口**：`GET /models/{model_id}`

**描述**：获取指定模型的详细信息

**请求参数**：

```json
{
  "include_relationships": true,
  "include_examples": true,
  "include_validation": true
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "id": "L2_D01",
    "name": "交互元模型",
    "type": "meta_model",
    "layer": "L2",
    "description": "定义交互相关的核心概念和关系",
    "version": "1.0.0",
    "status": "active",
    "content": {
      "concepts": [
        {
          "name": "Interaction",
          "description": "交互概念",
          "properties": ["id", "type", "participants", "protocol"]
        }
      ],
      "relationships": [
        {
          "name": "ParticipatesIn",
          "description": "参与关系",
          "from": "Actor",
          "to": "Interaction"
        }
      ],
      "constraints": [
        {
          "name": "UniqueInteractionId",
          "description": "交互ID唯一性约束",
          "expression": "unique(Interaction.id)"
        }
      ]
    },
    "relationships": [
      {
        "type": "extends",
        "target": "L3_D01_交互标准模型",
        "description": "扩展为标准模型"
      }
    ],
    "examples": [
      {
        "name": "REST API交互",
        "description": "基于REST协议的API交互示例",
        "content": "..."
      }
    ],
    "validation": {
      "syntax_valid": true,
      "semantics_valid": true,
      "consistency_valid": true,
      "last_validated": "2024-12-19T10:00:00Z"
    },
    "created_at": "2024-12-19T10:00:00Z",
    "updated_at": "2024-12-19T10:00:00Z"
  },
  "message": "模型详情获取成功"
}
```

#### 3.1.3 创建模型

**接口**：`POST /models`

**描述**：创建新的模型

**请求参数**：

```json
{
  "name": "新模型",
  "type": "standard_model",
  "layer": "L3",
  "description": "新模型的描述",
  "content": {
    "concepts": [
      {
        "name": "NewConcept",
        "description": "新概念",
        "properties": ["id", "name"]
      }
    ],
    "relationships": [
      {
        "name": "NewRelationship",
        "description": "新关系",
        "from": "Concept1",
        "to": "Concept2"
      }
    ]
  },
  "based_on": ["L2_D01"],
  "industry": "general"
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "id": "L3_D11",
    "name": "新模型",
    "type": "standard_model",
    "layer": "L3",
    "description": "新模型的描述",
    "version": "1.0.0",
    "status": "draft",
    "created_at": "2024-12-19T10:00:00Z",
    "updated_at": "2024-12-19T10:00:00Z"
  },
  "message": "模型创建成功"
}
```

### 3.2 模型验证API

#### 3.2.1 验证模型语法

**接口**：`POST /models/{model_id}/validate/syntax`

**描述**：验证模型的语法正确性

**请求参数**：

```json
{
  "validation_level": "strict",
  "include_suggestions": true
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "model_id": "L2_D01",
    "validation_type": "syntax",
    "is_valid": true,
    "errors": [],
    "warnings": [
      {
        "line": 15,
        "column": 10,
        "message": "建议使用更描述性的属性名",
        "suggestion": "将'prop'改为'property_name'"
      }
    ],
    "suggestions": [
      {
        "type": "naming",
        "message": "建议使用驼峰命名法",
        "example": "interactionType -> interaction_type"
      }
    ],
    "validated_at": "2024-12-19T10:00:00Z"
  },
  "message": "语法验证完成"
}
```

#### 3.2.2 验证模型语义

**接口**：`POST /models/{model_id}/validate/semantics`

**描述**：验证模型的语义正确性

**请求参数**：

```json
{
  "validation_rules": ["consistency", "completeness", "correctness"],
  "include_recommendations": true
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "model_id": "L2_D01",
    "validation_type": "semantics",
    "is_valid": true,
    "rule_results": {
      "consistency": {
        "passed": true,
        "score": 0.95,
        "details": "模型内部一致性良好"
      },
      "completeness": {
        "passed": true,
        "score": 0.90,
        "details": "模型定义完整"
      },
      "correctness": {
        "passed": true,
        "score": 0.92,
        "details": "模型逻辑正确"
      }
    },
    "recommendations": [
      {
        "type": "completeness",
        "priority": "medium",
        "message": "建议添加更多约束条件",
        "suggestion": "为关键概念添加业务规则约束"
      }
    ],
    "validated_at": "2024-12-19T10:00:00Z"
  },
  "message": "语义验证完成"
}
```

## 4. 验证API

### 4.1 形式化验证API

#### 4.1.1 验证不变式

**接口**：`POST /validation/invariants`

**描述**：验证模型的不变式属性

**请求参数**：

```json
{
  "model_id": "L2_D01",
  "invariants": [
    {
      "name": "DataConsistency",
      "expression": "∀ d ∈ DataModel. d.integrity_constraints ⇒ d.valid_state",
      "description": "数据一致性不变式"
    }
  ],
  "verification_method": "model_checking"
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "model_id": "L2_D01",
    "verification_method": "model_checking",
    "results": [
      {
        "invariant_name": "DataConsistency",
        "status": "satisfied",
        "verification_time": "0.5s",
        "details": "不变式在所有状态下都满足"
      }
    ],
    "overall_status": "satisfied",
    "verified_at": "2024-12-19T10:00:00Z"
  },
  "message": "不变式验证完成"
}
```

#### 4.1.2 验证属性

**接口**：`POST /validation/properties`

**描述**：验证模型的时序属性

**请求参数**：

```json
{
  "model_id": "L2_D01",
  "properties": [
    {
      "name": "Liveness",
      "formula": "◊ (system_ready ∧ service_available)",
      "description": "活性属性"
    },
    {
      "name": "Safety",
      "formula": "□ (no_unauthorized_access ∧ data_integrity)",
      "description": "安全性属性"
    }
  ],
  "temporal_logic": "CTL"
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "model_id": "L2_D01",
    "temporal_logic": "CTL",
    "results": [
      {
        "property_name": "Liveness",
        "status": "satisfied",
        "verification_time": "1.2s",
        "details": "活性属性在所有执行路径上都满足"
      },
      {
        "property_name": "Safety",
        "status": "satisfied",
        "verification_time": "0.8s",
        "details": "安全性属性在所有状态下都满足"
      }
    ],
    "overall_status": "satisfied",
    "verified_at": "2024-12-19T10:00:00Z"
  },
  "message": "属性验证完成"
}
```

### 4.2 质量验证API

#### 4.2.1 验证文档质量

**接口**：`POST /validation/document-quality`

**描述**：验证文档的质量指标

**请求参数**：

```json
{
  "document_path": "docs/README.md",
  "quality_dimensions": ["completeness", "consistency", "clarity", "accuracy", "usability"],
  "quality_gates": {
    "completeness_gate": 0.85,
    "consistency_gate": 0.90,
    "clarity_gate": 0.80,
    "accuracy_gate": 0.95,
    "usability_gate": 0.85
  }
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "document_path": "docs/README.md",
    "overall_score": 0.87,
    "quality_level": "Good",
    "dimension_scores": {
      "completeness": 0.85,
      "consistency": 0.90,
      "clarity": 0.80,
      "accuracy": 0.95,
      "usability": 0.85
    },
    "gate_results": {
      "completeness_gate": "passed",
      "consistency_gate": "passed",
      "clarity_gate": "passed",
      "accuracy_gate": "passed",
      "usability_gate": "passed"
    },
    "all_gates_passed": true,
    "validated_at": "2024-12-19T10:00:00Z"
  },
  "message": "文档质量验证完成"
}
```

#### 4.2.2 验证一致性

**接口**：`POST /validation/consistency`

**描述**：验证模型和文档的一致性

**请求参数**：

```json
{
  "validation_scope": "cross_layer",
  "models": ["L2_D01", "L3_D01", "L4_D90"],
  "documents": ["docs/README.md", "docs/CONTRIBUTING.md"],
  "consistency_rules": ["terminology", "structure", "content"]
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "validation_scope": "cross_layer",
    "overall_consistency": 0.92,
    "rule_results": {
      "terminology": {
        "score": 0.95,
        "status": "consistent",
        "details": "术语使用一致"
      },
      "structure": {
        "score": 0.90,
        "status": "consistent",
        "details": "结构组织一致"
      },
      "content": {
        "score": 0.90,
        "status": "consistent",
        "details": "内容逻辑一致"
      }
    },
    "inconsistencies": [
      {
        "type": "terminology",
        "severity": "low",
        "description": "部分术语定义略有差异",
        "suggestion": "统一术语定义"
      }
    ],
    "validated_at": "2024-12-19T10:00:00Z"
  },
  "message": "一致性验证完成"
}
```

## 5. 数据API

### 5.1 统计数据API

#### 5.1.1 获取项目统计

**接口**：`GET /stats/project`

**描述**：获取项目的整体统计数据

**请求参数**：

```json
{
  "include_details": true,
  "time_range": "all"
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "project_stats": {
      "total_documents": 50,
      "total_words": 200000,
      "total_lines": 10000,
      "total_models": 23,
      "total_evidence": 9,
      "total_tools": 5
    },
    "quality_stats": {
      "average_quality_score": 0.87,
      "quality_distribution": {
        "excellent": 15,
        "good": 25,
        "fair": 8,
        "poor": 2,
        "incomplete": 0
      }
    },
    "contribution_stats": {
      "total_contributors": 50,
      "active_contributors": 20,
      "total_commits": 500,
      "total_prs": 100
    },
    "generated_at": "2024-12-19T10:00:00Z"
  },
  "message": "项目统计获取成功"
}
```

#### 5.1.2 获取质量统计

**接口**：`GET /stats/quality`

**描述**：获取质量相关的统计数据

**请求参数**：

```json
{
  "dimension": "all",
  "time_range": "last_30_days",
  "include_trends": true
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "quality_stats": {
      "overall_score": 0.87,
      "dimension_scores": {
        "completeness": 0.85,
        "consistency": 0.90,
        "clarity": 0.80,
        "accuracy": 0.95,
        "usability": 0.85
      }
    },
    "trends": {
      "overall_score_trend": "improving",
      "dimension_trends": {
        "completeness": "stable",
        "consistency": "improving",
        "clarity": "improving",
        "accuracy": "stable",
        "usability": "improving"
      }
    },
    "quality_gates": {
      "passed_gates": 4,
      "total_gates": 5,
      "pass_rate": 0.80
    },
    "generated_at": "2024-12-19T10:00:00Z"
  },
  "message": "质量统计获取成功"
}
```

### 5.2 导出数据API

#### 5.2.1 导出文档数据

**接口**：`POST /export/documents`

**描述**：导出文档数据

**请求参数**：

```json
{
  "export_format": "json",
  "include_metadata": true,
  "include_content": true,
  "document_paths": ["docs/README.md", "docs/CONTRIBUTING.md"]
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "export_id": "EXP-20241219-001",
    "export_format": "json",
    "file_path": "exports/documents_20241219_001.json",
    "file_size": "2.5MB",
    "document_count": 2,
    "exported_at": "2024-12-19T10:00:00Z"
  },
  "message": "文档数据导出成功"
}
```

#### 5.2.2 导出模型数据

**接口**：`POST /export/models`

**描述**：导出模型数据

**请求参数**：

```json
{
  "export_format": "yaml",
  "include_relationships": true,
  "include_examples": true,
  "model_ids": ["L2_D01", "L3_D01"]
}
```

**响应数据**：

```json
{
  "success": true,
  "data": {
    "export_id": "EXP-20241219-002",
    "export_format": "yaml",
    "file_path": "exports/models_20241219_002.yaml",
    "file_size": "1.8MB",
    "model_count": 2,
    "exported_at": "2024-12-19T10:00:00Z"
  },
  "message": "模型数据导出成功"
}
```

## 6. 错误处理

### 6.1 错误码

#### 6.1.1 通用错误码

- **400 Bad Request**：请求参数错误
- **401 Unauthorized**：未授权访问
- **403 Forbidden**：禁止访问
- **404 Not Found**：资源不存在
- **429 Too Many Requests**：请求频率过高
- **500 Internal Server Error**：服务器内部错误

#### 6.1.2 业务错误码

- **1001**：模型不存在
- **1002**：模型验证失败
- **1003**：文档不存在
- **1004**：文档质量检查失败
- **1005**：证据条目不存在
- **1006**：证据条目验证失败

### 6.2 错误响应格式

```json
{
  "success": false,
  "error": {
    "code": 1001,
    "message": "模型不存在",
    "details": "指定的模型ID 'L2_D99' 不存在",
    "suggestion": "请检查模型ID是否正确，或查看可用模型列表"
  },
  "timestamp": "2024-12-19T10:00:00Z",
  "request_id": "req_123456789"
}
```

### 6.3 错误处理示例

#### 6.3.1 参数错误

```json
{
  "success": false,
  "error": {
    "code": 400,
    "message": "请求参数错误",
    "details": "缺少必需的参数 'model_id'",
    "suggestion": "请在请求中包含 'model_id' 参数"
  },
  "timestamp": "2024-12-19T10:00:00Z",
  "request_id": "req_123456789"
}
```

#### 6.3.2 验证失败

```json
{
  "success": false,
  "error": {
    "code": 1002,
    "message": "模型验证失败",
    "details": "模型语法错误：第15行第10列存在语法错误",
    "suggestion": "请检查模型语法，确保符合规范"
  },
  "timestamp": "2024-12-19T10:00:00Z",
  "request_id": "req_123456789"
}
```

## 7. 使用示例

### 7.1 Python客户端示例

```python
import requests
import json

class FormalFrameworkClient:
    def __init__(self, api_key, base_url="https://api.formal-framework.org/v1"):
        self.api_key = api_key
        self.base_url = base_url
        self.headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
            "Accept": "application/json"
        }
    
    def get_models(self, model_type="all", layer="all"):
        """获取模型列表"""
        params = {
            "model_type": model_type,
            "layer": layer,
            "limit": 50,
            "offset": 0
        }
        response = requests.get(
            f"{self.base_url}/models",
            headers=self.headers,
            params=params
        )
        return response.json()
    
    def get_model_detail(self, model_id):
        """获取模型详情"""
        response = requests.get(
            f"{self.base_url}/models/{model_id}",
            headers=self.headers
        )
        return response.json()
    
    def validate_model(self, model_id, validation_type="syntax"):
        """验证模型"""
        data = {
            "validation_level": "strict",
            "include_suggestions": True
        }
        response = requests.post(
            f"{self.base_url}/models/{model_id}/validate/{validation_type}",
            headers=self.headers,
            json=data
        )
        return response.json()
    
    def check_document_quality(self, document_path):
        """检查文档质量"""
        data = {
            "document_path": document_path,
            "check_dimensions": ["completeness", "consistency", "clarity", "accuracy", "usability"],
            "quality_threshold": 0.8
        }
        response = requests.post(
            f"{self.base_url}/tools/check-document-quality",
            headers=self.headers,
            json=data
        )
        return response.json()

# 使用示例
client = FormalFrameworkClient("your_api_key")

# 获取模型列表
models = client.get_models()
print(json.dumps(models, indent=2))

# 获取模型详情
model_detail = client.get_model_detail("L2_D01")
print(json.dumps(model_detail, indent=2))

# 验证模型
validation_result = client.validate_model("L2_D01")
print(json.dumps(validation_result, indent=2))

# 检查文档质量
quality_result = client.check_document_quality("docs/README.md")
print(json.dumps(quality_result, indent=2))
```

### 7.2 JavaScript客户端示例

```javascript
class FormalFrameworkClient {
    constructor(apiKey, baseUrl = 'https://api.formal-framework.org/v1') {
        this.apiKey = apiKey;
        this.baseUrl = baseUrl;
        this.headers = {
            'Content-Type': 'application/json',
            'Authorization': `Bearer ${apiKey}`,
            'Accept': 'application/json'
        };
    }
    
    async getModels(modelType = 'all', layer = 'all') {
        const params = new URLSearchParams({
            model_type: modelType,
            layer: layer,
            limit: 50,
            offset: 0
        });
        
        const response = await fetch(`${this.baseUrl}/models?${params}`, {
            headers: this.headers
        });
        
        return await response.json();
    }
    
    async getModelDetail(modelId) {
        const response = await fetch(`${this.baseUrl}/models/${modelId}`, {
            headers: this.headers
        });
        
        return await response.json();
    }
    
    async validateModel(modelId, validationType = 'syntax') {
        const data = {
            validation_level: 'strict',
            include_suggestions: true
        };
        
        const response = await fetch(`${this.baseUrl}/models/${modelId}/validate/${validationType}`, {
            method: 'POST',
            headers: this.headers,
            body: JSON.stringify(data)
        });
        
        return await response.json();
    }
    
    async checkDocumentQuality(documentPath) {
        const data = {
            document_path: documentPath,
            check_dimensions: ['completeness', 'consistency', 'clarity', 'accuracy', 'usability'],
            quality_threshold: 0.8
        };
        
        const response = await fetch(`${this.baseUrl}/tools/check-document-quality`, {
            method: 'POST',
            headers: this.headers,
            body: JSON.stringify(data)
        });
        
        return await response.json();
    }
}

// 使用示例
const client = new FormalFrameworkClient('your_api_key');

// 获取模型列表
client.getModels().then(models => {
    console.log(JSON.stringify(models, null, 2));
});

// 获取模型详情
client.getModelDetail('L2_D01').then(modelDetail => {
    console.log(JSON.stringify(modelDetail, null, 2));
});

// 验证模型
client.validateModel('L2_D01').then(validationResult => {
    console.log(JSON.stringify(validationResult, null, 2));
});

// 检查文档质量
client.checkDocumentQuality('docs/README.md').then(qualityResult => {
    console.log(JSON.stringify(qualityResult, null, 2));
});
```

## 8. 限制和配额

### 8.1 API限制

- **请求频率**：1000次/小时
- **并发请求**：10个/用户
- **请求大小**：10MB/请求
- **响应大小**：50MB/响应

### 8.2 配额管理

- **免费用户**：1000次API调用/月
- **付费用户**：10000次API调用/月
- **企业用户**：无限制API调用

### 8.3 使用建议

- **缓存结果**：合理缓存API响应结果
- **批量操作**：使用批量API减少请求次数
- **错误重试**：实现指数退避重试机制
- **监控使用**：监控API使用情况和配额

---

**API文档**提供了形式化框架项目的完整API接口说明，包括工具API、模型API、验证API等核心接口。通过API，您可以：

1. **自动化集成**：将形式化框架集成到您的开发流程中
2. **批量处理**：批量处理文档和模型
3. **质量监控**：实时监控项目质量
4. **自定义工具**：基于API开发自定义工具

如果您需要更多帮助或有任何问题，请随时联系我们的技术支持团队！

*最后更新：2024-12-19*-
