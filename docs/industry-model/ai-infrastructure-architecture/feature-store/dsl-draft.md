# 特征库 DSL 草案

## 1. 概述

### 1.1 目标与范围

- 定义特征库系统的DSL规范
- 支持特征定义、版本管理、存储、检索等功能
- 提供特征工程、特征服务、特征监控的形式化描述

### 1.2 核心概念

- **特征**：机器学习模型使用的数据属性
- **特征库**：存储和管理特征的系统
- **特征版本**：特征的时间版本控制
- **特征服务**：在线特征检索和计算服务

## 2. 结构定义

### 2.1 顶层对象

```yaml
feature_store:
  name: string
  version: string
  features: Feature[]
  storage: StorageConfig
  serving: ServingConfig
  monitoring: MonitoringConfig
```

### 2.2 特征定义（Feature）

```yaml
feature:
  name: string
  type: "numeric" | "categorical" | "text" | "embedding"
  data_type: "int" | "float" | "string" | "array"
  description: string
  version: string
  source: DataSource
  transformation: TransformationConfig
  validation: ValidationConfig
```

### 2.3 数据源配置（DataSource）

```yaml
data_source:
  type: "batch" | "streaming" | "real_time"
  location: string
  format: "parquet" | "csv" | "json" | "avro"
  schema: SchemaConfig
  partition: PartitionConfig
```

### 2.4 转换配置（TransformationConfig）

```yaml
transformation_config:
  type: "aggregation" | "normalization" | "encoding" | "custom"
  parameters: object
  window: WindowConfig
  custom_function: string
```

### 2.5 存储配置（StorageConfig）

```yaml
storage_config:
  offline_store:
    type: "hive" | "s3" | "gcs" | "adls"
    path: string
    format: "parquet" | "delta"
  online_store:
    type: "redis" | "dynamodb" | "cassandra"
    connection: ConnectionConfig
```

### 2.6 服务配置（ServingConfig）

```yaml
serving_config:
  api_endpoint: string
  batch_size: int
  timeout: int
  cache: CacheConfig
  load_balancing: LoadBalancingConfig
```

### 2.7 监控配置（MonitoringConfig）

```yaml
monitoring_config:
  metrics:
    - "feature_freshness"
    - "feature_quality"
    - "serving_latency"
    - "feature_usage"
  alerts:
    - "data_drift"
    - "feature_unavailable"
    - "quality_degradation"
```

## 3. 字段说明

### 3.1 特征定义字段

- **name**: 特征名称，全局唯一标识符
- **type**: 特征类型，支持数值、分类、文本、嵌入等
- **data_type**: 数据类型，定义特征的具体数据格式
- **version**: 特征版本，支持时间戳或语义化版本
- **source**: 数据源配置，定义特征数据的来源
- **transformation**: 转换配置，定义特征的计算逻辑

### 3.2 数据源字段

- **type**: 数据源类型，支持批处理、流处理、实时处理
- **location**: 数据位置，可以是文件路径、数据库连接等
- **format**: 数据格式，支持多种存储格式
- **schema**: 数据模式定义，包括字段类型和约束

### 3.3 转换配置字段

- **type**: 转换类型，支持聚合、归一化、编码等
- **parameters**: 转换参数，定义具体的转换逻辑
- **window**: 时间窗口配置，用于时间序列特征
- **custom_function**: 自定义函数，支持复杂的特征计算

## 4. 示例

### 4.1 用户特征示例

```yaml
feature_store:
  name: "user_features"
  version: "1.0.0"
  features:
    - name: "user_age"
      type: "numeric"
      data_type: "int"
      description: "用户年龄"
      version: "2024-01-01"
      source:
        type: "batch"
        location: "s3://data/user_profiles"
        format: "parquet"
      transformation:
        type: "custom"
        custom_function: "age_bucket"
    
    - name: "user_purchase_frequency"
      type: "numeric"
      data_type: "float"
      description: "用户购买频率"
      version: "2024-01-01"
      source:
        type: "streaming"
        location: "kafka://orders"
        format: "json"
      transformation:
        type: "aggregation"
        parameters:
          window: "30d"
          function: "count"
  
  storage:
    offline_store:
      type: "s3"
      path: "s3://feature-store/offline"
      format: "parquet"
    online_store:
      type: "redis"
      connection:
        host: "redis-cluster"
        port: 6379
  
  serving:
    api_endpoint: "https://feature-service.example.com"
    batch_size: 100
    timeout: 5000
  
  monitoring:
    metrics: ["feature_freshness", "serving_latency"]
    alerts: ["data_drift", "feature_unavailable"]
```

### 4.2 商品特征示例

```yaml
feature_store:
  name: "product_features"
  version: "1.0.0"
  features:
    - name: "product_category"
      type: "categorical"
      data_type: "string"
      description: "商品类别"
      version: "2024-01-01"
      source:
        type: "batch"
        location: "s3://data/products"
        format: "parquet"
      transformation:
        type: "encoding"
        parameters:
          method: "label_encoding"
    
    - name: "product_price"
      type: "numeric"
      data_type: "float"
      description: "商品价格"
      version: "2024-01-01"
      source:
        type: "batch"
        location: "s3://data/products"
        format: "parquet"
      transformation:
        type: "normalization"
        parameters:
          method: "min_max"
          min: 0
          max: 10000
```

### 4.3 实时特征示例

```yaml
feature_store:
  name: "real_time_features"
  version: "1.0.0"
  features:
    - name: "session_duration"
      type: "numeric"
      data_type: "float"
      description: "会话持续时间"
      version: "2024-01-01"
      source:
        type: "streaming"
        location: "kafka://user_sessions"
        format: "json"
      transformation:
        type: "aggregation"
        parameters:
          window: "1h"
          function: "avg"
    
    - name: "current_location"
      type: "categorical"
      data_type: "string"
      description: "当前位置"
      version: "2024-01-01"
      source:
        type: "real_time"
        location: "api://location_service"
        format: "json"
      transformation:
        type: "custom"
        custom_function: "location_encoder"
```

## 5. 自动化推理伪代码

### 5.1 特征依赖分析

```python
def analyze_feature_dependencies(features):
    dependencies = {}
    for feature in features:
        deps = []
        if feature.source.type == "streaming":
            deps.extend(analyze_streaming_deps(feature))
        if feature.transformation.type == "aggregation":
            deps.extend(analyze_aggregation_deps(feature))
        dependencies[feature.name] = deps
    return dependencies

def analyze_streaming_deps(feature):
    # 分析流式数据依赖
    return [feature.source.location]
```

### 5.2 特征质量评估

```python
def evaluate_feature_quality(feature, data):
    quality_metrics = {}
    
    # 完整性检查
    quality_metrics['completeness'] = calculate_completeness(data)
    
    # 一致性检查
    quality_metrics['consistency'] = calculate_consistency(data, feature.validation)
    
    # 准确性检查
    quality_metrics['accuracy'] = calculate_accuracy(data, feature.validation)
    
    return quality_metrics
```

### 5.3 特征版本管理

```python
def manage_feature_versions(feature_store):
    versions = {}
    for feature in feature_store.features:
        if feature.name not in versions:
            versions[feature.name] = []
        versions[feature.name].append({
            'version': feature.version,
            'timestamp': get_timestamp(feature.version),
            'changes': get_changes(feature)
        })
    return versions
```

## 6. 自动化生成脚本片段

### 6.1 特征服务API生成

```python
def generate_feature_service_api(feature_store):
    api_code = """
from fastapi import FastAPI
import redis

app = FastAPI()
redis_client = redis.Redis(host='localhost', port=6379)

"""
    
    for feature in feature_store.features:
        api_code += f"""
@app.get("/features/{feature.name}")
async def get_{feature.name}(entity_id: str):
    return redis_client.hget("features", f"{{entity_id}}:{feature.name}")
"""
    
    return api_code
```

### 6.2 特征计算脚本生成

```python
def generate_feature_computation_script(feature):
    script = f"""
def compute_{feature.name}(data):
    # 数据源读取
    source_data = read_from_source('{feature.source.location}')
    
    # 特征转换
    if '{feature.transformation.type}' == 'aggregation':
        result = aggregate_data(source_data, {feature.transformation.parameters})
    elif '{feature.transformation.type}' == 'normalization':
        result = normalize_data(source_data, {feature.transformation.parameters})
    else:
        result = custom_transform(source_data, '{feature.transformation.custom_function}')
    
    return result
"""
    return script
```

## 7. 模板使用说明

### 7.1 复制此模板到新模型目录

- 将此DSL草案作为特征库模型的基础模板
- 根据具体需求修改结构定义和字段说明
- 补充实际示例和自动化推理伪代码

### 7.2 根据具体需求修改

- 调整特征类型和数据类型
- 修改数据源配置和转换逻辑
- 优化存储配置和服务配置

### 7.3 补充实际示例

- 添加行业特定的特征场景
- 包含特征工程和特征服务案例
- 提供完整的端到端特征流程

### 7.4 删除可选部分

- 保留必要的结构定义和字段说明
- 删除不相关的示例和配置
- 确保DSL的简洁性和可读性
