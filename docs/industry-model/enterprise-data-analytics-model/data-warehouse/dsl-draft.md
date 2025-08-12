# 数据仓库DSL设计草案

## 1 DSL概述

数据仓库DSL（Domain Specific Language）旨在提供一种声明式、维度化的方式来描述数据仓库配置，支持跨平台的数据仓库代码生成和自动化管理。

## 2 核心语法设计

### 2.1 基础语法结构

```yaml
data_warehouse:
  name: "企业数据仓库"
  version: "1.0.0"
  platform: "snowflake" | "redshift" | "bigquery" | "synapse"
  modeling:
    facts: [...]
    dimensions: [...]
    aggregations: [...]
  etl:
    pipelines: [...]
    schedules: [...]
  olap:
    cubes: [...]
    queries: [...]
  performance:
    indexes: [...]
    partitions: [...]
```

### 2.2 维度建模语法

```yaml
modeling:
  facts:
    - name: "sales_fact"
      description: "销售事实表"
      grain: "每个销售订单行项目"
      measures:
        - name: "sales_amount"
          type: "decimal(18,2)"
          aggregation: "sum"
          description: "销售金额"
        - name: "sales_quantity"
          type: "integer"
          aggregation: "sum"
          description: "销售数量"
        - name: "unit_price"
          type: "decimal(10,2)"
          aggregation: "avg"
          description: "单价"
      dimensions:
        - name: "date_dim"
          type: "degenerate"
          key: "date_key"
        - name: "product_dim"
          type: "regular"
          key: "product_key"
        - name: "customer_dim"
          type: "regular"
          key: "customer_key"
        - name: "store_dim"
          type: "regular"
          key: "store_key"
  
  dimensions:
    - name: "date_dim"
      description: "日期维度表"
      type: "time"
      key: "date_key"
      attributes:
        - name: "date_key"
          type: "integer"
          primary_key: true
        - name: "full_date"
          type: "date"
          description: "完整日期"
        - name: "year"
          type: "integer"
          description: "年份"
        - name: "quarter"
          type: "integer"
          description: "季度"
        - name: "month"
          type: "integer"
          description: "月份"
        - name: "day_of_week"
          type: "integer"
          description: "星期几"
      hierarchies:
        - name: "calendar"
          levels: ["year", "quarter", "month", "day"]
    
    - name: "product_dim"
      description: "产品维度表"
      type: "conformed"
      key: "product_key"
      attributes:
        - name: "product_key"
          type: "integer"
          primary_key: true
        - name: "product_id"
          type: "string"
          description: "产品ID"
        - name: "product_name"
          type: "string"
          description: "产品名称"
        - name: "category"
          type: "string"
          description: "产品类别"
        - name: "brand"
          type: "string"
          description: "品牌"
        - name: "price"
          type: "decimal(10,2)"
          description: "价格"
      scd:
        type: "type2"
        start_date: "effective_date"
        end_date: "expiry_date"
        current_flag: "is_current"
      hierarchies:
        - name: "product"
          levels: ["category", "brand", "product"]
    
    - name: "customer_dim"
      description: "客户维度表"
      type: "conformed"
      key: "customer_key"
      attributes:
        - name: "customer_key"
          type: "integer"
          primary_key: true
        - name: "customer_id"
          type: "string"
          description: "客户ID"
        - name: "customer_name"
          type: "string"
          description: "客户名称"
        - name: "email"
          type: "string"
          description: "邮箱"
        - name: "phone"
          type: "string"
          description: "电话"
        - name: "address"
          type: "string"
          description: "地址"
        - name: "city"
          type: "string"
          description: "城市"
        - name: "state"
          type: "string"
          description: "州/省"
        - name: "country"
          type: "string"
          description: "国家"
      scd:
        type: "type1"
        update_strategy: "overwrite"
      hierarchies:
        - name: "geography"
          levels: ["country", "state", "city"]
```

### 2.3 ETL流程语法

```yaml
etl:
  pipelines:
    - name: "sales_etl"
      description: "销售数据ETL流程"
      type: "incremental"
      
      extract:
        - name: "extract_sales"
          type: "database"
          source:
            connection: "sales_db"
            query: |
              SELECT 
                order_id,
                product_id,
                customer_id,
                store_id,
                order_date,
                quantity,
                unit_price,
                total_amount
              FROM sales_orders
              WHERE order_date >= '${last_run_date}'
            incremental_column: "order_date"
            watermark_table: "etl_watermark"
            watermark_column: "sales_last_update"
      
      transform:
        - name: "clean_sales_data"
          type: "data_quality"
          rules:
            - rule: "quantity > 0"
              action: "filter"
            - rule: "unit_price > 0"
              action: "filter"
            - rule: "order_date IS NOT NULL"
              action: "filter"
        
        - name: "enrich_sales_data"
          type: "lookup"
          lookups:
            - name: "product_lookup"
              source: "product_dim"
              join_key: "product_id"
              target_key: "product_key"
            - name: "customer_lookup"
              source: "customer_dim"
              join_key: "customer_id"
              target_key: "customer_key"
            - name: "date_lookup"
              source: "date_dim"
              join_key: "order_date"
              target_key: "date_key"
        
        - name: "calculate_measures"
          type: "calculation"
          calculations:
            - name: "sales_amount"
              expression: "quantity * unit_price"
            - name: "discount_amount"
              expression: "CASE WHEN total_amount > sales_amount THEN total_amount - sales_amount ELSE 0 END"
      
      load:
        - name: "load_sales_fact"
          type: "table"
          target: "sales_fact"
          strategy: "merge"
          merge_key: ["order_id", "product_id"]
          columns:
            - source: "order_id"
              target: "order_id"
            - source: "product_key"
              target: "product_key"
            - source: "customer_key"
              target: "customer_key"
            - source: "date_key"
              target: "date_key"
            - source: "quantity"
              target: "sales_quantity"
            - source: "unit_price"
              target: "unit_price"
            - source: "sales_amount"
              target: "sales_amount"
      
      schedule:
        frequency: "daily"
        time: "02:00"
        timezone: "UTC"
        dependencies:
          - "product_dim_etl"
          - "customer_dim_etl"
      
      monitoring:
        success_criteria:
          - metric: "record_count"
            operator: ">"
            value: 0
          - metric: "data_freshness"
            operator: "<"
            value: "24 hours"
        alerts:
          - condition: "record_count = 0"
            severity: "critical"
            notification: "email"
          - condition: "execution_time > 2 hours"
            severity: "warning"
            notification: "slack"
```

### 2.4 OLAP立方体语法

```yaml
olap:
  cubes:
    - name: "sales_cube"
      description: "销售分析立方体"
      fact_table: "sales_fact"
      dimensions:
        - name: "time"
          source: "date_dim"
          hierarchies:
            - name: "calendar"
              levels: ["year", "quarter", "month", "day"]
        - name: "product"
          source: "product_dim"
          hierarchies:
            - name: "product"
              levels: ["category", "brand", "product"]
        - name: "customer"
          source: "customer_dim"
          hierarchies:
            - name: "geography"
              levels: ["country", "state", "city"]
      measures:
        - name: "sales_amount"
          source: "sales_amount"
          aggregation: "sum"
          format: "currency"
        - name: "sales_quantity"
          source: "sales_quantity"
          aggregation: "sum"
          format: "number"
        - name: "avg_unit_price"
          source: "unit_price"
          aggregation: "avg"
          format: "currency"
        - name: "order_count"
          source: "order_id"
          aggregation: "count_distinct"
          format: "number"
      aggregations:
        - name: "daily_sales"
          dimensions: ["time.day", "product.category", "customer.country"]
          measures: ["sales_amount", "sales_quantity"]
        - name: "monthly_sales"
          dimensions: ["time.month", "product.brand", "customer.state"]
          measures: ["sales_amount", "sales_quantity"]
        - name: "quarterly_sales"
          dimensions: ["time.quarter", "product.category", "customer.country"]
          measures: ["sales_amount", "sales_quantity"]
  
  queries:
    - name: "top_products_by_sales"
      description: "按销售额排名前10的产品"
      cube: "sales_cube"
      mdx: |
        SELECT 
          {[Measures].[sales_amount]} ON COLUMNS,
          TOPCOUNT([Product].[Product].Members, 10, [Measures].[sales_amount]) ON ROWS
        FROM [sales_cube]
        WHERE [Time].[2024]
    
    - name: "sales_trend_by_month"
      description: "按月份销售趋势"
      cube: "sales_cube"
      mdx: |
        SELECT 
          {[Measures].[sales_amount]} ON COLUMNS,
          {[Time].[2024].[Q1].Children} ON ROWS
        FROM [sales_cube]
        WHERE [Product].[Category].[Electronics]
```

### 2.5 性能优化语法

```yaml
performance:
  indexes:
    - name: "idx_sales_fact_date"
      table: "sales_fact"
      columns: ["date_key"]
      type: "btree"
      unique: false
    
    - name: "idx_sales_fact_product"
      table: "sales_fact"
      columns: ["product_key"]
      type: "btree"
      unique: false
    
    - name: "idx_sales_fact_customer"
      table: "sales_fact"
      columns: ["customer_key"]
      type: "btree"
      unique: false
    
    - name: "idx_sales_fact_composite"
      table: "sales_fact"
      columns: ["date_key", "product_key", "customer_key"]
      type: "btree"
      unique: false
  
  partitions:
    - name: "sales_fact_partition"
      table: "sales_fact"
      strategy:
        type: "range"
        column: "date_key"
        ranges:
          - name: "2024_q1"
            start: 20240101
            end: 20240331
          - name: "2024_q2"
            start: 20240401
            end: 20240630
          - name: "2024_q3"
            start: 20240701
            end: 20240930
          - name: "2024_q4"
            start: 20241001
            end: 20241231
  
  caching:
    - name: "sales_cube_cache"
      cube: "sales_cube"
      strategy: "mrolap"
      storage: "memory"
      refresh_schedule: "daily"
      refresh_time: "03:00"
    
    - name: "frequently_used_queries"
      queries: ["top_products_by_sales", "sales_trend_by_month"]
      strategy: "query_cache"
      ttl: "1 hour"
```

### 2.6 数据质量语法

```yaml
data_quality:
  rules:
    - name: "sales_amount_positive"
      table: "sales_fact"
      column: "sales_amount"
      rule: "sales_amount > 0"
      severity: "error"
      action: "reject"
    
    - name: "product_key_not_null"
      table: "sales_fact"
      column: "product_key"
      rule: "product_key IS NOT NULL"
      severity: "error"
      action: "reject"
    
    - name: "date_key_valid"
      table: "sales_fact"
      column: "date_key"
      rule: "date_key BETWEEN 20240101 AND 20241231"
      severity: "warning"
      action: "flag"
  
  monitoring:
    - name: "daily_data_quality_check"
      schedule: "daily"
      time: "06:00"
      rules: ["sales_amount_positive", "product_key_not_null", "date_key_valid"]
      reporting:
        - type: "email"
          recipients: ["data-team@company.com"]
        - type: "dashboard"
          url: "https://dashboard.company.com/data-quality"
```

## 3 高级特性

### 3.1 动态分区

```yaml
partitions:
  - name: "auto_partition_sales"
    table: "sales_fact"
    strategy:
      type: "auto"
      column: "date_key"
      interval: "month"
      retention: "36 months"
      archival:
        enabled: true
        storage_class: "cold"
        archival_days: 1095
```

### 3.2 智能索引

```yaml
indexes:
  - name: "adaptive_index_sales"
    table: "sales_fact"
    strategy:
      type: "adaptive"
      columns: ["date_key", "product_key", "customer_key"]
      usage_threshold: 0.1
      creation_threshold: 0.05
      monitoring_interval: "daily"
```

### 3.3 数据血缘追踪

```yaml
lineage:
  enabled: true
  tracking:
    - source: "sales_orders"
      target: "sales_fact"
      transformation: "sales_etl"
      columns:
        - source: "order_id"
          target: "order_id"
        - source: "product_id"
          target: "product_key"
          transformation: "product_lookup"
        - source: "quantity * unit_price"
          target: "sales_amount"
          transformation: "calculation"
```

## 4 代码生成模板

### 4.1 Snowflake生成模板

```sql
-- 生成的Snowflake DDL代码示例

-- 创建日期维度表
CREATE OR REPLACE TABLE date_dim (
    date_key INTEGER PRIMARY KEY,
    full_date DATE NOT NULL,
    year INTEGER NOT NULL,
    quarter INTEGER NOT NULL,
    month INTEGER NOT NULL,
    day_of_week INTEGER NOT NULL,
    created_at TIMESTAMP_NTZ DEFAULT CURRENT_TIMESTAMP(),
    updated_at TIMESTAMP_NTZ DEFAULT CURRENT_TIMESTAMP()
);

-- 创建产品维度表
CREATE OR REPLACE TABLE product_dim (
    product_key INTEGER PRIMARY KEY,
    product_id STRING NOT NULL,
    product_name STRING NOT NULL,
    category STRING,
    brand STRING,
    price DECIMAL(10,2),
    effective_date DATE NOT NULL,
    expiry_date DATE,
    is_current BOOLEAN DEFAULT TRUE,
    created_at TIMESTAMP_NTZ DEFAULT CURRENT_TIMESTAMP(),
    updated_at TIMESTAMP_NTZ DEFAULT CURRENT_TIMESTAMP()
);

-- 创建销售事实表
CREATE OR REPLACE TABLE sales_fact (
    order_id STRING NOT NULL,
    product_key INTEGER NOT NULL,
    customer_key INTEGER NOT NULL,
    date_key INTEGER NOT NULL,
    sales_quantity INTEGER NOT NULL,
    unit_price DECIMAL(10,2) NOT NULL,
    sales_amount DECIMAL(18,2) NOT NULL,
    created_at TIMESTAMP_NTZ DEFAULT CURRENT_TIMESTAMP(),
    FOREIGN KEY (product_key) REFERENCES product_dim(product_key),
    FOREIGN KEY (customer_key) REFERENCES customer_dim(customer_key),
    FOREIGN KEY (date_key) REFERENCES date_dim(date_key)
);

-- 创建分区
ALTER TABLE sales_fact ADD PARTITION (date_key = 20240101);
ALTER TABLE sales_fact ADD PARTITION (date_key = 20240102);
-- ... 更多分区

-- 创建索引
CREATE INDEX idx_sales_fact_date ON sales_fact(date_key);
CREATE INDEX idx_sales_fact_product ON sales_fact(product_key);
CREATE INDEX idx_sales_fact_customer ON sales_fact(customer_key);
```

### 4.2 ETL生成模板

```python
# 生成的Python ETL代码示例
import snowflake.connector
import pandas as pd
from datetime import datetime, timedelta

def extract_sales_data(last_run_date):
    """提取销售数据"""
    conn = snowflake.connector.connect(
        user='${SNOWFLAKE_USER}',
        password='${SNOWFLAKE_PASSWORD}',
        account='${SNOWFLAKE_ACCOUNT}',
        warehouse='${SNOWFLAKE_WAREHOUSE}',
        database='${SNOWFLAKE_DATABASE}',
        schema='${SNOWFLAKE_SCHEMA}'
    )
    
    query = f"""
    SELECT 
        order_id,
        product_id,
        customer_id,
        store_id,
        order_date,
        quantity,
        unit_price,
        total_amount
    FROM sales_orders
    WHERE order_date >= '{last_run_date}'
    """
    
    df = pd.read_sql(query, conn)
    conn.close()
    return df

def transform_sales_data(df):
    """转换销售数据"""
    # 数据清洗
    df = df[df['quantity'] > 0]
    df = df[df['unit_price'] > 0]
    df = df[df['order_date'].notna()]
    
    # 计算销售额
    df['sales_amount'] = df['quantity'] * df['unit_price']
    
    # 查找维度键
    df = lookup_dimension_keys(df)
    
    return df

def load_sales_fact(df):
    """加载销售事实表"""
    conn = snowflake.connector.connect(
        user='${SNOWFLAKE_USER}',
        password='${SNOWFLAKE_PASSWORD}',
        account='${SNOWFLAKE_ACCOUNT}',
        warehouse='${SNOWFLAKE_WAREHOUSE}',
        database='${SNOWFLAKE_DATABASE}',
        schema='${SNOWFLAKE_SCHEMA}'
    )
    
    # 合并数据
    merge_query = """
    MERGE INTO sales_fact AS target
    USING (SELECT * FROM VALUES {}) AS source
    ON target.order_id = source.order_id AND target.product_key = source.product_key
    WHEN MATCHED THEN
        UPDATE SET
            customer_key = source.customer_key,
            date_key = source.date_key,
            sales_quantity = source.sales_quantity,
            unit_price = source.unit_price,
            sales_amount = source.sales_amount,
            updated_at = CURRENT_TIMESTAMP()
    WHEN NOT MATCHED THEN
        INSERT (order_id, product_key, customer_key, date_key, sales_quantity, unit_price, sales_amount)
        VALUES (source.order_id, source.product_key, source.customer_key, source.date_key, source.sales_quantity, source.unit_price, source.sales_amount)
    """
    
    conn.cursor().execute(merge_query)
    conn.commit()
    conn.close()

def main():
    """主函数"""
    last_run_date = get_last_run_date()
    
    # 提取
    df = extract_sales_data(last_run_date)
    
    # 转换
    df = transform_sales_data(df)
    
    # 加载
    load_sales_fact(df)
    
    # 更新水印
    update_watermark('sales_last_update', datetime.now())

if __name__ == "__main__":
    main()
```

## 5 验证规则

### 5.1 语法验证

```yaml
validation:
  required_fields:
    - data_warehouse.name
    - data_warehouse.platform
    - data_warehouse.modeling.facts
    - data_warehouse.modeling.dimensions
  
  type_constraints:
    - field: "data_warehouse.platform"
      allowed_values: ["snowflake", "redshift", "bigquery", "synapse"]
    - field: "modeling.facts[].measures[].type"
      allowed_values: ["integer", "decimal", "string", "date", "timestamp"]
    - field: "modeling.dimensions[].scd.type"
      allowed_values: ["type1", "type2", "type3"]
  
  business_rules:
    - rule: "facts[].dimensions[].key must reference existing dimension"
    - rule: "etl.pipelines[].extract[].source must be valid"
    - rule: "olap.cubes[].fact_table must reference existing fact table"
```

### 5.2 性能约束

```yaml
performance:
  max_table_size: "1TB"
  max_partition_count: 1000
  query_timeout: "300 seconds"
  etl_timeout: "2 hours"
  
  optimization:
    auto_clustering: true
    auto_scaling: true
    query_optimization: true
    materialized_views: true
```

## 6 扩展机制

### 6.1 自定义转换器

```yaml
custom_transformers:
  - name: "custom_data_quality"
    type: "custom"
    class: "com.company.CustomDataQualityTransformer"
    config:
      rules_file: "/config/quality_rules.json"
      threshold: 0.95
  
  - name: "custom_enrichment"
    type: "custom"
    class: "com.company.CustomEnrichmentTransformer"
    config:
      api_endpoint: "https://api.company.com/enrich"
      api_key: "${API_KEY}"
      timeout: "30 seconds"
```

### 6.2 插件系统

```yaml
plugins:
  - name: "data_profiling"
    version: "1.0.0"
    config:
      enabled: true
      sample_size: 10000
      output_format: "html"
  
  - name: "data_masking"
    version: "1.0.0"
    config:
      enabled: true
      masking_rules: [...]
      preserve_format: true
```

## 7 工具链集成

### 7.1 开发工具

- **DSL编辑器**: 语法高亮、自动补全、错误提示
- **数据仓库浏览器**: 可视化浏览数据仓库结构
- **配置验证**: 实时验证配置的正确性
- **代码生成**: 一键生成目标平台代码

### 7.2 部署工具

- **基础设施即代码**: 自动生成Terraform/CloudFormation配置
- **配置管理**: 管理不同环境的配置
- **版本管理**: 管理不同版本的数据仓库配置
- **回滚机制**: 支持快速回滚到之前的版本

### 7.3 运维工具

- **监控面板**: 实时监控数据仓库状态
- **性能分析**: 分析查询性能和ETL性能
- **成本分析**: 分析存储和计算成本
- **容量规划**: 预测存储需求和增长趋势

这个DSL设计为数据仓库提供了完整的配置语言，支持从简单的表结构到复杂的OLAP立方体的各种需求，同时保持了良好的可扩展性和可维护性。
