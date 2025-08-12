# BI报表DSL设计草案

## 1 DSL概述

BI报表DSL（Domain Specific Language）旨在提供一种声明式、可视化的方式来描述BI报表配置，支持跨平台的BI报表代码生成和自动化管理。

## 2 核心语法设计

### 2.1 基础语法结构

```yaml
bi_reporting:
  name: "企业BI报表系统"
  version: "1.0.0"
  platform: "tableau" | "powerbi" | "qlik" | "looker"
  data_sources:
    connections: [...]
    models: [...]
  reports:
    reports: [...]
    dashboards: [...]
  users:
    roles: [...]
    permissions: [...]
  scheduling:
    schedules: [...]
    distributions: [...]
```

### 2.2 数据源配置语法

```yaml
data_sources:
  connections:
    - name: "sales_database"
      type: "database"
      platform: "snowflake"
      config:
        host: "company.snowflakecomputing.com"
        database: "SALES_DB"
        schema: "PUBLIC"
        warehouse: "ANALYTICS_WH"
        role: "ANALYST_ROLE"
        authentication: "oauth"
    
    - name: "marketing_api"
      type: "api"
      platform: "rest"
      config:
        base_url: "https://api.marketing.company.com"
        authentication: "bearer_token"
        token: "${MARKETING_API_TOKEN}"
        rate_limit: 1000
    
    - name: "customer_files"
      type: "file"
      platform: "s3"
      config:
        bucket: "customer-data"
        prefix: "reports/"
        format: "csv"
        compression: "gzip"
  
  models:
    - name: "sales_model"
      description: "销售数据模型"
      source: "sales_database"
      tables:
        - name: "sales_fact"
          alias: "Sales"
          columns:
            - name: "order_id"
              type: "string"
              description: "订单ID"
            - name: "order_date"
              type: "date"
              description: "订单日期"
            - name: "product_id"
              type: "string"
              description: "产品ID"
            - name: "customer_id"
              type: "string"
              description: "客户ID"
            - name: "quantity"
              type: "integer"
              description: "数量"
            - name: "unit_price"
              type: "decimal"
              description: "单价"
            - name: "total_amount"
              type: "decimal"
              description: "总金额"
      
      relationships:
        - name: "product_relationship"
          from_table: "sales_fact"
          from_column: "product_id"
          to_table: "product_dim"
          to_column: "product_id"
          type: "many_to_one"
        
        - name: "customer_relationship"
          from_table: "sales_fact"
          from_column: "customer_id"
          to_table: "customer_dim"
          to_column: "customer_id"
          type: "many_to_one"
      
      calculated_fields:
        - name: "profit_margin"
          expression: "(total_amount - (quantity * cost_price)) / total_amount"
          type: "percentage"
          description: "利润率"
        
        - name: "sales_rank"
          expression: "RANK() OVER (PARTITION BY product_id ORDER BY total_amount DESC)"
          type: "integer"
          description: "销售排名"
```

### 2.3 报表设计语法

```yaml
reports:
  reports:
    - name: "monthly_sales_report"
      description: "月度销售报表"
      type: "tabular"
      data_source: "sales_model"
      
      structure:
        title: "月度销售报表"
        subtitle: "按产品类别统计"
        header:
          - field: "company_logo"
            type: "image"
            position: "left"
          - field: "report_date"
            type: "text"
            position: "right"
            format: "YYYY年MM月DD日"
        
        sections:
          - name: "summary"
            type: "summary"
            layout: "horizontal"
            components:
              - name: "total_sales"
                type: "metric"
                field: "total_amount"
                aggregation: "sum"
                format: "currency"
                label: "总销售额"
              - name: "total_orders"
                type: "metric"
                field: "order_id"
                aggregation: "count_distinct"
                format: "number"
                label: "总订单数"
              - name: "avg_order_value"
                type: "metric"
                field: "total_amount"
                aggregation: "avg"
                format: "currency"
                label: "平均订单金额"
          
          - name: "details"
            type: "table"
            data:
              query: |
                SELECT 
                  product_category,
                  SUM(total_amount) as sales_amount,
                  COUNT(DISTINCT order_id) as order_count,
                  AVG(total_amount) as avg_order_value
                FROM sales_fact
                JOIN product_dim ON sales_fact.product_id = product_dim.product_id
                WHERE order_date >= '${start_date}' AND order_date <= '${end_date}'
                GROUP BY product_category
                ORDER BY sales_amount DESC
            columns:
              - name: "product_category"
                header: "产品类别"
                width: 200
                alignment: "left"
              - name: "sales_amount"
                header: "销售额"
                width: 150
                alignment: "right"
                format: "currency"
              - name: "order_count"
                header: "订单数"
                width: 120
                alignment: "center"
                format: "number"
              - name: "avg_order_value"
                header: "平均订单金额"
                width: 150
                alignment: "right"
                format: "currency"
        
        footer:
          - field: "page_number"
            type: "text"
            position: "center"
            format: "第 {page} 页，共 {total_pages} 页"
          - field: "generated_time"
            type: "text"
            position: "right"
            format: "生成时间：{datetime}"
      
      parameters:
        - name: "start_date"
          type: "date"
          default: "2024-01-01"
          label: "开始日期"
        - name: "end_date"
          type: "date"
          default: "2024-12-31"
          label: "结束日期"
        - name: "product_category"
          type: "multi_select"
          source: "product_dim.product_category"
          label: "产品类别"
      
      filters:
        - name: "date_filter"
          field: "order_date"
          type: "date_range"
          default: "last_30_days"
        - name: "region_filter"
          field: "customer_region"
          type: "multi_select"
          default: "all"
```

### 2.4 仪表盘设计语法

```yaml
dashboards:
  - name: "executive_dashboard"
    description: "高管仪表盘"
    layout:
      type: "grid"
      columns: 4
      rows: 3
      gap: 16
    
    components:
      - name: "kpi_summary"
        type: "metrics"
        position: [0, 0, 4, 1]
        layout: "horizontal"
        metrics:
          - name: "total_revenue"
            field: "total_amount"
            aggregation: "sum"
            format: "currency"
            label: "总收入"
            trend: "month_over_month"
          - name: "total_customers"
            field: "customer_id"
            aggregation: "count_distinct"
            format: "number"
            label: "客户总数"
            trend: "month_over_month"
          - name: "avg_order_value"
            field: "total_amount"
            aggregation: "avg"
            format: "currency"
            label: "平均订单金额"
            trend: "month_over_month"
          - name: "conversion_rate"
            field: "conversion_rate"
            aggregation: "avg"
            format: "percentage"
            label: "转化率"
            trend: "month_over_month"
      
      - name: "sales_trend"
        type: "line_chart"
        position: [0, 1, 2, 2]
        data:
          query: |
            SELECT 
              DATE_TRUNC('month', order_date) as month,
              SUM(total_amount) as revenue
            FROM sales_fact
            WHERE order_date >= DATEADD(month, -12, CURRENT_DATE())
            GROUP BY DATE_TRUNC('month', order_date)
            ORDER BY month
        config:
          x_axis: "month"
          y_axis: "revenue"
          title: "月度销售趋势"
          show_grid: true
          show_legend: false
      
      - name: "product_performance"
        type: "bar_chart"
        position: [2, 1, 2, 2]
        data:
          query: |
            SELECT 
              product_category,
              SUM(total_amount) as revenue
            FROM sales_fact
            JOIN product_dim ON sales_fact.product_id = product_dim.product_id
            WHERE order_date >= DATEADD(month, -1, CURRENT_DATE())
            GROUP BY product_category
            ORDER BY revenue DESC
            LIMIT 10
        config:
          x_axis: "product_category"
          y_axis: "revenue"
          title: "产品类别销售排名"
          orientation: "horizontal"
          show_values: true
      
      - name: "regional_distribution"
        type: "map"
        position: [0, 3, 2, 1]
        data:
          query: |
            SELECT 
              customer_region,
              SUM(total_amount) as revenue
            FROM sales_fact
            JOIN customer_dim ON sales_fact.customer_id = customer_dim.customer_id
            WHERE order_date >= DATEADD(month, -1, CURRENT_DATE())
            GROUP BY customer_region
        config:
          map_type: "choropleth"
          region_field: "customer_region"
          value_field: "revenue"
          title: "区域销售分布"
          color_scheme: "blues"
      
      - name: "recent_orders"
        type: "table"
        position: [2, 3, 2, 1]
        data:
          query: |
            SELECT 
              order_id,
              customer_name,
              product_name,
              total_amount,
              order_date
            FROM sales_fact
            JOIN customer_dim ON sales_fact.customer_id = customer_dim.customer_id
            JOIN product_dim ON sales_fact.product_id = product_dim.product_id
            ORDER BY order_date DESC
            LIMIT 10
        config:
          columns:
            - name: "order_id"
              header: "订单ID"
              width: 120
            - name: "customer_name"
              header: "客户名称"
              width: 150
            - name: "product_name"
              header: "产品名称"
              width: 200
            - name: "total_amount"
              header: "金额"
              width: 100
              format: "currency"
            - name: "order_date"
              header: "订单日期"
              width: 120
              format: "date"
          title: "最近订单"
          show_header: true
          pagination: false
    
    interactions:
      - name: "date_filter"
        type: "filter"
        target: "all"
        field: "order_date"
        default: "last_30_days"
      
      - name: "region_filter"
        type: "filter"
        target: ["regional_distribution", "recent_orders"]
        field: "customer_region"
        default: "all"
      
      - name: "product_drill_down"
        type: "drill_down"
        source: "product_performance"
        target: "recent_orders"
        field: "product_category"
    
    refresh:
      type: "automatic"
      interval: "5 minutes"
      conditions:
        - condition: "business_hours"
          time_range: "09:00-18:00"
          interval: "2 minutes"
        - condition: "after_hours"
          time_range: "18:00-09:00"
          interval: "15 minutes"
```

### 2.5 用户权限语法

```yaml
users:
  roles:
    - name: "executive"
      description: "高管角色"
      permissions:
        - resource: "executive_dashboard"
          actions: ["view", "export"]
        - resource: "monthly_sales_report"
          actions: ["view", "export", "schedule"]
        - resource: "all_reports"
          actions: ["view"]
    
    - name: "manager"
      description: "经理角色"
      permissions:
        - resource: "department_dashboard"
          actions: ["view", "export", "filter"]
        - resource: "team_reports"
          actions: ["view", "export", "schedule"]
        - resource: "customer_data"
          actions: ["view"]
          conditions:
            - field: "department"
              operator: "equals"
              value: "${user_department}"
    
    - name: "analyst"
      description: "分析师角色"
      permissions:
        - resource: "all_reports"
          actions: ["view", "export", "create", "edit"]
        - resource: "all_data"
          actions: ["view", "query"]
        - resource: "dashboards"
          actions: ["view", "export", "create", "edit"]
  
  permissions:
    - name: "view_reports"
      description: "查看报表权限"
      resources: ["reports", "dashboards"]
      actions: ["view"]
    
    - name: "export_reports"
      description: "导出报表权限"
      resources: ["reports", "dashboards"]
      actions: ["export"]
      formats: ["pdf", "excel", "csv"]
    
    - name: "create_reports"
      description: "创建报表权限"
      resources: ["reports", "dashboards"]
      actions: ["create", "edit"]
    
    - name: "schedule_reports"
      description: "调度报表权限"
      resources: ["reports"]
      actions: ["schedule"]
      frequency: ["daily", "weekly", "monthly"]
```

### 2.6 调度分发语法

```yaml
scheduling:
  schedules:
    - name: "daily_sales_report"
      description: "每日销售报表"
      report: "daily_sales_report"
      frequency: "daily"
      time: "08:00"
      timezone: "Asia/Shanghai"
      recipients:
        - type: "email"
          addresses: ["sales-team@company.com"]
          subject: "每日销售报表 - {date}"
          body: "请查收今日销售报表"
        - type: "slack"
          channel: "#sales-reports"
          message: "每日销售报表已生成"
      conditions:
        - condition: "business_day"
          skip_weekends: true
          skip_holidays: true
    
    - name: "weekly_executive_summary"
      description: "周度高管总结"
      report: "executive_summary"
      frequency: "weekly"
      day: "monday"
      time: "09:00"
      timezone: "Asia/Shanghai"
      recipients:
        - type: "email"
          addresses: ["executives@company.com"]
          subject: "周度业务总结 - {week_range}"
          body: "请查收本周业务总结报告"
        - type: "file"
          path: "/shared/executive-reports/"
          filename: "executive_summary_{date}.pdf"
    
    - name: "monthly_financial_report"
      description: "月度财务报表"
      report: "financial_report"
      frequency: "monthly"
      day: 1
      time: "10:00"
      timezone: "Asia/Shanghai"
      recipients:
        - type: "email"
          addresses: ["finance@company.com", "audit@company.com"]
          subject: "月度财务报表 - {month_year}"
          body: "请查收月度财务报表"
        - type: "api"
          endpoint: "https://api.company.com/reports"
          method: "POST"
          headers:
            Content-Type: "application/json"
          body: |
            {
              "report_type": "financial",
              "period": "{month_year}",
              "recipients": ["finance", "audit"]
            }
  
  distributions:
    - name: "email_distribution"
      type: "email"
      config:
        smtp_server: "smtp.company.com"
        smtp_port: 587
        username: "${SMTP_USERNAME}"
        password: "${SMTP_PASSWORD}"
        from_address: "reports@company.com"
        reply_to: "support@company.com"
    
    - name: "slack_distribution"
      type: "slack"
      config:
        webhook_url: "${SLACK_WEBHOOK_URL}"
        default_channel: "#reports"
        username: "BI Reports Bot"
        icon_emoji: ":chart_with_upwards_trend:"
    
    - name: "file_distribution"
      type: "file"
      config:
        storage_type: "s3"
        bucket: "company-reports"
        prefix: "distributed/"
        retention_days: 90
```

## 3 高级特性

### 3.1 智能报表生成

```yaml
reports:
  - name: "auto_generated_report"
    type: "auto"
    data_source: "sales_model"
    intelligence:
      enabled: true
      insights:
        - type: "trend_analysis"
          fields: ["total_amount", "order_count"]
          time_granularity: "month"
        - type: "anomaly_detection"
          fields: ["total_amount"]
          sensitivity: 0.95
        - type: "correlation_analysis"
          fields: ["total_amount", "customer_satisfaction"]
      recommendations:
        - type: "chart_selection"
          criteria: ["data_type", "cardinality", "trends"]
        - type: "layout_optimization"
          criteria: ["screen_size", "user_role", "usage_patterns"]
```

### 3.2 动态内容

```yaml
reports:
  - name: "dynamic_content_report"
    type: "dynamic"
    content:
      - name: "conditional_section"
        type: "conditional"
        condition: "user_role = 'executive'"
        content:
          - type: "executive_summary"
            data: "executive_metrics"
        else_content:
          - type: "detailed_analysis"
            data: "detailed_metrics"
      
      - name: "adaptive_chart"
        type: "adaptive"
        data: "sales_data"
        chart_selection:
          - when: "data_points <= 10"
            chart: "bar"
          - when: "data_points > 10 AND data_points <= 50"
            chart: "line"
          - when: "data_points > 50"
            chart: "heatmap"
```

### 3.3 协作功能

```yaml
collaboration:
  - name: "shared_dashboard"
    type: "shared"
    dashboard: "team_dashboard"
    features:
      - name: "comments"
        enabled: true
        permissions: ["view", "add", "edit", "delete"]
      - name: "annotations"
        enabled: true
        types: ["highlight", "arrow", "text", "shape"]
      - name: "sharing"
        enabled: true
        methods: ["link", "email", "embed"]
      - name: "versioning"
        enabled: true
        retention: "30 days"
```

## 4 代码生成模板

### 4.1 Tableau生成模板

```xml
<!-- 生成的Tableau工作簿示例 -->
<workbook source="Tableau">
  <datasources>
    <datasource name="Sales Data" class="snowflake">
      <connection class="snowflake" server="company.snowflakecomputing.com" database="SALES_DB">
        <relation name="sales_fact" table="sales_fact" type="table">
          <column datatype="string" name="order_id"/>
          <column datatype="datetime" name="order_date"/>
          <column datatype="string" name="product_id"/>
          <column datatype="string" name="customer_id"/>
          <column datatype="integer" name="quantity"/>
          <column datatype="real" name="unit_price"/>
          <column datatype="real" name="total_amount"/>
        </relation>
      </connection>
    </datasource>
  </datasources>
  
  <worksheets>
    <worksheet name="Sales Trend">
      <view>
        <column field="order_date" datatype="date" role="dimension"/>
        <column field="total_amount" datatype="real" role="measure" aggregation="sum"/>
        <mark type="line"/>
      </view>
    </worksheet>
    
    <worksheet name="Product Performance">
      <view>
        <column field="product_category" datatype="string" role="dimension"/>
        <column field="total_amount" datatype="real" role="measure" aggregation="sum"/>
        <mark type="bar"/>
      </view>
    </worksheet>
  </worksheets>
  
  <dashboards>
    <dashboard name="Executive Dashboard">
      <layout type="grid" columns="2" rows="2">
        <component type="worksheet" name="Sales Trend" position="0,0,1,1"/>
        <component type="worksheet" name="Product Performance" position="1,0,1,1"/>
        <component type="text" name="Title" position="0,1,2,1" value="Executive Dashboard"/>
      </layout>
    </dashboard>
  </dashboards>
</workbook>
```

### 4.2 Power BI生成模板

```json
// 生成的Power BI模板示例
{
  "name": "Sales Analysis",
  "version": "1.0.0",
  "dataSources": [
    {
      "name": "Sales Database",
      "type": "database",
      "connection": {
        "server": "company.snowflakecomputing.com",
        "database": "SALES_DB",
        "authentication": "oauth"
      },
      "queries": [
        {
          "name": "Sales Data",
          "query": "SELECT * FROM sales_fact",
          "parameters": []
        }
      ]
    }
  ],
  "dataModel": {
    "tables": [
      {
        "name": "Sales",
        "source": "Sales Data",
        "columns": [
          {
            "name": "Order ID",
            "dataType": "string",
            "sourceColumn": "order_id"
          },
          {
            "name": "Order Date",
            "dataType": "date",
            "sourceColumn": "order_date"
          },
          {
            "name": "Total Amount",
            "dataType": "decimal",
            "sourceColumn": "total_amount",
            "format": "currency"
          }
        ],
        "measures": [
          {
            "name": "Total Sales",
            "expression": "SUM(Sales[Total Amount])",
            "format": "currency"
          },
          {
            "name": "Order Count",
            "expression": "COUNTROWS(Sales)",
            "format": "number"
          }
        ]
      }
    ],
    "relationships": [
      {
        "name": "Product Relationship",
        "fromTable": "Sales",
        "fromColumn": "Product ID",
        "toTable": "Product",
        "toColumn": "Product ID"
      }
    ]
  },
  "reports": [
    {
      "name": "Sales Dashboard",
      "pages": [
        {
          "name": "Overview",
          "visuals": [
            {
              "type": "card",
              "title": "Total Sales",
              "measure": "Total Sales",
              "position": {"x": 0, "y": 0, "width": 200, "height": 100}
            },
            {
              "type": "lineChart",
              "title": "Sales Trend",
              "xAxis": "Order Date",
              "yAxis": "Total Sales",
              "position": {"x": 0, "y": 120, "width": 400, "height": 300}
            }
          ]
        }
      ]
    }
  ]
}
```

## 5 验证规则

### 5.1 语法验证

```yaml
validation:
  required_fields:
    - bi_reporting.name
    - bi_reporting.platform
    - bi_reporting.data_sources.connections
    - bi_reporting.reports.reports
  
  type_constraints:
    - field: "bi_reporting.platform"
      allowed_values: ["tableau", "powerbi", "qlik", "looker"]
    - field: "reports.reports[].type"
      allowed_values: ["tabular", "chart", "dashboard", "auto", "dynamic"]
    - field: "users.roles[].permissions[].actions"
      allowed_values: ["view", "export", "create", "edit", "delete", "schedule"]
  
  business_rules:
    - rule: "reports[].data_source must reference existing data source"
    - rule: "dashboards[].components[].data.query must be valid SQL"
    - rule: "users.roles[].permissions[].resource must reference existing resource"
```

### 5.2 性能约束

```yaml
performance:
  max_query_time: "30 seconds"
  max_data_points: 10000
  max_concurrent_users: 100
  cache_ttl: "5 minutes"
  
  optimization:
    query_optimization: true
    caching_enabled: true
    compression_enabled: true
    lazy_loading: true
```

## 6 扩展机制

### 6.1 自定义组件

```yaml
custom_components:
  - name: "custom_chart"
    type: "custom"
    class: "com.company.CustomChartComponent"
    config:
      chart_library: "d3.js"
      data_format: "json"
      responsive: true
  
  - name: "custom_filter"
    type: "custom"
    class: "com.company.CustomFilterComponent"
    config:
      filter_type: "advanced_search"
      auto_complete: true
      suggestions: true
```

### 6.2 插件系统

```yaml
plugins:
  - name: "data_quality"
    version: "1.0.0"
    config:
      enabled: true
      validation_rules: [...]
      alert_threshold: 0.95
  
  - name: "natural_language"
    version: "1.0.0"
    config:
      enabled: true
      language: "zh-CN"
      supported_queries: ["trend", "comparison", "ranking"]
```

## 7 工具链集成

### 7.1 开发工具

- **DSL编辑器**: 语法高亮、自动补全、错误提示
- **报表预览**: 实时预览生成的报表效果
- **配置验证**: 实时验证配置的正确性
- **代码生成**: 一键生成目标平台代码

### 7.2 部署工具

- **容器化部署**: 自动生成Docker镜像和Kubernetes配置
- **配置管理**: 管理不同环境的配置
- **版本管理**: 管理不同版本的报表配置
- **回滚机制**: 支持快速回滚到之前的版本

### 7.3 运维工具

- **监控面板**: 实时监控BI系统状态
- **使用分析**: 分析用户使用情况和报表性能
- **成本分析**: 分析系统运行成本
- **容量规划**: 预测系统容量需求

这个DSL设计为BI报表提供了完整的配置语言，支持从简单的报表到复杂的仪表盘的各种需求，同时保持了良好的可扩展性和可维护性。
