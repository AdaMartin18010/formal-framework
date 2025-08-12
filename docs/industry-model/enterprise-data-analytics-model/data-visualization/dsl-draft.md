# 数据可视化DSL设计草案

## 1 DSL概述

数据可视化DSL（Domain Specific Language）旨在提供一种声明式、类型安全的方式来描述数据可视化配置，支持跨平台的可视化代码生成和自动化管理。

## 2 核心语法设计

### 2.1 基础语法结构

```yaml
visualization:
  name: "销售数据分析"
  version: "1.0.0"
  data:
    source: "sales_data"
    schema: "sales_schema"
  chart:
    type: "bar"
    config: {...}
  interaction:
    events: [...]
  layout:
    responsive: true
  theme:
    name: "corporate"
```

### 2.2 数据定义语法

```yaml
data:
  source:
    type: "database" | "file" | "api"
    connection: {...}
    query: "SELECT * FROM sales WHERE date >= '2024-01-01'"
  
  schema:
    fields:
      - name: "date"
        type: "date"
        format: "YYYY-MM-DD"
      - name: "amount"
        type: "number"
        unit: "CNY"
      - name: "category"
        type: "string"
        enum: ["电子产品", "服装", "食品"]
  
  transform:
    - type: "filter"
      condition: "amount > 1000"
    - type: "aggregate"
      group_by: ["category"]
      measures: ["amount"]
```

### 2.3 图表配置语法

```yaml
chart:
  type: "bar" | "line" | "scatter" | "pie" | "heatmap"
  
  # 柱状图配置
  bar:
    x_axis:
      field: "category"
      title: "产品类别"
      rotation: 45
    y_axis:
      field: "amount"
      title: "销售额"
      format: "currency"
    color:
      field: "category"
      palette: "category10"
    tooltip:
      enabled: true
      template: "类别: {category}<br>销售额: {amount}"
  
  # 折线图配置
  line:
    x_axis:
      field: "date"
      type: "time"
    y_axis:
      field: "amount"
    series:
      - field: "amount"
        name: "销售额"
        color: "#1890ff"
    markers:
      enabled: true
      size: 4
```

### 2.4 交互配置语法

```yaml
interaction:
  events:
    - type: "click"
      target: "bar"
      action:
        type: "filter"
        field: "category"
        value: "{clicked_value}"
    
    - type: "hover"
      target: "all"
      action:
        type: "highlight"
        duration: 200
    
    - type: "zoom"
      target: "chart"
      action:
        type: "scale"
        axis: "both"
  
  state:
    history: true
    max_steps: 10
    undo_redo: true
```

### 2.5 布局配置语法

```yaml
layout:
  type: "grid" | "flex" | "absolute"
  
  grid:
    rows: 2
    columns: 2
    gap: 16
  
  responsive:
    breakpoints:
      - name: "mobile"
        max_width: 768
        layout: "stack"
      - name: "tablet"
        max_width: 1024
        layout: "grid"
        columns: 1
      - name: "desktop"
        min_width: 1025
        layout: "grid"
        columns: 2
  
  positioning:
    alignment: "center"
    padding: 16
    margin: 8
```

### 2.6 主题配置语法

```yaml
theme:
  name: "corporate" | "dark" | "light" | "custom"
  
  colors:
    primary: "#1890ff"
    secondary: "#52c41a"
    accent: "#faad14"
    background: "#ffffff"
    text: "#262626"
    border: "#d9d9d9"
  
  typography:
    font_family: "PingFang SC, -apple-system, BlinkMacSystemFont"
    font_size: 14
    line_height: 1.5
    heading:
      font_weight: 600
      font_size: 16
  
  spacing:
    unit: 8
    padding: 16
    margin: 8
    gap: 12
```

## 3 高级特性

### 3.1 条件渲染

```yaml
chart:
  type: "conditional"
  conditions:
    - when: "data.length > 1000"
      chart: "heatmap"
    - when: "data.length <= 1000 && data.length > 100"
      chart: "bar"
    - when: "data.length <= 100"
      chart: "table"
```

### 3.2 动态配置

```yaml
chart:
  type: "bar"
  config:
    color:
      field: "category"
      palette: "dynamic"
      algorithm: "hash"
    
    size:
      field: "amount"
      scale: "linear"
      range: [10, 50]
    
    opacity:
      field: "profit_margin"
      scale: "linear"
      range: [0.3, 1.0]
```

### 3.3 组合图表

```yaml
chart:
  type: "composite"
  components:
    - type: "bar"
      position: "left"
      config: {...}
    - type: "line"
      position: "right"
      config: {...}
  
  shared:
    x_axis: true
    tooltip: true
```

## 4 代码生成模板

### 4.1 D3.js生成模板

```javascript
// 生成的D3.js代码示例
const visualization = {
  data: async () => {
    const response = await fetch('/api/sales-data');
    return response.json();
  },
  
  render: (container, data) => {
    const margin = {top: 20, right: 20, bottom: 30, left: 40};
    const width = 960 - margin.left - margin.right;
    const height = 500 - margin.top - margin.bottom;
    
    const svg = d3.select(container)
      .append("svg")
      .attr("width", width + margin.right + margin.left)
      .attr("height", height + margin.top + margin.bottom)
      .append("g")
      .attr("transform", `translate(${margin.left},${margin.top})`);
    
    const x = d3.scaleBand()
      .range([0, width])
      .padding(0.1);
    
    const y = d3.scaleLinear()
      .range([height, 0]);
    
    x.domain(data.map(d => d.category));
    y.domain([0, d3.max(data, d => d.amount)]);
    
    svg.selectAll(".bar")
      .data(data)
      .enter().append("rect")
      .attr("class", "bar")
      .attr("x", d => x(d.category))
      .attr("width", x.bandwidth())
      .attr("y", d => y(d.amount))
      .attr("height", d => height - y(d.amount))
      .attr("fill", "#1890ff");
  }
};
```

### 4.2 React组件生成模板

```jsx
// 生成的React组件示例
import React, { useEffect, useRef } from 'react';
import * as d3 from 'd3';

const SalesChart = ({ data, config }) => {
  const svgRef = useRef();
  
  useEffect(() => {
    if (!data || !svgRef.current) return;
    
    const svg = d3.select(svgRef.current);
    svg.selectAll("*").remove();
    
    const margin = {top: 20, right: 20, bottom: 30, left: 40};
    const width = 960 - margin.left - margin.right;
    const height = 500 - margin.top - margin.bottom;
    
    const g = svg.append("g")
      .attr("transform", `translate(${margin.left},${margin.top})`);
    
    // 渲染逻辑...
  }, [data, config]);
  
  return (
    <div className="chart-container">
      <svg ref={svgRef} width="960" height="500"></svg>
    </div>
  );
};

export default SalesChart;
```

## 5 验证规则

### 5.1 语法验证

```yaml
validation:
  required_fields:
    - visualization.name
    - visualization.data.source
    - visualization.chart.type
  
  type_constraints:
    - field: "chart.type"
      allowed_values: ["bar", "line", "scatter", "pie", "heatmap"]
    - field: "data.schema.fields[].type"
      allowed_values: ["string", "number", "date", "boolean"]
  
  business_rules:
    - rule: "chart.bar.x_axis.field must exist in data.schema.fields"
    - rule: "chart.bar.y_axis.field must be numeric"
    - rule: "interaction.events[].target must be valid chart element"
```

### 5.2 性能约束

```yaml
performance:
  max_data_points: 10000
  max_chart_elements: 1000
  render_timeout: 5000
  memory_limit: "100MB"
  
  optimization:
    virtual_scrolling: true
    lazy_loading: true
    data_sampling: true
```

## 6 扩展机制

### 6.1 自定义图表类型

```yaml
custom_charts:
  sankey:
    type: "custom"
    library: "d3-sankey"
    config:
      nodes: {...}
      links: {...}
  
  treemap:
    type: "custom"
    library: "d3-treemap"
    config:
      hierarchy: {...}
      size: {...}
```

### 6.2 插件系统

```yaml
plugins:
  - name: "export"
    version: "1.0.0"
    config:
      formats: ["png", "svg", "pdf"]
  
  - name: "animation"
    version: "1.0.0"
    config:
      duration: 1000
      easing: "ease-in-out"
```

## 7 工具链集成

### 7.1 开发工具

- **DSL编辑器**: 语法高亮、自动补全、错误提示
- **可视化预览**: 实时预览生成的图表效果
- **配置验证**: 实时验证配置的正确性
- **代码生成**: 一键生成目标平台代码

### 7.2 构建工具

- **编译检查**: 编译时检查配置和依赖
- **代码优化**: 自动优化生成的代码
- **打包部署**: 自动打包和部署可视化应用

### 7.3 监控工具

- **性能监控**: 监控图表渲染性能
- **错误追踪**: 追踪和报告渲染错误
- **使用统计**: 统计图表使用情况

这个DSL设计为数据可视化提供了完整的配置语言，支持从简单的图表到复杂的交互式可视化的各种需求，同时保持了良好的可扩展性和可维护性。
