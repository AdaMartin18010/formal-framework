# 指标建模DSL草案

## 1. 设计目标
- 用统一DSL描述Counter、Gauge、Histogram、Summary等指标要素。
- 支持自动生成Prometheus、OpenTelemetry等指标配置。

## 2. 基本语法结构
```dsl
metric http_requests_total {
  type: counter
  labels: [method, status]
  help: "HTTP请求总数"
}

metric cpu_usage {
  type: gauge
  labels: [host]
  help: "CPU使用率"
}

metric request_latency {
  type: histogram
  labels: [endpoint]
  buckets: [0.1, 0.5, 1, 2, 5]
  help: "请求延迟分布"
}
```

## 3. 关键元素
- metric：指标声明
- type/labels/help/buckets：类型、标签、说明、分桶

## 4. 常用指标声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| metric http_requests_total { ... }            | 计数器指标     |
| type: counter/gauge/histogram/summary         | 指标类型       |
| labels: [method, status]                      | 标签维度       |
| help: "说明"                                  | 指标说明       |
| buckets: [0.1, 0.5, 1]                        | 分桶区间       |

## 5. 与主流标准的映射
- 可自动转换为Prometheus、OpenTelemetry等配置
- 支持与主流监控与可观测性工具集成

## 6. 递归扩展建议
- 支持自定义聚合、动态标签、自动告警
- 支持指标趋势预测与异常检测 