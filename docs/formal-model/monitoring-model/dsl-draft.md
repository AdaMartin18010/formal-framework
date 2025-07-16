# 监控模型DSL草案

## 1. 设计目标

- 用统一DSL描述监控指标、告警规则、日志格式、追踪等要素。
- 支持自动生成Prometheus、Grafana、OpenTelemetry等主流配置。

## 2. 基本语法结构

```dsl
metric http_requests_total {
  type: counter
  labels: [method, status]
  help: "HTTP请求总数"
}

alert HighErrorRate {
  expr: http_requests_total{status="500"} > 10
  for: "5m"
  severity: critical
  notify: ["oncall"]
}

log_format app_log {
  fields: [timestamp, level, message, trace_id]
}

trace service_trace {
  sample_rate: 0.1
  exporter: "otlp"
}
```

## 3. 关键元素

- metric：指标定义
- alert：告警规则
- log_format：日志格式
- trace：追踪配置
- labels/expr/for/severity/notify：常用监控与告警字段

## 4. 示例

```dsl
metric cpu_usage {
  type: gauge
  labels: [host]
  help: "CPU使用率"
}

alert CPULoadHigh {
  expr: cpu_usage > 0.9
  for: "2m"
  severity: warning
  notify: ["devops"]
}

log_format nginx_log {
  fields: [remote_addr, request, status, bytes_sent]
}

trace api_trace {
  sample_rate: 1.0
  exporter: "jaeger"
}
```

## 5. 与主流标准的映射

- 可自动转换为Prometheus规则、Alertmanager、Grafana仪表盘、OpenTelemetry配置等
- 支持与ELK/EFK日志采集集成

## 6. 递归扩展建议

- 支持多维指标聚合、动态告警
- 支持日志采集、过滤、脱敏
- 支持分布式追踪与调用链分析
