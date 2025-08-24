# 日志查询建模DSL草案

## 1. 设计目标

- 用声明式语法描述日志查询语法、过滤、聚合、排序、权限等流程
- 支持多维度、多条件日志统一查询建模
- 便于自动生成查询与权限配置
- 支持复杂查询、实时分析、权限控制等高级特性

## 2. 基本语法结构

```dsl
log_query "error_analysis" {
  description: "错误日志分析查询"
  version: "1.0.0"
  author: "system"
  
  source: {
    type: "elasticsearch"
    index: "web-service-logs-*"
    endpoint: "http://elasticsearch:9200"
  }
  
  filter: {
    enabled: true
    conditions: [
      {
        field: "level"
        operator: "equals"
        value: "ERROR"
      },
      {
        field: "timestamp"
        operator: "range"
        value: {
          gte: "now-24h"
          lte: "now"
        }
      }
    ]
    logic: "AND"
  }
  
  aggregation: {
    enabled: true
    type: "terms"
    field: "service"
    size: 10
    sub_aggregations: [
      {
        name: "error_count"
        type: "count"
        field: "level"
      },
      {
        name: "avg_response_time"
        type: "avg"
        field: "response_time"
      }
    ]
  }
  
  sorting: {
    enabled: true
    field: "error_count"
    order: "desc"
  }
  
  pagination: {
    enabled: true
    page: 1
    size: 100
    max_size: 1000
  }
  
  output: {
    format: "json"
    include_metadata: true
    include_total: true
  }
  
  caching: {
    enabled: true
    ttl: "5m"
    key: "error_analysis_{timestamp}"
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "query_execution_time",
      "result_count",
      "cache_hit_rate"
    ]
  }
}
```

## 3. 关键元素

- log_query：日志查询声明
- description：描述信息
- version：版本号
- author：作者
- source：数据源配置
- filter：过滤条件
- aggregation：聚合配置
- sorting：排序配置
- pagination：分页配置
- output：输出配置
- caching：缓存配置
- monitoring：监控配置

## 4. 高级用法

### 4.1 复杂查询配置

```dsl
log_query "performance_analysis" {
  description: "性能分析查询"
  version: "1.0.0"
  author: "system"
  
  source: {
    type: "elasticsearch"
    index: "web-service-logs-*"
    endpoint: "http://elasticsearch:9200"
  }
  
  filter: {
    enabled: true
    conditions: [
      {
        field: "level"
        operator: "in"
        value: ["INFO", "WARN", "ERROR"]
      },
      {
        field: "timestamp"
        operator: "range"
        value: {
          gte: "now-7d"
          lte: "now"
        }
      },
      {
        field: "response_time"
        operator: "exists"
        value: true
      }
    ]
    logic: "AND"
    custom_script: {
      enabled: true
      script: "doc['response_time'].value > 1000 && doc['status_code'].value >= 400"
    }
  }
  
  aggregation: {
    enabled: true
    type: "date_histogram"
    field: "timestamp"
    interval: "1h"
    sub_aggregations: [
      {
        name: "avg_response_time"
        type: "avg"
        field: "response_time"
      },
      {
        name: "p95_response_time"
        type: "percentiles"
        field: "response_time"
        percents: [95]
      },
      {
        name: "error_rate"
        type: "bucket_script"
        script: "params.error_count / params.total_count * 100"
        buckets_path: {
          error_count: "error_count",
          total_count: "_count"
        }
      }
    ]
  }
  
  sorting: {
    enabled: true
    field: "timestamp"
    order: "asc"
  }
  
  output: {
    format: "json"
    include_metadata: true
    include_total: true
    fields: [
      "timestamp",
      "service",
      "avg_response_time",
      "p95_response_time",
      "error_rate"
    ]
  }
}
```

### 4.2 实时查询配置

```dsl
log_query "real_time_monitoring" {
  description: "实时监控查询"
  version: "1.0.0"
  author: "system"
  
  source: {
    type: "elasticsearch"
    index: "web-service-logs-*"
    endpoint: "http://elasticsearch:9200"
  }
  
  filter: {
    enabled: true
    conditions: [
      {
        field: "timestamp"
        operator: "range"
        value: {
          gte: "now-5m"
          lte: "now"
        }
      }
    ]
  }
  
  aggregation: {
    enabled: true
    type: "cardinality"
    field: "trace_id"
    sub_aggregations: [
      {
        name: "error_count"
        type: "filter"
        filter: {
          field: "level"
          operator: "equals"
          value: "ERROR"
        }
      }
    ]
  }
  
  streaming: {
    enabled: true
    interval: "30s"
    max_duration: "1h"
    on_update: {
      action: "webhook"
      url: "https://api.example.com/alerts"
      method: "POST"
      headers: {
        "Content-Type": "application/json"
        "Authorization": "Bearer ${API_TOKEN}"
      }
    }
  }
  
  output: {
    format: "json"
    include_metadata: true
  }
}
```

## 5. 代码生成模板

### 5.1 Elasticsearch查询生成

```json
{
  "query": {
    "bool": {
      "must": [
        {
          "term": {
            "level": "ERROR"
          }
        },
        {
          "range": {
            "timestamp": {
              "gte": "now-24h",
              "lte": "now"
            }
          }
        }
      ]
    }
  },
  "aggs": {
    "service_errors": {
      "terms": {
        "field": "service",
        "size": 10
      },
      "aggs": {
        "error_count": {
          "value_count": {
            "field": "level"
          }
        },
        "avg_response_time": {
          "avg": {
            "field": "response_time"
          }
        }
      }
    }
  },
  "sort": [
    {
      "error_count": {
        "order": "desc"
      }
    }
  ],
  "from": 0,
  "size": 100
}
```

### 5.2 Loki查询生成

```logql
{job="web-service"} |= "ERROR" | json | timestamp > now() - 24h
| group_by(service)
| count_over_time(1h)
| sort()
```

### 5.3 SQL查询生成

```sql
SELECT 
  service,
  COUNT(*) as error_count,
  AVG(response_time) as avg_response_time
FROM web_service_logs
WHERE level = 'ERROR'
  AND timestamp >= NOW() - INTERVAL 24 HOUR
GROUP BY service
ORDER BY error_count DESC
LIMIT 100;
```

### 5.4 PromQL查询生成

```promql
# 错误率查询
rate(log_entries_total{level="ERROR"}[5m])

# 响应时间查询
histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - log_query.name
    - log_query.description
    - log_query.version
    - log_query.source
  
  type_constraints:
    - field: "log_query.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "log_query.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "log_query.source.type"
      type: "string"
      enum: ["elasticsearch", "loki", "clickhouse", "prometheus"]
```

### 6.2 查询验证规则

```yaml
query_validation:
  source_consistency:
    - rule: "source type must be supported"
    - rule: "source endpoint must be accessible"
    - rule: "source index must exist"
  
  filter_validation:
    - rule: "filter conditions must be valid"
    - rule: "filter operators must be supported"
    - rule: "filter values must be consistent"
  
  aggregation_validation:
    - rule: "aggregation type must be supported"
    - rule: "aggregation field must exist"
    - rule: "aggregation parameters must be valid"
```

## 7. 最佳实践

### 7.1 查询设计模式

```dsl
# 基础查询模式
log_query "basic_query" {
  description: "基础日志查询"
  version: "1.0.0"
  
  source: {
    type: "elasticsearch"
    index: "logs-*"
  }
  
  filter: {
    enabled: true
    conditions: [
      {
        field: "level"
        operator: "equals"
        value: "ERROR"
      }
    ]
  }
  
  output: {
    format: "json"
  }
}

# 聚合查询模式
log_query "aggregation_query" {
  description: "聚合日志查询"
  version: "1.0.0"
  
  source: {
    type: "elasticsearch"
    index: "logs-*"
  }
  
  aggregation: {
    enabled: true
    type: "terms"
    field: "service"
    sub_aggregations: [
      {
        name: "count"
        type: "count"
      }
    ]
  }
  
  output: {
    format: "json"
  }
}
```

### 7.2 查询命名规范

```dsl
# 推荐命名模式
log_query "service_metric_analysis" {
  # 服务_指标_分析
}

log_query "time_range_performance" {
  # 时间范围_性能
}

log_query "user_behavior_pattern" {
  # 用户_行为_模式
}
```

## 8. 与主流标准的映射

| DSL元素 | Elasticsearch | Loki | ClickHouse | Prometheus |
|---------|---------------|------|------------|------------|
| log_query | query | query | select | query |
| filter | bool | filter | where | label matcher |
| aggregation | aggs | aggregation | group by | aggregation |
| sorting | sort | sort | order by | sort |
| pagination | from/size | limit | limit | limit |

## 9. 工程实践示例

```dsl
# 生产环境日志查询配置示例
log_query "production_error_analysis" {
  description: "生产环境错误分析查询"
  version: "1.0.0"
  author: "system"
  
  source: {
    type: "elasticsearch"
    index: "production-logs-*"
    endpoint: "http://elasticsearch:9200"
    authentication: {
      enabled: true
      type: "service_account"
      service_account: "log-query"
      namespace: "logging"
    }
  }
  
  filter: {
    enabled: true
    conditions: [
      {
        field: "level"
        operator: "in"
        value: ["ERROR", "FATAL"]
      },
      {
        field: "timestamp"
        operator: "range"
        value: {
          gte: "now-1h"
          lte: "now"
        }
      },
      {
        field: "environment"
        operator: "equals"
        value: "production"
      }
    ]
    logic: "AND"
    custom_script: {
      enabled: true
      script: "doc['response_time'].value > 5000 || doc['status_code'].value >= 500"
    }
  }
  
  aggregation: {
    enabled: true
    type: "date_histogram"
    field: "timestamp"
    interval: "5m"
    sub_aggregations: [
      {
        name: "error_count"
        type: "filter"
        filter: {
          field: "level"
          operator: "equals"
          value: "ERROR"
        }
      },
      {
        name: "fatal_count"
        type: "filter"
        filter: {
          field: "level"
          operator: "equals"
          value: "FATAL"
        }
      },
      {
        name: "avg_response_time"
        type: "avg"
        field: "response_time"
      },
      {
        name: "p95_response_time"
        type: "percentiles"
        field: "response_time"
        percents: [95]
      },
      {
        name: "p99_response_time"
        type: "percentiles"
        field: "response_time"
        percents: [99]
      },
      {
        name: "error_rate"
        type: "bucket_script"
        script: "params.error_count / params.total_count * 100"
        buckets_path: {
          error_count: "error_count",
          total_count: "_count"
        }
      },
      {
        name: "service_breakdown"
        type: "terms"
        field: "service"
        size: 10
        sub_aggregations: [
          {
            name: "service_error_count"
            type: "count"
          }
        ]
      }
    ]
  }
  
  sorting: {
    enabled: true
    field: "timestamp"
    order: "asc"
  }
  
  pagination: {
    enabled: true
    page: 1
    size: 1000
    max_size: 10000
  }
  
  output: {
    format: "json"
    include_metadata: true
    include_total: true
    fields: [
      "timestamp",
      "service",
      "error_count",
      "fatal_count",
      "avg_response_time",
      "p95_response_time",
      "p99_response_time",
      "error_rate"
    ]
    compression: {
      enabled: true
      algorithm: "gzip"
      level: 6
    }
  }
  
  caching: {
    enabled: true
    ttl: "2m"
    key: "production_error_analysis_{timestamp}_{hash}"
    strategy: "lru"
    max_size: "100MB"
  }
  
  streaming: {
    enabled: true
    interval: "1m"
    max_duration: "24h"
    on_update: {
      action: "webhook"
      url: "https://api.example.com/alerts"
      method: "POST"
      headers: {
        "Content-Type": "application/json"
        "Authorization": "Bearer ${API_TOKEN}"
      }
      timeout: "30s"
      retry: {
        enabled: true
        max_attempts: 3
        backoff: "exponential"
      }
    }
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "query_execution_time",
      "result_count",
      "cache_hit_rate",
      "error_rate",
      "throughput"
    ]
    alerts: [
      {
        name: "slow_query_execution"
        condition: "query_execution_time > 10s"
        duration: "5m"
        severity: "warning"
      },
      {
        name: "high_error_rate"
        condition: "error_rate > 0.05"
        duration: "2m"
        severity: "critical"
      }
    ]
    dashboards: [
      "https://grafana.example.com/d/log-query"
    ]
  }
  
  security: {
    enabled: true
    authentication: {
      enabled: true
      type: "service_account"
      service_account: "log-query"
      namespace: "logging"
    }
    authorization: {
      enabled: true
      rbac: {
        enabled: true
        service_account: "log-query"
        namespace: "logging"
        cluster_role: "log-query"
      }
    }
    audit: {
      enabled: true
      log_queries: true
      log_results: false
      retention_period: "30d"
    }
  }
  
  performance: {
    timeout: "60s"
    max_memory: "1GB"
    parallel_execution: {
      enabled: true
      workers: 4
      queue_size: 1000
    }
    optimization: {
      enabled: true
      use_cache: true
      preload_common_queries: true
      index_hints: [
        "timestamp",
        "level",
        "service"
      ]
    }
  }
}
```

这个DSL设计为日志查询建模提供了完整的配置语言，支持基础查询、复杂查询、实时查询等多种模式，同时保持了良好的可扩展性和可维护性。
