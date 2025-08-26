# 日志查询建模DSL设计

## 设计目标

日志查询建模DSL旨在提供声明式语言定义复杂的日志查询规则，支持多种查询语法、过滤条件、聚合操作、排序分页，并与主流日志查询平台无缝集成。

## 基本语法

### 核心结构

```dsl
log_query "web_service_query" {
  description: "Web服务日志查询"
  version: "1.0.0"
  
  source: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    index: "web-service-logs"
  }
  
  query: {
    filter: "level:ERROR AND service:web-service"
    time_range: {
      from: "now-1h"
      to: "now"
    }
  }
  
  output: {
    format: "json"
    limit: 100
    sort: "timestamp desc"
  }
}
```

### 基本查询

```dsl
basic_query "error_logs_query" {
  description: "错误日志查询"
  
  source: {
    type: "elasticsearch"
    index: "web-service-logs"
    alias: "error_logs"
  }
  
  filter: {
    conditions: [
      "level:ERROR"
      "service:web-service"
      "timestamp:[now-1h TO now]"
    ]
    operator: "AND"
  }
  
  fields: [
    "timestamp"
    "level"
    "message"
    "service"
    "trace_id"
    "user_id"
  ]
  
  sort: [
    {
      field: "timestamp"
      order: "desc"
    }
  ]
  
  pagination: {
    from: 0
    size: 100
    scroll: "5m"
  }
  
  output: {
    format: "json"
    include_metadata: true
    include_score: false
  }
}
```

### 聚合查询

```dsl
aggregation_query "error_statistics" {
  description: "错误统计聚合查询"
  
  source: {
    type: "elasticsearch"
    index: "web-service-logs"
  }
  
  filter: {
    conditions: [
      "level:ERROR"
      "timestamp:[now-24h TO now]"
    ]
    operator: "AND"
  }
  
  aggregations: [
    {
      name: "error_count_by_service"
      type: "terms"
      field: "service.keyword"
      size: 10
      order: {
        field: "_count"
        order: "desc"
      }
    },
    {
      name: "error_count_by_hour"
      type: "date_histogram"
      field: "timestamp"
      interval: "1h"
      format: "yyyy-MM-dd HH:mm:ss"
    },
    {
      name: "error_rate"
      type: "ratio"
      numerator: {
        filter: "level:ERROR"
      }
      denominator: {
        filter: "*"
      }
    }
  ]
  
  output: {
    format: "json"
    include_aggregations: true
    include_hits: false
  }
}
```

### 复杂查询

```dsl
complex_query "user_activity_analysis" {
  description: "用户活动分析查询"
  
  source: {
    type: "elasticsearch"
    index: "web-service-logs"
  }
  
  filter: {
    conditions: [
      "service:web-service"
      "user_id:*"
      "timestamp:[now-7d TO now]"
    ]
    operator: "AND"
  }
  
  query: {
    type: "bool"
    must: [
      {
        type: "match"
        field: "message"
        value: "user action"
        operator: "or"
      }
    ]
    should: [
      {
        type: "wildcard"
        field: "message"
        value: "*login*"
      },
      {
        type: "wildcard"
        field: "message"
        value: "*logout*"
      }
    ]
    must_not: [
      {
        type: "match"
        field: "level"
        value: "DEBUG"
      }
    ]
  }
  
  aggregations: [
    {
      name: "user_actions"
      type: "terms"
      field: "user_id.keyword"
      size: 100
      aggregations: [
        {
          name: "action_count"
          type: "value_count"
          field: "message"
        },
        {
          name: "last_activity"
          type: "max"
          field: "timestamp"
        }
      ]
    },
    {
      name: "action_types"
      type: "terms"
      field: "message.keyword"
      size: 20
    }
  ]
  
  sort: [
    {
      field: "timestamp"
      order: "desc"
    }
  ]
  
  pagination: {
    from: 0
    size: 1000
  }
  
  output: {
    format: "json"
    include_aggregations: true
    include_hits: true
    include_total: true
  }
}
```

### 时间序列查询

```dsl
timeseries_query "performance_metrics" {
  description: "性能指标时间序列查询"
  
  source: {
    type: "elasticsearch"
    index: "web-service-logs"
  }
  
  filter: {
    conditions: [
      "service:web-service"
      "timestamp:[now-24h TO now]"
    ]
    operator: "AND"
  }
  
  aggregations: [
    {
      name: "response_time_stats"
      type: "date_histogram"
      field: "timestamp"
      interval: "5m"
      aggregations: [
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
        }
      ]
    },
    {
      name: "error_rate_timeline"
      type: "date_histogram"
      field: "timestamp"
      interval: "5m"
      aggregations: [
        {
          name: "error_count"
          type: "filter"
          filter: "level:ERROR"
          aggregations: [
            {
              name: "count"
              type: "value_count"
              field: "message"
            }
          ]
        },
        {
          name: "total_count"
          type: "value_count"
          field: "message"
        }
      ]
    }
  ]
  
  output: {
    format: "json"
    include_aggregations: true
    include_hits: false
    time_series: true
  }
}
```

## 高级用法

### 多源查询

```dsl
multi_source_query "distributed_logs_query" {
  description: "分布式日志查询"
  
  sources: [
    {
      name: "web_service_logs"
      type: "elasticsearch"
      endpoint: "http://elasticsearch-1:9200"
      index: "web-service-logs"
      weight: 0.4
    },
    {
      name: "database_logs"
      type: "elasticsearch"
      endpoint: "http://elasticsearch-2:9200"
      index: "database-logs"
      weight: 0.3
    },
    {
      name: "cache_logs"
      type: "elasticsearch"
      endpoint: "http://elasticsearch-3:9200"
      index: "cache-logs"
      weight: 0.3
    }
  ]
  
  global_filter: {
    conditions: [
      "timestamp:[now-1h TO now]"
      "level:ERROR"
    ]
    operator: "AND"
  }
  
  source_specific_filters: {
    web_service_logs: {
      conditions: ["service:web-service"]
    },
    database_logs: {
      conditions: ["service:database-service"]
    },
    cache_logs: {
      conditions: ["service:cache-service"]
    }
  }
  
  correlation: {
    enabled: true
    correlation_key: "trace_id"
    time_window: "5m"
    sources: ["web_service_logs", "database_logs", "cache_logs"]
  }
  
  aggregations: [
    {
      name: "errors_by_service"
      type: "terms"
      field: "service.keyword"
      size: 10
    },
    {
      name: "errors_by_source"
      type: "terms"
      field: "_index"
      size: 5
    }
  ]
  
  output: {
    format: "json"
    merge_strategy: "union"
    deduplication: true
    deduplication_key: "id"
  }
}
```

### 实时流查询

```dsl
stream_query "real_time_monitoring" {
  description: "实时监控查询"
  
  streaming: {
    engine: "kafka_streams"
    mode: "real_time"
    parallelism: 4
  }
  
  sources: [
    {
      name: "log_stream"
      type: "kafka"
      topic: "log-stream"
      consumer_group: "real-time-monitor"
      auto_offset_reset: "latest"
    }
  ]
  
  processing: [
    {
      name: "error_detection"
      type: "stream_processor"
      filter: "level:ERROR"
      window: "5m"
      aggregations: [
        {
          name: "error_count"
          type: "count"
        },
        {
          name: "error_rate"
          type: "rate"
          window: "1m"
        }
      ]
    },
    {
      name: "anomaly_detection"
      type: "stream_processor"
      algorithm: "z_score"
      field: "error_rate"
      threshold: 3.0
      window: "10m"
    },
    {
      name: "alert_generation"
      type: "stream_processor"
      condition: "anomaly_detected == true"
      action: "generate_alert"
      output: "alert-stream"
    }
  ]
  
  output: {
    format: "json"
    destination: "kafka"
    topic: "monitoring-results"
    batch_size: 100
    flush_interval: "5s"
  }
  
  monitoring: {
    metrics: [
      "query_latency",
      "throughput",
      "error_rate",
      "alert_count"
    ]
    alerting: {
      on_high_latency: {
        threshold: "100ms"
        severity: "warning"
      }
      on_high_error_rate: {
        threshold: 0.01
        severity: "critical"
      }
    }
  }
}
```

### 机器学习查询

```dsl
ml_query "anomaly_detection_query" {
  description: "异常检测机器学习查询"
  
  source: {
    type: "elasticsearch"
    index: "web-service-logs"
  }
  
  filter: {
    conditions: [
      "service:web-service"
      "timestamp:[now-7d TO now]"
    ]
    operator: "AND"
  }
  
  ml_analysis: [
    {
      name: "log_pattern_anomaly"
      type: "anomaly_detection"
      algorithm: "isolation_forest"
      features: [
        "message_length"
        "error_frequency"
        "response_time"
        "user_activity"
      ]
      parameters: {
        contamination: 0.1
        n_estimators: 100
      }
    },
    {
      name: "time_series_anomaly"
      type: "anomaly_detection"
      algorithm: "prophet"
      field: "error_rate"
      parameters: {
        changepoint_prior_scale: 0.05
        seasonality_prior_scale: 10.0
      }
    }
  ]
  
  aggregations: [
    {
      name: "anomaly_scores"
      type: "date_histogram"
      field: "timestamp"
      interval: "1h"
      aggregations: [
        {
          name: "avg_anomaly_score"
          type: "avg"
          field: "anomaly_score"
        },
        {
          name: "anomaly_count"
          type: "filter"
          filter: "anomaly_score > 0.8"
          aggregations: [
            {
              name: "count"
              type: "value_count"
              field: "message"
            }
          ]
        }
      ]
    }
  ]
  
  output: {
    format: "json"
    include_ml_results: true
    include_confidence: true
    include_explanations: true
  }
}
```

## 代码生成模板

### Elasticsearch查询

```json
// 生成的Elasticsearch查询
{
  "query": {
    "bool": {
      "must": [
        {
          "match": {
            "level": "ERROR"
          }
        },
        {
          "match": {
            "service": "web-service"
          }
        },
        {
          "range": {
            "@timestamp": {
              "gte": "now-1h",
              "lte": "now"
            }
          }
        }
      ]
    }
  },
  "aggs": {
    "error_count_by_service": {
      "terms": {
        "field": "service.keyword",
        "size": 10,
        "order": {
          "_count": "desc"
        }
      }
    },
    "error_count_by_hour": {
      "date_histogram": {
        "field": "@timestamp",
        "interval": "1h",
        "format": "yyyy-MM-dd HH:mm:ss"
      }
    },
    "error_rate": {
      "filters": {
        "filters": {
          "errors": {
            "term": {
              "level": "ERROR"
            }
          },
          "total": {
            "match_all": {}
          }
        }
      },
      "aggs": {
        "error_ratio": {
          "bucket_script": {
            "buckets_path": {
              "errors": "errors",
              "total": "total"
            },
            "script": "params.errors / params.total"
          }
        }
      }
    }
  },
  "sort": [
    {
      "@timestamp": {
        "order": "desc"
      }
    }
  ],
  "from": 0,
  "size": 100
}
```

### Prometheus查询

```promql
# 生成的Prometheus查询
# 错误率
rate(log_entries_total{level="ERROR", service="web-service"}[5m])

# 响应时间95分位数
histogram_quantile(0.95, rate(http_request_duration_seconds_bucket{service="web-service"}[5m]))

# 请求率
rate(http_requests_total{service="web-service"}[5m])

# 错误率时间序列
rate(log_entries_total{level="ERROR", service="web-service"}[1m])

# 异常检测（基于Z-score）
(
  rate(log_entries_total{level="ERROR", service="web-service"}[5m]) -
  avg_over_time(rate(log_entries_total{level="ERROR", service="web-service"}[5m])[1h])
) / stddev_over_time(rate(log_entries_total{level="ERROR", service="web-service"}[5m])[1h])
```

### SQL查询

```sql
-- 生成的SQL查询
-- 错误日志查询
SELECT 
    timestamp,
    level,
    message,
    service,
    trace_id,
    user_id
FROM web_service_logs
WHERE level = 'ERROR'
    AND service = 'web-service'
    AND timestamp >= NOW() - INTERVAL '1 hour'
ORDER BY timestamp DESC
LIMIT 100;

-- 错误统计聚合查询
SELECT 
    service,
    COUNT(*) as error_count,
    DATE_TRUNC('hour', timestamp) as hour_bucket
FROM web_service_logs
WHERE level = 'ERROR'
    AND timestamp >= NOW() - INTERVAL '24 hours'
GROUP BY service, DATE_TRUNC('hour', timestamp)
ORDER BY error_count DESC;

-- 用户活动分析查询
SELECT 
    user_id,
    COUNT(*) as action_count,
    MAX(timestamp) as last_activity,
    STRING_AGG(DISTINCT message, ', ') as action_types
FROM web_service_logs
WHERE service = 'web-service'
    AND user_id IS NOT NULL
    AND timestamp >= NOW() - INTERVAL '7 days'
    AND message LIKE '%user action%'
    AND level != 'DEBUG'
GROUP BY user_id
ORDER BY action_count DESC
LIMIT 100;

-- 性能指标时间序列查询
SELECT 
    DATE_TRUNC('5 minutes', timestamp) as time_bucket,
    AVG(response_time) as avg_response_time,
    PERCENTILE_CONT(0.95) WITHIN GROUP (ORDER BY response_time) as p95_response_time,
    PERCENTILE_CONT(0.99) WITHIN GROUP (ORDER BY response_time) as p99_response_time,
    COUNT(CASE WHEN level = 'ERROR' THEN 1 END) as error_count,
    COUNT(*) as total_count,
    COUNT(CASE WHEN level = 'ERROR' THEN 1 END)::float / COUNT(*) as error_rate
FROM web_service_logs
WHERE service = 'web-service'
    AND timestamp >= NOW() - INTERVAL '24 hours'
GROUP BY DATE_TRUNC('5 minutes', timestamp)
ORDER BY time_bucket;
```

### Python实现

```python
import requests
import json
from datetime import datetime, timedelta
from typing import Dict, Any, List, Optional

class LogQueryEngine:
    def __init__(self, config):
        self.config = config
        self.session = requests.Session()
        self.session.headers.update({
            'Content-Type': 'application/json'
        })
    
    def execute_query(self, query_config: Dict[str, Any]) -> Dict[str, Any]:
        """执行日志查询"""
        try:
            # 构建查询
            query_body = self._build_query(query_config)
            
            # 执行查询
            response = self._execute_elasticsearch_query(query_body, query_config)
            
            # 处理结果
            result = self._process_response(response, query_config)
            
            return result
            
        except Exception as e:
            return {
                'error': str(e),
                'status': 'error'
            }
    
    def _build_query(self, query_config: Dict[str, Any]) -> Dict[str, Any]:
        """构建Elasticsearch查询"""
        query_body = {
            'query': {
                'bool': {
                    'must': [],
                    'should': [],
                    'must_not': [],
                    'filter': []
                }
            }
        }
        
        # 添加过滤条件
        if 'filter' in query_config:
            for condition in query_config['filter']['conditions']:
                if ':' in condition:
                    field, value = condition.split(':', 1)
                    if value.startswith('[') and value.endswith(']'):
                        # 范围查询
                        range_value = value[1:-1]
                        if ' TO ' in range_value:
                            from_val, to_val = range_value.split(' TO ')
                            query_body['query']['bool']['filter'].append({
                                'range': {
                                    field: {
                                        'gte': from_val,
                                        'lte': to_val
                                    }
                                }
                            })
                    else:
                        # 匹配查询
                        query_body['query']['bool']['must'].append({
                            'match': {
                                field: value
                            }
                        })
        
        # 添加聚合
        if 'aggregations' in query_config:
            query_body['aggs'] = {}
            for agg in query_config['aggregations']:
                query_body['aggs'][agg['name']] = self._build_aggregation(agg)
        
        # 添加排序
        if 'sort' in query_config:
            query_body['sort'] = []
            for sort_config in query_config['sort']:
                query_body['sort'].append({
                    sort_config['field']: {
                        'order': sort_config['order']
                    }
                })
        
        # 添加分页
        if 'pagination' in query_config:
            query_body['from'] = query_config['pagination']['from']
            query_body['size'] = query_config['pagination']['size']
        
        return query_body
    
    def _build_aggregation(self, agg_config: Dict[str, Any]) -> Dict[str, Any]:
        """构建聚合查询"""
        agg = {}
        
        if agg_config['type'] == 'terms':
            agg['terms'] = {
                'field': agg_config['field'],
                'size': agg_config.get('size', 10)
            }
            if 'order' in agg_config:
                agg['terms']['order'] = {
                    agg_config['order']['field']: agg_config['order']['order']
                }
        
        elif agg_config['type'] == 'date_histogram':
            agg['date_histogram'] = {
                'field': agg_config['field'],
                'interval': agg_config['interval']
            }
            if 'format' in agg_config:
                agg['date_histogram']['format'] = agg_config['format']
        
        elif agg_config['type'] == 'avg':
            agg['avg'] = {
                'field': agg_config['field']
            }
        
        elif agg_config['type'] == 'count':
            agg['value_count'] = {
                'field': agg_config['field']
            }
        
        # 添加子聚合
        if 'aggregations' in agg_config:
            agg['aggs'] = {}
            for sub_agg in agg_config['aggregations']:
                agg['aggs'][sub_agg['name']] = self._build_aggregation(sub_agg)
        
        return agg
    
    def _execute_elasticsearch_query(self, query_body: Dict[str, Any], query_config: Dict[str, Any]) -> Dict[str, Any]:
        """执行Elasticsearch查询"""
        url = f"{query_config['source']['endpoint']}/{query_config['source']['index']}/_search"
        
        response = self.session.post(url, json=query_body)
        response.raise_for_status()
        
        return response.json()
    
    def _process_response(self, response: Dict[str, Any], query_config: Dict[str, Any]) -> Dict[str, Any]:
        """处理查询响应"""
        result = {
            'status': 'success',
            'total': response['hits']['total']['value'],
            'took': response['took']
        }
        
        # 处理命中结果
        if query_config['output'].get('include_hits', True):
            result['hits'] = []
            for hit in response['hits']['hits']:
                hit_data = hit['_source']
                if query_config['output'].get('include_metadata', False):
                    hit_data['_id'] = hit['_id']
                    hit_data['_index'] = hit['_index']
                    hit_data['_score'] = hit['_score']
                result['hits'].append(hit_data)
        
        # 处理聚合结果
        if 'aggregations' in response and query_config['output'].get('include_aggregations', False):
            result['aggregations'] = response['aggregations']
        
        return result

# 使用示例
config = {
    "source": {
        "type": "elasticsearch",
        "endpoint": "http://elasticsearch:9200",
        "index": "web-service-logs"
    }
}

query_engine = LogQueryEngine(config)

# 基本查询
basic_query = {
    "description": "错误日志查询",
    "source": {
        "endpoint": "http://elasticsearch:9200",
        "index": "web-service-logs"
    },
    "filter": {
        "conditions": [
            "level:ERROR",
            "service:web-service",
            "timestamp:[now-1h TO now]"
        ]
    },
    "sort": [
        {
            "field": "timestamp",
            "order": "desc"
        }
    ],
    "pagination": {
        "from": 0,
        "size": 100
    },
    "output": {
        "include_hits": True,
        "include_aggregations": False,
        "include_metadata": True
    }
}

result = query_engine.execute_query(basic_query)
print(json.dumps(result, indent=2))
```

## 验证规则

### 语法验证

```dsl
validation_rules "log_query_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "version", "source", "query"]
      message: "必须包含描述、版本、数据源和查询"
    },
    {
      rule: "valid_source_type"
      allowed_types: ["elasticsearch", "prometheus", "loki", "sql"]
      message: "数据源类型必须是支持的类型"
    },
    {
      rule: "valid_query_type"
      allowed_types: ["basic", "aggregation", "complex", "timeseries"]
      message: "查询类型必须是支持的类型"
    }
  ]
  
  semantic: [
    {
      rule: "time_range_validity"
      condition: "query.time_range.from < query.time_range.to"
      message: "时间范围起始时间必须早于结束时间"
    },
    {
      rule: "field_existence"
      condition: "all referenced fields exist in schema"
      message: "所有引用的字段必须在模式中存在"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "query_performance" {
  constraints: [
    {
      metric: "query_execution_time"
      threshold: "30s"
      action: "warn"
    },
    {
      metric: "result_size"
      threshold: "100MB"
      action: "error"
    },
    {
      metric: "memory_usage"
      threshold: "2GB"
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "query_optimization"
      enabled: true
      max_query_time: "10s"
    },
    {
      strategy: "result_limiting"
      enabled: true
      max_results: 10000
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "log_query_patterns" {
  patterns: [
    {
      name: "incremental_query"
      description: "增量查询模式"
      implementation: {
        strategy: "time_based_incremental"
        checkpoint: "last_query_time"
        recovery: "resume_from_checkpoint"
      }
    },
    {
      name: "distributed_query"
      description: "分布式查询模式"
      implementation: {
        strategy: "federated_query"
        load_balancing: true
        result_merging: true
      }
    },
    {
      name: "cached_query"
      description: "缓存查询模式"
      implementation: {
        strategy: "query_caching"
        cache_ttl: "5m"
        cache_key: "query_hash"
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "over_query"
      description: "过度查询"
      symptoms: ["high_resource_usage", "slow_response"]
      solution: "optimize_query"
    },
    {
      name: "under_query"
      description: "查询不足"
      symptoms: ["incomplete_data", "missing_results"]
      solution: "expand_query_scope"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "query_monitoring" {
  metrics: [
    {
      name: "query_execution_time"
      type: "histogram"
      labels: ["query_type", "source", "status"]
      buckets: [0.1, 0.5, 1, 5, 10, 30, 60]
    },
    {
      name: "query_success_rate"
      type: "gauge"
      labels: ["query_type", "source"]
      range: [0, 1]
    },
    {
      name: "query_result_size"
      type: "histogram"
      labels: ["query_type", "source"]
      buckets: [1, 10, 100, 1000, 10000, 100000]
    }
  ]
  
  alerts: [
    {
      name: "query_timeout"
      condition: "query_execution_time > 30"
      severity: "critical"
      action: "cancel_query"
    },
    {
      name: "query_failure"
      condition: "query_success_rate < 0.9"
      severity: "warning"
      action: "investigate_failure"
    }
  ]
}
```

## 主流标准映射

### ELK Stack集成

```dsl
elk_integration "elk_query" {
  elasticsearch: {
    endpoint: "http://elasticsearch:9200"
    index_pattern: "web-service-logs-*"
    query_dsl: true
    aggregations: true
  }
  
  kibana: {
    discover: {
      index_pattern: "web-service-logs-*"
      time_field: "@timestamp"
      default_columns: ["@timestamp", "level", "service", "message"]
    }
    visualize: {
      types: ["line", "bar", "pie", "table"]
      data_sources: ["elasticsearch"]
    }
    dashboard: {
      title: "Log Query Dashboard"
      panels: ["error_rate", "response_time", "user_activity"]
    }
  }
  
  logstash: {
    input: {
      type: "elasticsearch"
      query: "level:ERROR"
      schedule: "*/5 * * * *"
    }
    filter: [
      {
        type: "grok"
        pattern: "%{TIMESTAMP_ISO8601:timestamp} %{LOGLEVEL:level} %{GREEDYDATA:message}"
      }
    ]
    output: {
      type: "elasticsearch"
      index: "query-results"
    }
  }
}
```

### Prometheus集成

```dsl
prometheus_integration "prometheus_query" {
  metrics: [
    {
      name: "log_query_duration_seconds"
      type: "histogram"
      help: "Log query execution time"
      labels: ["query_type", "source", "status"]
    },
    {
      name: "log_query_results_total"
      type: "counter"
      help: "Total number of query results"
      labels: ["query_type", "source"]
    },
    {
      name: "log_query_errors_total"
      type: "counter"
      help: "Total number of query errors"
      labels: ["query_type", "error_type"]
    }
  ]
  
  rules: [
    {
      name: "High Query Error Rate"
      expr: "rate(log_query_errors_total[5m]) > 0.1"
      for: "2m"
      labels: { severity: warning }
      annotations: { summary: "High log query error rate" }
    },
    {
      name: "Slow Query Execution"
      expr: "histogram_quantile(0.95, rate(log_query_duration_seconds_bucket[5m])) > 30"
      for: "1m"
      labels: { severity: critical }
      annotations: { summary: "Slow log query execution" }
    }
  ]
  
  alertmanager: {
    receivers: [
      {
        name: "slack"
        slack_configs: [
          {
            channel: "#alerts"
            title: "Log Query Alert"
            text: "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}"
          }
        ]
      }
    ]
  }
}
```

## 工程实践示例

### 微服务日志查询

```dsl
microservice_query "order_service_query" {
  description: "订单服务日志查询"
  
  services: [
    {
      name: "order-service"
      index: "order-service-logs"
      queries: [
        {
          name: "order_creation_errors"
          filter: "level:ERROR AND message:*order*creation*"
          aggregations: [
            {
              name: "error_count_by_type"
              type: "terms"
              field: "error_type.keyword"
              size: 10
            }
          ]
        },
        {
          name: "order_processing_performance"
          filter: "message:*order*processing*"
          aggregations: [
            {
              name: "avg_processing_time"
              type: "avg"
              field: "processing_time"
            },
            {
              name: "p95_processing_time"
              type: "percentiles"
              field: "processing_time"
              percents: [95]
            }
          ]
        }
      ]
    },
    {
      name: "payment-service"
      index: "payment-service-logs"
      queries: [
        {
          name: "payment_failures"
          filter: "level:ERROR AND message:*payment*failure*"
          aggregations: [
            {
              name: "failure_count_by_reason"
              type: "terms"
              field: "failure_reason.keyword"
              size: 10
            }
          ]
        }
      ]
    },
    {
      name: "inventory-service"
      index: "inventory-service-logs"
      queries: [
        {
          name: "inventory_updates"
          filter: "message:*inventory*update*"
          aggregations: [
            {
              name: "update_count_by_product"
              type: "terms"
              field: "product_id.keyword"
              size: 20
            }
          ]
        }
      ]
    }
  ]
  
  correlation: {
    enabled: true
    correlation_key: "order_id"
    services: ["order-service", "payment-service", "inventory-service"]
    time_window: "5m"
  }
  
  workflow_analysis: [
    {
      name: "order_workflow"
      steps: [
        "order_created",
        "payment_processed",
        "inventory_updated",
        "order_completed"
      ]
      metrics: ["success_rate", "average_duration", "failure_points"]
    }
  ]
  
  alerting: {
    rules: [
      {
        name: "Order Workflow Failure"
        condition: "order_workflow_success_rate < 0.95"
        severity: "critical"
        notification: "pagerduty"
        escalation: {
          levels: ["immediate", "5m", "15m"]
          actions: ["page_oncall", "notify_manager", "create_incident"]
        }
      }
    ]
  }
}
```

### 实时流查询

```dsl
stream_query "real_time_log_analysis" {
  description: "实时日志分析查询"
  
  streaming: {
    engine: "kafka_streams"
    mode: "real_time"
    parallelism: 8
  }
  
  sources: [
    {
      name: "log_stream"
      type: "kafka"
      topic: "log-stream"
      consumer_group: "real-time-analyzer"
      auto_offset_reset: "latest"
      max_poll_records: 1000
    }
  ]
  
  processing: [
    {
      name: "error_detection"
      type: "stream_processor"
      filter: "level:ERROR"
      window: "5m"
      aggregations: [
        {
          name: "error_count"
          type: "count"
        },
        {
          name: "error_rate"
          type: "rate"
          window: "1m"
        },
        {
          name: "error_distribution"
          type: "group_by"
          fields: ["service", "error_type"]
          aggregations: [
            {
              name: "count"
              type: "count"
            }
          ]
        }
      ]
    },
    {
      name: "performance_monitoring"
      type: "stream_processor"
      filter: "response_time:*"
      window: "1m"
      aggregations: [
        {
          name: "avg_response_time"
          type: "avg"
          field: "response_time"
        },
        {
          name: "p95_response_time"
          type: "percentile"
          field: "response_time"
          percentile: 95
        },
        {
          name: "p99_response_time"
          type: "percentile"
          field: "response_time"
          percentile: 99
        }
      ]
    },
    {
      name: "user_activity_tracking"
      type: "stream_processor"
      filter: "user_id:*"
      window: "10m"
      aggregations: [
        {
          name: "active_users"
          type: "cardinality"
          field: "user_id"
        },
        {
          name: "user_actions"
          type: "group_by"
          fields: ["user_id", "action_type"]
          aggregations: [
            {
              name: "action_count"
              type: "count"
            },
            {
              name: "last_activity"
              type: "max"
              field: "timestamp"
            }
          ]
        }
      ]
    },
    {
      name: "anomaly_detection"
      type: "stream_processor"
      algorithm: "z_score"
      fields: ["error_rate", "response_time", "user_activity"]
      threshold: 3.0
      window: "15m"
    },
    {
      name: "alert_generation"
      type: "stream_processor"
      condition: "anomaly_detected == true OR error_rate > 0.05"
      action: "generate_alert"
      severity_mapping: {
        low: { threshold: 2.0, actions: ["notify"] },
        medium: { threshold: 3.0, actions: ["notify", "escalate"] },
        high: { threshold: 5.0, actions: ["notify", "escalate", "page"] }
      }
    }
  ]
  
  outputs: [
    {
      name: "metrics_sink"
      type: "prometheus"
      topic: "metrics-stream"
      endpoint: "http://prometheus:9090"
      batch_size: 100
      flush_interval: "10s"
    },
    {
      name: "alert_sink"
      type: "multiple"
      outputs: [
        {
          type: "kafka"
          topic: "alert-stream"
          endpoint: "kafka:9092"
          acks: "all"
          compression: "snappy"
        },
        {
          type: "slack"
          webhook_url: "https://hooks.slack.com/services/xxx"
          channel: "#alerts"
        },
        {
          type: "pagerduty"
          api_key: "xxx"
          service_id: "xxx"
        }
      ]
    },
    {
      name: "dashboard_sink"
      type: "elasticsearch"
      topic: "dashboard-stream"
      endpoint: "http://elasticsearch:9200"
      index: "real-time-metrics"
      batch_size: 1000
      flush_interval: "30s"
    }
  ]
  
  performance: {
    latency: {
      p95: "100ms"
      p99: "500ms"
    }
    throughput: {
      events_per_second: 50000
      max_lag: "1m"
    }
    scalability: {
      auto_scaling: true
      min_instances: 2
      max_instances: 20
      scale_up_threshold: 0.8
      scale_down_threshold: 0.3
      scale_up_cooldown: "5m"
      scale_down_cooldown: "10m"
    }
  }
  
  monitoring: {
    metrics: [
      "query_latency",
      "throughput",
      "error_rate",
      "alert_count",
      "anomaly_detection_accuracy",
      "memory_usage",
      "cpu_usage"
    ]
    health_checks: [
      "kafka_connectivity",
      "elasticsearch_connectivity",
      "prometheus_connectivity",
      "processing_pipeline_health"
    ]
    alerting: {
      on_high_latency: {
        threshold: "100ms"
        severity: "warning"
      }
      on_high_error_rate: {
        threshold: 0.01
        severity: "critical"
      }
      on_high_memory_usage: {
        threshold: 0.9
        severity: "critical"
      }
      on_pipeline_failure: {
        severity: "critical"
        notification: "pagerduty"
      }
    }
  }
}
```

这个DSL设计提供了完整的日志查询建模能力，支持多种查询语法、过滤条件、聚合操作、排序分页，并能够与主流日志查询平台无缝集成。
