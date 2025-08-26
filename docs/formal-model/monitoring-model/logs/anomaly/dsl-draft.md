# 日志异常检测建模DSL设计

## 设计目标

日志异常检测建模DSL旨在提供声明式语言定义复杂的日志异常检测规则和算法，支持多种异常类型检测、自适应阈值调整、机器学习模型集成。

## 基本语法

### 核心结构

```dsl
anomaly_detection "web_service_anomaly" {
  description: "Web服务日志异常检测"
  version: "1.0.0"
  
  source: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    index: "web-service-logs"
    query: "service:web-service"
    time_window: "5m"
  }
  
  detection_rules: [
    {
      name: "error_spike_detection"
      type: "frequency_anomaly"
      algorithm: "z_score"
      threshold: 3.0
      window: "1h"
    }
  ]
  
  alerting: {
    severity: "critical"
    channels: ["slack", "email", "pagerduty"]
  }
}
```

### 频率异常检测

```dsl
frequency_anomaly "error_rate_anomaly" {
  description: "错误率异常检测"
  
  metric: {
    name: "error_count"
    aggregation: "count"
    filter: "level:ERROR"
    group_by: ["service", "endpoint"]
  }
  
  algorithm: {
    type: "z_score"
    parameters: {
      window_size: "1h"
      baseline_period: "7d"
      threshold: 3.0
    }
  }
  
  baseline: {
    calculation: "rolling_mean"
    window: "24h"
    min_data_points: 100
  }
  
  detection: {
    sensitivity: "medium"
    min_anomaly_duration: "2m"
    max_anomaly_duration: "1h"
  }
  
  alerting: {
    severity: "warning"
    message: "错误率异常：{service} 服务在 {endpoint} 端点的错误率异常升高"
  }
}
```

### 模式异常检测

```dsl
pattern_anomaly "log_pattern_anomaly" {
  description: "日志模式异常检测"
  
  algorithm: {
    type: "isolation_forest"
    parameters: {
      contamination: 0.1
      n_estimators: 100
      max_samples: "auto"
    }
  }
  
  features: [
    {
      name: "message_length"
      type: "numeric"
      normalization: "standard"
    },
    {
      name: "error_type"
      type: "categorical"
      encoding: "one_hot"
    },
    {
      name: "service_name"
      type: "categorical"
      encoding: "label"
    }
  ]
  
  training: {
    data_source: "historical_logs"
    period: "30d"
    update_frequency: "1d"
    validation_split: 0.2
  }
  
  detection: {
    confidence_threshold: 0.8
    min_anomaly_score: 0.7
    batch_size: 1000
  }
}
```

### 时间序列异常检测

```dsl
timeseries_anomaly "response_time_anomaly" {
  description: "响应时间时间序列异常检测"
  
  metric: {
    name: "response_time"
    aggregation: "percentile"
    percentile: 95
    unit: "ms"
  }
  
  algorithm: {
    type: "prophet"
    parameters: {
      changepoint_prior_scale: 0.05
      seasonality_prior_scale: 10.0
      holidays_prior_scale: 10.0
      seasonality_mode: "multiplicative"
    }
  }
  
  seasonality: {
    yearly: true
    weekly: true
    daily: true
    custom_seasonalities: [
      {
        name: "hourly"
        period: 24
        fourier_order: 5
      }
    ]
  }
  
  forecasting: {
    horizon: "1h"
    confidence_interval: 0.95
    update_frequency: "5m"
  }
  
  detection: {
    method: "confidence_interval"
    threshold: 2.0
    min_anomaly_duration: "5m"
  }
}
```

## 高级用法

### 复合异常检测

```dsl
composite_anomaly "comprehensive_anomaly_detection" {
  description: "综合异常检测"
  
  detectors: [
    {
      name: "error_rate_detector"
      type: "frequency_anomaly"
      weight: 0.4
    },
    {
      name: "response_time_detector"
      type: "timeseries_anomaly"
      weight: 0.3
    },
    {
      name: "pattern_detector"
      type: "pattern_anomaly"
      weight: 0.3
    }
  ]
  
  aggregation: {
    method: "weighted_average"
    threshold: 0.6
    consensus_required: 2
  }
  
  alerting: {
    severity_mapping: {
      low: { score: [0.6, 0.8], actions: ["notify"] },
      medium: { score: [0.8, 0.9], actions: ["notify", "escalate"] },
      high: { score: [0.9, 1.0], actions: ["notify", "escalate", "page"] }
    }
  }
}
```

### 自适应阈值

```dsl
adaptive_threshold "dynamic_threshold" {
  description: "动态阈值调整"
  
  learning: {
    algorithm: "exponential_smoothing"
    alpha: 0.1
    beta: 0.05
    gamma: 0.01
  }
  
  baseline: {
    calculation: "adaptive_mean"
    window: "24h"
    seasonality: "daily"
    trend_adjustment: true
  }
  
  adjustment: {
    sensitivity: "adaptive"
    min_threshold: 2.0
    max_threshold: 5.0
    adjustment_rate: 0.1
  }
  
  feedback: {
    false_positive_penalty: 0.1
    false_negative_penalty: 0.3
    learning_rate: 0.05
  }
}
```

### 机器学习集成

```dsl
ml_anomaly "ml_based_anomaly" {
  description: "机器学习异常检测"
  
  model: {
    type: "autoencoder"
    architecture: {
      encoder: [64, 32, 16]
      decoder: [16, 32, 64]
      activation: "relu"
      dropout: 0.2
    }
  }
  
  training: {
    data_source: "normal_logs"
    period: "30d"
    batch_size: 32
    epochs: 100
    validation_split: 0.2
    early_stopping: true
  }
  
  features: [
    {
      name: "log_volume"
      type: "numeric"
      window: "5m"
      aggregation: "count"
    },
    {
      name: "error_distribution"
      type: "categorical"
      encoding: "frequency"
    },
    {
      name: "temporal_features"
      type: "temporal"
      include: ["hour", "day_of_week", "is_weekend"]
    }
  ]
  
  detection: {
    method: "reconstruction_error"
    threshold: "adaptive"
    min_error_threshold: 0.1
  }
  
  online_learning: {
    enabled: true
    update_frequency: "1h"
    batch_size: 100
    learning_rate: 0.001
  }
}
```

## 代码生成模板

### Python实现

```python
import pandas as pd
import numpy as np
from sklearn.ensemble import IsolationForest
from sklearn.preprocessing import StandardScaler
import elasticsearch

class LogAnomalyDetector:
    def __init__(self, config):
        self.config = config
        self.es_client = elasticsearch.Elasticsearch(config['source']['endpoint'])
    
    def collect_logs(self):
        query = {
            "query": {
                "bool": {
                    "must": [{"match": {"service": "web-service"}}],
                    "filter": {
                        "range": {
                            "@timestamp": {
                                "gte": f"now-{self.config['source']['time_window']}",
                                "lte": "now"
                            }
                        }
                    }
                }
            },
            "aggs": {
                "error_count": {
                    "date_histogram": {
                        "field": "@timestamp",
                        "interval": "1m"
                    },
                    "aggs": {
                        "error_count": {
                            "filter": {"term": {"level": "ERROR"}}
                        }
                    }
                }
            }
        }
        
        response = self.es_client.search(
            index=self.config['source']['index'],
            body=query,
            size=0
        )
        
        return response['aggregations']['error_count']['buckets']
    
    def frequency_anomaly_detection(self, data):
        error_counts = [bucket['error_count']['doc_count'] for bucket in data]
        
        if len(error_counts) < 10:
            return []
        
        # 计算Z-score
        mean = np.mean(error_counts)
        std = np.std(error_counts)
        
        if std == 0:
            return []
        
        z_scores = [(count - mean) / std for count in error_counts]
        
        # 检测异常
        anomalies = []
        threshold = self.config['detection_rules'][0]['threshold']
        
        for i, z_score in enumerate(z_scores):
            if abs(z_score) > threshold:
                anomalies.append({
                    'timestamp': data[i]['key_as_string'],
                    'value': error_counts[i],
                    'z_score': z_score,
                    'severity': 'high' if abs(z_score) > threshold * 1.5 else 'medium'
                })
        
        return anomalies
    
    def pattern_anomaly_detection(self, data):
        # 特征提取
        features = []
        for bucket in data:
            feature_vector = [
                bucket['error_count']['doc_count'],
                len(bucket.get('key_as_string', '')),
                hash(bucket.get('key_as_string', '')) % 1000
            ]
            features.append(feature_vector)
        
        if len(features) < 10:
            return []
        
        # 标准化
        scaler = StandardScaler()
        features_scaled = scaler.fit_transform(features)
        
        # 异常检测
        model = IsolationForest(
            contamination=0.1,
            n_estimators=100,
            random_state=42
        )
        
        anomaly_scores = model.fit_predict(features_scaled)
        
        anomalies = []
        for i, score in enumerate(anomaly_scores):
            if score == -1:
                anomalies.append({
                    'timestamp': data[i]['key_as_string'],
                    'anomaly_score': model.decision_function([features_scaled[i]])[0],
                    'severity': 'high'
                })
        
        return anomalies
    
    def run_detection(self):
        logs = self.collect_logs()
        all_anomalies = []
        
        for rule in self.config['detection_rules']:
            if rule['type'] == 'frequency_anomaly':
                anomalies = self.frequency_anomaly_detection(logs)
            elif rule['type'] == 'pattern_anomaly':
                anomalies = self.pattern_anomaly_detection(logs)
            else:
                continue
            
            all_anomalies.extend(anomalies)
        
        # 发送告警
        if all_anomalies:
            self.send_alerts(all_anomalies)
        
        return all_anomalies
    
    def send_alerts(self, anomalies):
        for anomaly in anomalies:
            alert = {
                'severity': anomaly.get('severity', 'medium'),
                'message': f"检测到日志异常：{anomaly}",
                'timestamp': anomaly.get('timestamp', datetime.now().isoformat()),
                'channels': self.config['alerting']['channels']
            }
            
            # 发送到各个告警渠道
            for channel in alert['channels']:
                if channel == 'slack':
                    self.send_slack_alert(alert)
                elif channel == 'email':
                    self.send_email_alert(alert)
                elif channel == 'pagerduty':
                    self.send_pagerduty_alert(alert)

# 使用示例
config = {
    "source": {
        "type": "elasticsearch",
        "endpoint": "http://elasticsearch:9200",
        "index": "web-service-logs",
        "time_window": "5m"
    },
    "detection_rules": [
        {
            "name": "error_spike_detection",
            "type": "frequency_anomaly",
            "algorithm": "z_score",
            "threshold": 3.0,
            "window": "1h"
        }
    ],
    "alerting": {
        "severity": "critical",
        "channels": ["slack", "email", "pagerduty"]
    }
}

detector = LogAnomalyDetector(config)
anomalies = detector.run_detection()
```

### Prometheus告警规则

```yaml
# 生成的Prometheus告警规则
groups:
  - name: log_anomaly_detection
    rules:
      - alert: HighErrorRate
        expr: |
          (
            rate(log_entries_total{level="ERROR", service="web-service"}[5m]) -
            avg_over_time(rate(log_entries_total{level="ERROR", service="web-service"}[5m])[1h])
          ) / stddev_over_time(rate(log_entries_total{level="ERROR", service="web-service"}[5m])[1h]) > 3
        for: 2m
        labels:
          severity: warning
          service: web-service
        annotations:
          summary: "High error rate anomaly detected"
          description: "Error rate for {{ $labels.service }} is {{ $value }} standard deviations above normal"
      
      - alert: ResponseTimeAnomaly
        expr: |
          histogram_quantile(0.95, rate(http_request_duration_seconds_bucket{service="web-service"}[5m])) >
          avg_over_time(histogram_quantile(0.95, rate(http_request_duration_seconds_bucket{service="web-service"}[5m]))[1h]) * 2
        for: 5m
        labels:
          severity: critical
          service: web-service
        annotations:
          summary: "Response time anomaly detected"
          description: "95th percentile response time for {{ $labels.service }} is {{ $value }}s"
      
      - alert: LogVolumeAnomaly
        expr: |
          rate(log_entries_total{service="web-service"}[5m]) >
          avg_over_time(rate(log_entries_total{service="web-service"}[5m])[1h]) * 3
        for: 1m
        labels:
          severity: warning
          service: web-service
        annotations:
          summary: "Log volume anomaly detected"
          description: "Log volume for {{ $labels.service }} is {{ $value }} logs/sec"
```

### Elasticsearch查询

```json
// 生成的Elasticsearch异常检测查询
{
  "query": {
    "bool": {
      "must": [
        {"match": {"service": "web-service"}},
        {"range": {"@timestamp": {"gte": "now-1h", "lte": "now"}}}
      ]
    }
  },
  "aggs": {
    "error_rate_anomaly": {
      "date_histogram": {
        "field": "@timestamp",
        "interval": "1m"
      },
      "aggs": {
        "error_count": {
          "filter": {"term": {"level": "ERROR"}}
        },
        "total_count": {
          "value_count": {"field": "level"}
        },
        "error_rate": {
          "bucket_script": {
            "buckets_path": {
              "errors": "error_count",
              "total": "total_count"
            },
            "script": "params.errors / params.total"
          }
        },
        "z_score": {
          "bucket_script": {
            "buckets_path": {
              "current": "error_rate"
            },
            "script": "(params.current - 0.05) / 0.02"
          }
        }
      }
    },
    "response_time_anomaly": {
      "date_histogram": {
        "field": "@timestamp",
        "interval": "1m"
      },
      "aggs": {
        "response_time_p95": {
          "percentiles": {
            "field": "response_time",
            "percents": [95]
          }
        }
      }
    }
  }
}
```

## 验证规则

### 语法验证

```dsl
validation_rules "anomaly_detection_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["description", "version", "source", "detection_rules"]
      message: "必须包含描述、版本、数据源和检测规则"
    },
    {
      rule: "valid_algorithm"
      allowed_algorithms: ["z_score", "isolation_forest", "prophet", "autoencoder"]
      message: "算法类型必须是支持的类型"
    },
    {
      rule: "valid_threshold"
      condition: "threshold > 0"
      message: "阈值必须大于0"
    }
  ]
  
  semantic: [
    {
      rule: "time_window_validity"
      condition: "source.time_window > 0"
      message: "时间窗口必须大于0"
    },
    {
      rule: "threshold_range"
      condition: "threshold >= 1.0 AND threshold <= 10.0"
      message: "阈值应在1.0到10.0之间"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "anomaly_detection_performance" {
  constraints: [
    {
      metric: "detection_latency"
      threshold: "30s"
      action: "warn"
    },
    {
      metric: "false_positive_rate"
      threshold: 0.1
      action: "error"
    },
    {
      metric: "false_negative_rate"
      threshold: 0.05
      action: "error"
    }
  ]
  
  optimization: [
    {
      strategy: "model_optimization"
      enabled: true
      target_accuracy: 0.95
    },
    {
      strategy: "feature_selection"
      enabled: true
      max_features: 50
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "anomaly_detection_patterns" {
  patterns: [
    {
      name: "ensemble_detection"
      description: "集成检测模式"
      implementation: {
        strategy: "multiple_algorithms"
        aggregation: "voting"
        consensus_threshold: 0.6
      }
    },
    {
      name: "adaptive_detection"
      description: "自适应检测模式"
      implementation: {
        strategy: "online_learning"
        update_frequency: "1h"
        feedback_loop: true
      }
    },
    {
      name: "hierarchical_detection"
      description: "分层检测模式"
      implementation: {
        strategy: "coarse_to_fine"
        levels: ["service", "endpoint", "method"]
        cascade: true
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "over_detection"
      description: "过度检测"
      symptoms: ["high_false_positive_rate", "alert_fatigue"]
      solution: "adjust_thresholds"
    },
    {
      name: "under_detection"
      description: "检测不足"
      symptoms: ["high_false_negative_rate", "missed_incidents"]
      solution: "lower_thresholds"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "anomaly_detection_monitoring" {
  metrics: [
    {
      name: "anomaly_detection_accuracy"
      type: "gauge"
      labels: ["algorithm", "service"]
      range: [0, 1]
    },
    {
      name: "anomaly_detection_latency"
      type: "histogram"
      labels: ["algorithm", "service"]
      buckets: [0.1, 0.5, 1, 5, 10, 30]
    },
    {
      name: "anomaly_count"
      type: "counter"
      labels: ["severity", "service", "algorithm"]
    }
  ]
  
  alerts: [
    {
      name: "detection_accuracy_degraded"
      condition: "anomaly_detection_accuracy < 0.9"
      severity: "warning"
      action: "retrain_model"
    },
    {
      name: "detection_latency_high"
      condition: "anomaly_detection_latency > 30"
      severity: "critical"
      action: "optimize_algorithm"
    }
  ]
}
```

## 主流标准映射

### Prometheus集成

```dsl
prometheus_integration "prometheus_anomaly" {
  metrics: [
    {
      name: "log_anomaly_detection_duration_seconds"
      type: "histogram"
      help: "Log anomaly detection execution time"
      labels: ["algorithm", "service", "status"]
    },
    {
      name: "log_anomaly_detection_accuracy"
      type: "gauge"
      help: "Anomaly detection accuracy"
      labels: ["algorithm", "service"]
    },
    {
      name: "log_anomaly_detection_results_total"
      type: "counter"
      help: "Total number of anomaly detection results"
      labels: ["algorithm", "service", "result_type"]
    }
  ]
  
  rules: [
    {
      name: "high_error_rate_anomaly"
      expr: "rate(log_entries_total{level=\"ERROR\"}[5m]) > 0.1"
      for: "2m"
      labels: { severity: warning }
      annotations: { summary: "High error rate anomaly detected" }
    },
    {
      name: "response_time_anomaly"
      expr: "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 1"
      for: "5m"
      labels: { severity: critical }
      annotations: { summary: "Response time anomaly detected" }
    }
  ]
  
  alertmanager: {
    receivers: [
      {
        name: "slack"
        slack_configs: [
          {
            channel: "#alerts"
            title: "Log Anomaly Alert"
            text: "{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}"
          }
        ]
      }
    ]
  }
}
```

### ELK Stack集成

```dsl
elk_integration "elk_anomaly" {
  elasticsearch: {
    index_pattern: "logstash-*"
    anomaly_detection: {
      enabled: true
      algorithms: ["isolation_forest", "dbscan"]
    }
  }
  
  logstash: {
    input: {
      type: "elasticsearch"
      query: "service:web-service"
    }
    filter: [
      {
        type: "grok"
        pattern: "%{TIMESTAMP_ISO8601:timestamp} %{LOGLEVEL:level} %{GREEDYDATA:message}"
      },
      {
        type: "anomaly_detection"
        algorithm: "isolation_forest"
        features: ["message_length", "error_count"]
        threshold: 0.8
      }
    ]
    output: {
      type: "elasticsearch"
      index: "anomaly-results"
    }
  }
  
  kibana: {
    visualization: {
      type: "line"
      index_pattern: "anomaly-results"
      time_field: "@timestamp"
    }
    dashboard: {
      title: "Anomaly Detection Dashboard"
      panels: ["error_rate_anomaly", "response_time_anomaly", "pattern_anomaly"]
    }
    alerting: {
      rules: [
        {
          name: "High Anomaly Score"
          condition: "anomaly_score > 0.8"
          actions: ["slack", "email"]
        }
      ]
    }
  }
}
```

### Grafana集成

```dsl
grafana_integration "grafana_anomaly" {
  datasources: [
    {
      name: "elasticsearch"
      type: "elasticsearch"
      url: "http://elasticsearch:9200"
    },
    {
      name: "prometheus"
      type: "prometheus"
      url: "http://prometheus:9090"
    }
  ]
  
  dashboards: [
    {
      title: "Anomaly Detection Overview"
      panels: [
        {
          title: "Anomaly Detection Results"
          type: "graph"
          datasource: "elasticsearch"
          query: {
            index: "anomaly-results"
            query: "anomaly_score:*"
            aggregation: "date_histogram"
            field: "@timestamp"
            interval: "5m"
          }
        },
        {
          title: "Detection Accuracy"
          type: "stat"
          datasource: "prometheus"
          query: "log_anomaly_detection_accuracy"
        },
        {
          title: "False Positive Rate"
          type: "graph"
          datasource: "prometheus"
          query: "rate(log_anomaly_detection_results_total{result_type=\"false_positive\"}[5m])"
        }
      ]
    }
  ]
  
  alerts: [
    {
      name: "High False Positive Rate"
      condition: "false_positive_rate > 0.1"
      frequency: "5m"
      notifications: ["slack", "email"]
    },
    {
      name: "Detection Accuracy Degraded"
      condition: "detection_accuracy < 0.9"
      frequency: "10m"
      notifications: ["slack", "pagerduty"]
    }
  ]
}
```

## 工程实践示例

### 微服务异常检测

```dsl
microservice_anomaly "order_service_anomaly" {
  description: "订单服务异常检测"
  
  services: [
    {
      name: "order-service"
      metrics: [
        {
          name: "order_creation_rate"
          type: "counter"
          aggregation: "rate"
          window: "5m"
        },
        {
          name: "order_processing_time"
          type: "histogram"
          aggregation: "percentile"
          percentile: 95
        },
        {
          name: "order_failure_rate"
          type: "ratio"
          numerator: "failed_orders"
          denominator: "total_orders"
        }
      ]
    },
    {
      name: "payment-service"
      metrics: [
        {
          name: "payment_success_rate"
          type: "ratio"
          numerator: "successful_payments"
          denominator: "total_payments"
        },
        {
          name: "payment_processing_time"
          type: "histogram"
          aggregation: "percentile"
          percentile: 95
        }
      ]
    }
  ]
  
  correlation: {
    services: ["order-service", "payment-service"]
    correlation_threshold: 0.7
    time_window: "15m"
  }
  
  detection: [
    {
      name: "order_flow_anomaly"
      type: "workflow_anomaly"
      steps: ["order_created", "payment_processed", "order_completed"]
      metrics: ["success_rate", "average_duration"]
      threshold: 0.95
    },
    {
      name: "service_dependency_anomaly"
      type: "correlation_anomaly"
      method: "granger_causality"
      significance_level: 0.05
    }
  ]
  
  alerting: {
    rules: [
      {
        name: "Order Flow Failure"
        condition: "order_flow_success_rate < 0.95"
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

### 实时流异常检测

```dsl
stream_anomaly "real_time_anomaly_detection" {
  description: "实时流异常检测"
  
  stream_processing: {
    engine: "kafka_streams"
    input_topic: "log-stream"
    output_topic: "anomaly-alerts"
    
    processing: {
      window_size: "5m"
      slide_interval: "1m"
      state_store: "anomaly_state"
    }
  }
  
  real_time_detection: [
    {
      name: "error_rate_monitoring"
      type: "sliding_window"
      window: "5m"
      metric: "error_rate"
      algorithm: "z_score"
      threshold: 3.0
      action: "alert"
    },
    {
      name: "pattern_anomaly"
      type: "online_learning"
      algorithm: "isolation_forest"
      update_frequency: "1m"
      batch_size: 100
      sensitivity: "adaptive"
    },
    {
      name: "trend_anomaly"
      type: "exponential_smoothing"
      alpha: 0.3
      forecast_horizon: "10m"
      confidence_interval: 0.95
    }
  ]
  
  performance: {
    latency: { p95: "100ms", p99: "500ms" }
    throughput: { events_per_second: 10000 }
    scalability: {
      auto_scaling: true
      min_instances: 2
      max_instances: 10
      scale_up_threshold: 0.8
      scale_down_threshold: 0.3
    }
  }
  
  monitoring: {
    metrics: [
      "detection_latency",
      "throughput",
      "accuracy",
      "false_positive_rate",
      "false_negative_rate"
    ]
    health_checks: [
      "kafka_connectivity",
      "state_store_health",
      "model_health"
    ]
    alerting: {
      on_accuracy_degradation: true
      on_high_latency: true
      on_model_drift: true
    }
  }
}
```

这个DSL设计提供了完整的日志异常检测建模能力，支持多种异常检测算法、自适应阈值调整、机器学习集成，并能够与主流监控平台无缝集成。
