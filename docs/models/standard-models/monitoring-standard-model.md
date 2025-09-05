# 监控标准模型

## 概述

监控标准模型定义了系统监控的标准化实现，基于监控元模型构建，提供统一的监控指标、告警机制和可视化展示。

## 标准监控指标

### 1. 系统指标

#### 基础系统指标

```yaml
SystemMetrics:
  cpu:
    usage_percent: "gauge"
    load_average_1m: "gauge"
    load_average_5m: "gauge"
    load_average_15m: "gauge"
    context_switches: "counter"
    interrupts: "counter"
  
  memory:
    total_bytes: "gauge"
    used_bytes: "gauge"
    free_bytes: "gauge"
    available_bytes: "gauge"
    cached_bytes: "gauge"
    buffer_bytes: "gauge"
    swap_total_bytes: "gauge"
    swap_used_bytes: "gauge"
  
  disk:
    total_bytes: "gauge"
    used_bytes: "gauge"
    free_bytes: "gauge"
    usage_percent: "gauge"
    read_iops: "counter"
    write_iops: "counter"
    read_throughput_bytes: "counter"
    write_throughput_bytes: "counter"
  
  network:
    bytes_sent: "counter"
    bytes_received: "counter"
    packets_sent: "counter"
    packets_received: "counter"
    errors_in: "counter"
    errors_out: "counter"
    drops_in: "counter"
    drops_out: "counter"
```

#### 实现示例

```python
import psutil
import time
from typing import Dict, Any, List
from dataclasses import dataclass
from prometheus_client import Gauge, Counter, start_http_server

@dataclass
class SystemMetrics:
    cpu_usage_percent: float
    memory_used_bytes: int
    memory_total_bytes: int
    disk_used_bytes: int
    disk_total_bytes: int
    network_bytes_sent: int
    network_bytes_received: int

class SystemMonitor:
    """标准系统监控器"""
    
    def __init__(self, port: int = 8000):
        self.port = port
        self.metrics = self._init_metrics()
        self.previous_network_stats = None
    
    def _init_metrics(self) -> Dict[str, Any]:
        """初始化监控指标"""
        return {
            "cpu_usage_percent": Gauge("system_cpu_usage_percent", "CPU使用率百分比"),
            "memory_used_bytes": Gauge("system_memory_used_bytes", "内存使用字节数"),
            "memory_total_bytes": Gauge("system_memory_total_bytes", "内存总字节数"),
            "disk_used_bytes": Gauge("system_disk_used_bytes", "磁盘使用字节数"),
            "disk_total_bytes": Gauge("system_disk_total_bytes", "磁盘总字节数"),
            "network_bytes_sent": Counter("system_network_bytes_sent_total", "网络发送字节数"),
            "network_bytes_received": Counter("system_network_bytes_received_total", "网络接收字节数"),
        }
    
    def start_monitoring(self):
        """开始监控"""
        start_http_server(self.port)
        
        while True:
            metrics = self.collect_metrics()
            self.update_metrics(metrics)
            time.sleep(10)  # 每10秒收集一次
    
    def collect_metrics(self) -> SystemMetrics:
        """收集系统指标"""
        # CPU指标
        cpu_usage = psutil.cpu_percent(interval=1)
        
        # 内存指标
        memory = psutil.virtual_memory()
        
        # 磁盘指标
        disk = psutil.disk_usage('/')
        
        # 网络指标
        network_stats = psutil.net_io_counters()
        
        return SystemMetrics(
            cpu_usage_percent=cpu_usage,
            memory_used_bytes=memory.used,
            memory_total_bytes=memory.total,
            disk_used_bytes=disk.used,
            disk_total_bytes=disk.total,
            network_bytes_sent=network_stats.bytes_sent,
            network_bytes_received=network_stats.bytes_recv
        )
    
    def update_metrics(self, metrics: SystemMetrics):
        """更新监控指标"""
        self.metrics["cpu_usage_percent"].set(metrics.cpu_usage_percent)
        self.metrics["memory_used_bytes"].set(metrics.memory_used_bytes)
        self.metrics["memory_total_bytes"].set(metrics.memory_total_bytes)
        self.metrics["disk_used_bytes"].set(metrics.disk_used_bytes)
        self.metrics["disk_total_bytes"].set(metrics.disk_total_bytes)
        
        # 网络指标需要计算增量
        if self.previous_network_stats:
            sent_delta = metrics.network_bytes_sent - self.previous_network_stats.bytes_sent
            received_delta = metrics.network_bytes_received - self.previous_network_stats.bytes_recv
            
            self.metrics["network_bytes_sent"].inc(sent_delta)
            self.metrics["network_bytes_received"].inc(received_delta)
        
        self.previous_network_stats = psutil.net_io_counters()
```

### 2. 应用指标

#### 应用性能指标

```yaml
ApplicationMetrics:
  http_requests:
    total: "counter"
    duration_seconds: "histogram"
    status_codes: "counter"
  
  business_metrics:
    active_users: "gauge"
    transactions_per_second: "gauge"
    revenue_per_hour: "gauge"
    error_rate: "gauge"
  
  database:
    connection_pool_size: "gauge"
    active_connections: "gauge"
    query_duration_seconds: "histogram"
    slow_queries: "counter"
  
  cache:
    hit_rate: "gauge"
    miss_rate: "gauge"
    eviction_count: "counter"
    memory_usage_bytes: "gauge"
```

#### 实现示例1

```python
from prometheus_client import Counter, Histogram, Gauge
from typing import Dict, Any
import time
from functools import wraps

class ApplicationMonitor:
    """标准应用监控器"""
    
    def __init__(self):
        self.metrics = self._init_metrics()
    
    def _init_metrics(self) -> Dict[str, Any]:
        """初始化应用指标"""
        return {
            "http_requests_total": Counter("http_requests_total", "HTTP请求总数", ["method", "endpoint", "status"]),
            "http_request_duration": Histogram("http_request_duration_seconds", "HTTP请求持续时间", ["method", "endpoint"]),
            "active_users": Gauge("active_users", "活跃用户数"),
            "transactions_per_second": Gauge("transactions_per_second", "每秒事务数"),
            "error_rate": Gauge("error_rate", "错误率"),
            "db_connection_pool_size": Gauge("db_connection_pool_size", "数据库连接池大小"),
            "db_query_duration": Histogram("db_query_duration_seconds", "数据库查询持续时间", ["query_type"]),
            "cache_hit_rate": Gauge("cache_hit_rate", "缓存命中率"),
        }
    
    def track_http_request(self, method: str, endpoint: str, status_code: int, duration: float):
        """跟踪HTTP请求"""
        self.metrics["http_requests_total"].labels(
            method=method, 
            endpoint=endpoint, 
            status=str(status_code)
        ).inc()
        
        self.metrics["http_request_duration"].labels(
            method=method, 
            endpoint=endpoint
        ).observe(duration)
    
    def update_business_metrics(self, active_users: int, tps: float, error_rate: float):
        """更新业务指标"""
        self.metrics["active_users"].set(active_users)
        self.metrics["transactions_per_second"].set(tps)
        self.metrics["error_rate"].set(error_rate)
    
    def track_database_query(self, query_type: str, duration: float):
        """跟踪数据库查询"""
        self.metrics["db_query_duration"].labels(query_type=query_type).observe(duration)
    
    def update_cache_metrics(self, hit_rate: float):
        """更新缓存指标"""
        self.metrics["cache_hit_rate"].set(hit_rate)

# 装饰器用于自动监控HTTP请求
def monitor_http_request(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        start_time = time.time()
        try:
            result = func(*args, **kwargs)
            status_code = 200
            return result
        except Exception as e:
            status_code = 500
            raise
        finally:
            duration = time.time() - start_time
            # 这里应该获取实际的method和endpoint
            monitor.track_http_request("GET", "/api/endpoint", status_code, duration)
    
    return wrapper

# 全局监控器实例
monitor = ApplicationMonitor()
```

### 3. 业务指标

#### 业务KPI指标

```yaml
BusinessMetrics:
  user_engagement:
    daily_active_users: "gauge"
    monthly_active_users: "gauge"
    session_duration_seconds: "histogram"
    page_views: "counter"
  
  revenue:
    total_revenue: "counter"
    revenue_per_user: "gauge"
    conversion_rate: "gauge"
    average_order_value: "gauge"
  
  performance:
    response_time_p95: "gauge"
    response_time_p99: "gauge"
    availability_percent: "gauge"
    throughput_rps: "gauge"
```

## 标准告警机制

### 1. 告警规则

#### 告警配置

```yaml
AlertRules:
  - name: "HighCPUUsage"
    condition: "cpu_usage_percent > 80"
    duration: "5m"
    severity: "warning"
    labels:
      service: "system"
      component: "cpu"
  
  - name: "HighMemoryUsage"
    condition: "memory_usage_percent > 90"
    duration: "3m"
    severity: "critical"
    labels:
      service: "system"
      component: "memory"
  
  - name: "HighErrorRate"
    condition: "error_rate > 5"
    duration: "2m"
    severity: "critical"
    labels:
      service: "application"
      component: "errors"
  
  - name: "SlowResponseTime"
    condition: "response_time_p95 > 1000"
    duration: "5m"
    severity: "warning"
    labels:
      service: "application"
      component: "performance"
```

#### 实现示例2

```python
from typing import Dict, Any, List, Callable
from dataclasses import dataclass
from enum import Enum
import time

class AlertSeverity(Enum):
    INFO = "info"
    WARNING = "warning"
    CRITICAL = "critical"

@dataclass
class AlertRule:
    name: str
    condition: str
    duration: str
    severity: AlertSeverity
    labels: Dict[str, str]

@dataclass
class Alert:
    rule_name: str
    severity: AlertSeverity
    message: str
    labels: Dict[str, str]
    timestamp: float
    resolved: bool = False

class AlertManager:
    """标准告警管理器"""
    
    def __init__(self, rules: List[AlertRule]):
        self.rules = rules
        self.active_alerts = {}
        self.notification_handlers = []
    
    def add_notification_handler(self, handler: Callable):
        """添加通知处理器"""
        self.notification_handlers.append(handler)
    
    def evaluate_rules(self, metrics: Dict[str, float]):
        """评估告警规则"""
        for rule in self.rules:
            if self._evaluate_condition(rule.condition, metrics):
                self._trigger_alert(rule, metrics)
            else:
                self._resolve_alert(rule.name)
    
    def _evaluate_condition(self, condition: str, metrics: Dict[str, float]) -> bool:
        """评估告警条件"""
        # 简化的条件评估，实际应该使用更复杂的表达式解析器
        try:
            # 替换指标名称
            for metric_name, value in metrics.items():
                condition = condition.replace(metric_name, str(value))
            
            # 评估条件
            return eval(condition)
        except:
            return False
    
    def _trigger_alert(self, rule: AlertRule, metrics: Dict[str, float]):
        """触发告警"""
        alert_key = rule.name
        
        if alert_key not in self.active_alerts:
            alert = Alert(
                rule_name=rule.name,
                severity=rule.severity,
                message=f"告警触发: {rule.name}",
                labels=rule.labels,
                timestamp=time.time()
            )
            
            self.active_alerts[alert_key] = alert
            self._send_notifications(alert)
    
    def _resolve_alert(self, rule_name: str):
        """解决告警"""
        if rule_name in self.active_alerts:
            alert = self.active_alerts[rule_name]
            alert.resolved = True
            self._send_notifications(alert)
            del self.active_alerts[rule_name]
    
    def _send_notifications(self, alert: Alert):
        """发送通知"""
        for handler in self.notification_handlers:
            try:
                handler(alert)
            except Exception as e:
                print(f"通知发送失败: {e}")

# 通知处理器示例
def slack_notification_handler(alert: Alert):
    """Slack通知处理器"""
    status = "解决" if alert.resolved else "触发"
    message = f"告警{status}: {alert.rule_name} - {alert.message}"
    print(f"发送Slack通知: {message}")

def email_notification_handler(alert: Alert):
    """邮件通知处理器"""
    status = "解决" if alert.resolved else "触发"
    message = f"告警{status}: {alert.rule_name} - {alert.message}"
    print(f"发送邮件通知: {message}")
```

### 2. 告警聚合

#### 告警聚合策略

```yaml
AlertAggregation:
  grouping:
    by_labels: ["service", "component"]
    group_wait: "30s"
    group_interval: "5m"
    repeat_interval: "1h"
  
  inhibition:
    - source_match:
        severity: "critical"
      target_match:
        severity: "warning"
      equal: ["service"]
  
  silence:
    - matchers:
        - name: "service"
          value: "maintenance"
      duration: "2h"
```

## 标准可视化

### 1. 仪表板配置

#### Grafana仪表板

```json
{
  "dashboard": {
    "title": "系统监控仪表板",
    "panels": [
      {
        "title": "CPU使用率",
        "type": "graph",
        "targets": [
          {
            "expr": "cpu_usage_percent",
            "legendFormat": "CPU使用率"
          }
        ]
      },
      {
        "title": "内存使用率",
        "type": "graph",
        "targets": [
          {
            "expr": "memory_used_bytes / memory_total_bytes * 100",
            "legendFormat": "内存使用率"
          }
        ]
      },
      {
        "title": "HTTP请求数",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_requests_total[5m])",
            "legendFormat": "{{method}} {{endpoint}}"
          }
        ]
      }
    ]
  }
}
```

### 2. 自定义可视化

#### 实现示例3

```python
import matplotlib.pyplot as plt
import pandas as pd
from typing import List, Dict, Any
import json

class VisualizationManager:
    """标准可视化管理器"""
    
    def __init__(self):
        self.charts = {}
    
    def create_time_series_chart(self, data: pd.DataFrame, title: str, metrics: List[str]):
        """创建时间序列图表"""
        plt.figure(figsize=(12, 6))
        
        for metric in metrics:
            if metric in data.columns:
                plt.plot(data.index, data[metric], label=metric)
        
        plt.title(title)
        plt.xlabel("时间")
        plt.ylabel("值")
        plt.legend()
        plt.grid(True)
        
        return plt.gcf()
    
    def create_histogram(self, data: List[float], title: str, bins: int = 30):
        """创建直方图"""
        plt.figure(figsize=(10, 6))
        plt.hist(data, bins=bins, alpha=0.7, edgecolor='black')
        plt.title(title)
        plt.xlabel("值")
        plt.ylabel("频次")
        plt.grid(True)
        
        return plt.gcf()
    
    def create_heatmap(self, data: pd.DataFrame, title: str):
        """创建热力图"""
        plt.figure(figsize=(10, 8))
        plt.imshow(data.values, cmap='YlOrRd', aspect='auto')
        plt.colorbar()
        plt.title(title)
        plt.xlabel("列")
        plt.ylabel("行")
        
        return plt.gcf()
    
    def export_dashboard_config(self, dashboard_name: str) -> Dict[str, Any]:
        """导出仪表板配置"""
        return {
            "dashboard": {
                "title": dashboard_name,
                "panels": self._generate_panel_configs()
            }
        }
    
    def _generate_panel_configs(self) -> List[Dict[str, Any]]:
        """生成面板配置"""
        return [
            {
                "title": "系统指标",
                "type": "graph",
                "targets": [
                    {
                        "expr": "cpu_usage_percent",
                        "legendFormat": "CPU使用率"
                    },
                    {
                        "expr": "memory_usage_percent",
                        "legendFormat": "内存使用率"
                    }
                ]
            },
            {
                "title": "应用指标",
                "type": "graph",
                "targets": [
                    {
                        "expr": "rate(http_requests_total[5m])",
                        "legendFormat": "HTTP请求率"
                    }
                ]
            }
        ]
```

## 标准日志管理

### 1. 日志收集

#### 日志配置

```yaml
LogCollection:
  sources:
    - type: "file"
      paths: ["/var/log/app/*.log"]
      format: "json"
    - type: "syslog"
      port: 514
      protocol: "udp"
    - type: "journald"
      units: ["app.service"]
  
  processing:
    parsing:
      - field: "timestamp"
        format: "RFC3339"
      - field: "level"
        mapping:
          "ERROR": "error"
          "WARN": "warning"
          "INFO": "info"
          "DEBUG": "debug"
    
    enrichment:
      - add_hostname: true
      - add_service_name: true
      - add_environment: true
  
  output:
    - type: "elasticsearch"
      endpoint: "http://elasticsearch:9200"
      index: "logs-{date}"
    - type: "kafka"
      brokers: ["kafka:9092"]
      topic: "logs"
```

### 2. 日志分析

#### 实现示例4

```python
import re
from typing import List, Dict, Any, Optional
from dataclasses import dataclass
from datetime import datetime

@dataclass
class LogEntry:
    timestamp: datetime
    level: str
    message: str
    service: str
    hostname: str
    metadata: Dict[str, Any]

class LogAnalyzer:
    """标准日志分析器"""
    
    def __init__(self):
        self.patterns = {
            "error": re.compile(r"ERROR|FATAL|CRITICAL", re.IGNORECASE),
            "warning": re.compile(r"WARN|WARNING", re.IGNORECASE),
            "info": re.compile(r"INFO", re.IGNORECASE),
            "debug": re.compile(r"DEBUG", re.IGNORECASE),
        }
    
    def analyze_logs(self, logs: List[LogEntry]) -> Dict[str, Any]:
        """分析日志"""
        analysis = {
            "total_logs": len(logs),
            "error_count": 0,
            "warning_count": 0,
            "info_count": 0,
            "debug_count": 0,
            "error_rate": 0.0,
            "top_errors": [],
            "service_distribution": {},
            "time_distribution": {}
        }
        
        for log in logs:
            # 统计日志级别
            if self.patterns["error"].search(log.message):
                analysis["error_count"] += 1
            elif self.patterns["warning"].search(log.message):
                analysis["warning_count"] += 1
            elif self.patterns["info"].search(log.message):
                analysis["info_count"] += 1
            elif self.patterns["debug"].search(log.message):
                analysis["debug_count"] += 1
            
            # 统计服务分布
            service = log.service
            analysis["service_distribution"][service] = analysis["service_distribution"].get(service, 0) + 1
        
        # 计算错误率
        if analysis["total_logs"] > 0:
            analysis["error_rate"] = analysis["error_count"] / analysis["total_logs"] * 100
        
        # 获取常见错误
        analysis["top_errors"] = self._get_top_errors(logs)
        
        return analysis
    
    def _get_top_errors(self, logs: List[LogEntry]) -> List[Dict[str, Any]]:
        """获取常见错误"""
        error_messages = {}
        
        for log in logs:
            if self.patterns["error"].search(log.message):
                # 提取错误关键词
                error_key = self._extract_error_key(log.message)
                error_messages[error_key] = error_messages.get(error_key, 0) + 1
        
        # 按出现次数排序
        sorted_errors = sorted(error_messages.items(), key=lambda x: x[1], reverse=True)
        
        return [{"error": error, "count": count} for error, count in sorted_errors[:10]]
    
    def _extract_error_key(self, message: str) -> str:
        """提取错误关键词"""
        # 简化的错误关键词提取
        words = message.split()
        if len(words) > 3:
            return " ".join(words[:3])
        return message[:50]
```

## 最佳实践

1. **指标设计**: 设计有意义的监控指标
2. **告警策略**: 制定合理的告警规则和阈值
3. **可视化展示**: 创建直观的监控仪表板
4. **日志管理**: 建立完善的日志收集和分析机制
5. **性能优化**: 优化监控系统的性能
6. **安全考虑**: 保护监控数据的安全性
7. **文档维护**: 保持监控配置和流程文档的更新

## 相关文档

- [监控元模型](../meta-models/monitoring-model/README.md)
- [验证脚本](../../tools/verification-scripts/README.md)
- [可视化工具](../../tools/visualization/README.md)
