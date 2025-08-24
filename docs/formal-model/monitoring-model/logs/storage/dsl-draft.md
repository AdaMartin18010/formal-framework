# 日志存储建模DSL草案

## 1. 设计目标

- 用声明式语法描述日志存储后端、索引、分区、生命周期、备份等流程
- 支持多类型、多规模日志统一存储建模
- 便于自动生成存储与归档配置
- 支持多级存储、冷热分层、自动优化等高级特性

## 2. 基本语法结构

```dsl
log_store "web_service_logs" {
  description: "Web服务日志存储"
  version: "1.0.0"
  author: "system"
  
  backend: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
    cluster_name: "production-cluster"
    version: "8.5.0"
    authentication: {
      enabled: true
      type: "basic"
      username: "elastic"
      password: "changeme"
    }
  }
  
  index: {
    name: "web-service-logs"
    pattern: "web-service-logs-{YYYY.MM.DD}"
    settings: {
      number_of_shards: 3
      number_of_replicas: 1
      refresh_interval: "1s"
    }
    mapping: {
      dynamic: "strict"
      properties: {
        timestamp: {
          type: "date"
          format: "strict_date_optional_time||epoch_millis"
        }
        level: {
          type: "keyword"
        }
        message: {
          type: "text"
          analyzer: "standard"
        }
        service: {
          type: "keyword"
        }
      }
    }
  }
  
  partitioning: {
    enabled: true
    strategy: "time_based"
    field: "timestamp"
    interval: "daily"
    format: "YYYY.MM.DD"
  }
  
  lifecycle: {
    enabled: true
    phases: [
      {
        name: "hot"
        min_age: "0ms"
        actions: {
          rollover: {
            max_size: "50GB"
            max_age: "1d"
          }
        }
      },
      {
        name: "warm"
        min_age: "1d"
        actions: {
          forcemerge: {
            max_num_segments: 1
          }
        }
      },
      {
        name: "delete"
        min_age: "30d"
        actions: {
          delete: {}
        }
      }
    ]
  }
  
  backup: {
    enabled: true
    strategy: "snapshot"
    schedule: "0 2 * * *"
    retention: {
      max_snapshots: 30
      max_age: "90d"
    }
    repositories: [
      {
        name: "s3_backup"
        type: "s3"
        settings: {
          bucket: "logs-backup"
          region: "us-east-1"
          base_path: "elasticsearch/snapshots"
        }
      }
    ]
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "index_size",
      "document_count",
      "search_rate",
      "indexing_rate",
      "disk_usage"
    ]
    alerts: [
      {
        name: "high_disk_usage"
        condition: "disk_usage > 0.9"
        duration: "5m"
      }
    ]
  }
}
```

## 3. 关键元素

- log_store：日志存储声明
- description：描述信息
- version：版本号
- author：作者
- backend：存储后端配置
- index：索引配置
- partitioning：分区策略
- lifecycle：生命周期管理
- backup：备份配置
- monitoring：监控配置

## 4. 高级用法

### 4.1 多级存储配置

```dsl
log_store "multi_tier_storage" {
  description: "多级日志存储"
  version: "1.0.0"
  author: "system"
  
  tiers: [
    {
      name: "hot_tier"
      backend: {
        type: "elasticsearch"
        endpoint: "http://elasticsearch-hot:9200"
        cluster_name: "hot-cluster"
      }
      index: {
        name: "logs-hot"
        pattern: "logs-hot-{YYYY.MM.DD}"
        settings: {
          number_of_shards: 5
          number_of_replicas: 1
          refresh_interval: "500ms"
        }
      }
      retention: "7d"
    },
    {
      name: "warm_tier"
      backend: {
        type: "elasticsearch"
        endpoint: "http://elasticsearch-warm:9200"
        cluster_name: "warm-cluster"
      }
      index: {
        name: "logs-warm"
        pattern: "logs-warm-{YYYY.MM}"
        settings: {
          number_of_shards: 3
          number_of_replicas: 1
          refresh_interval: "30s"
        }
      }
      retention: "30d"
    },
    {
      name: "cold_tier"
      backend: {
        type: "s3"
        bucket: "logs-cold"
        region: "us-east-1"
        prefix: "elasticsearch/"
      }
      index: {
        name: "logs-cold"
        pattern: "logs-cold-{YYYY}"
      }
      retention: "365d"
    }
  ]
  
  data_movement: {
    enabled: true
    policies: [
      {
        name: "hot_to_warm"
        source_tier: "hot_tier"
        target_tier: "warm_tier"
        condition: "age > 7d"
        schedule: "0 1 * * *"
      },
      {
        name: "warm_to_cold"
        source_tier: "warm_tier"
        target_tier: "cold_tier"
        condition: "age > 30d"
        schedule: "0 2 * * 0"
      }
    ]
  }
}
```

### 4.2 分布式存储配置

```dsl
log_store "distributed_storage" {
  description: "分布式日志存储"
  version: "1.0.0"
  author: "system"
  
  backend: {
    type: "elasticsearch"
    endpoints: [
      "http://es-node-1:9200",
      "http://es-node-2:9200",
      "http://es-node-3:9200"
    ]
    cluster_name: "distributed-cluster"
    discovery: {
      enabled: true
      type: "zen"
      ping_timeout: "30s"
    }
  }
  
  index: {
    name: "distributed-logs"
    pattern: "distributed-logs-{YYYY.MM.DD}"
    settings: {
      number_of_shards: 6
      number_of_replicas: 2
      refresh_interval: "1s"
    }
  }
  
  sharding: {
    strategy: "hash"
    key: "service"
    num_shards: 6
    routing: {
      enabled: true
      field: "service"
    }
  }
  
  replication: {
    enabled: true
    factor: 2
    strategy: "async"
    consistency: "quorum"
  }
  
  backup: {
    enabled: true
    strategy: "distributed_snapshot"
    schedule: "0 3 * * *"
    repositories: [
      {
        name: "s3_backup"
        type: "s3"
        settings: {
          bucket: "logs-backup"
          region: "us-east-1"
          base_path: "elasticsearch/snapshots"
        }
      }
    ]
  }
}
```

## 5. 代码生成模板

### 5.1 Elasticsearch配置生成

```yaml
# elasticsearch.yml
cluster.name: production-cluster
node.name: es-node-1
path.data: /var/lib/elasticsearch
path.logs: /var/log/elasticsearch

network.host: 0.0.0.0
http.port: 9200

discovery.seed_hosts: ["es-node-1", "es-node-2", "es-node-3"]
cluster.initial_master_nodes: ["es-node-1", "es-node-2", "es-node-3"]

xpack.security.enabled: true
xpack.security.transport.ssl.enabled: true
```

### 5.2 索引模板配置生成

```json
{
  "index_patterns": ["web-service-logs-*"],
  "template": {
    "settings": {
      "number_of_shards": 3,
      "number_of_replicas": 1,
      "refresh_interval": "1s"
    },
    "mappings": {
      "dynamic": "strict",
      "properties": {
        "timestamp": {
          "type": "date",
          "format": "strict_date_optional_time||epoch_millis"
        },
        "level": {
          "type": "keyword"
        },
        "message": {
          "type": "text",
          "analyzer": "standard"
        },
        "service": {
          "type": "keyword"
        }
      }
    }
  }
}
```

### 5.3 Kubernetes部署配置生成

```yaml
# elasticsearch-statefulset.yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: elasticsearch
  namespace: logging
spec:
  serviceName: elasticsearch
  replicas: 3
  selector:
    matchLabels:
      app: elasticsearch
  template:
    metadata:
      labels:
        app: elasticsearch
    spec:
      containers:
      - name: elasticsearch
        image: docker.elastic.co/elasticsearch/elasticsearch:8.5.0
        env:
        - name: cluster.name
          value: "production-cluster"
        - name: node.name
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: discovery.seed_hosts
          value: "elasticsearch-0.elasticsearch,elasticsearch-1.elasticsearch,elasticsearch-2.elasticsearch"
        - name: cluster.initial_master_nodes
          value: "elasticsearch-0,elasticsearch-1,elasticsearch-2"
        - name: ES_JAVA_OPTS
          value: "-Xms2g -Xmx2g"
        ports:
        - containerPort: 9200
          name: http
        - containerPort: 9300
          name: transport
        volumeMounts:
        - name: data
          mountPath: /usr/share/elasticsearch/data
        resources:
          limits:
            memory: 4Gi
            cpu: 2
          requests:
            memory: 2Gi
            cpu: 1
  volumeClaimTemplates:
  - metadata:
      name: data
    spec:
      accessModes: [ "ReadWriteOnce" ]
      resources:
        requests:
          storage: 100Gi
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - log_store.name
    - log_store.description
    - log_store.version
    - log_store.backend
  
  type_constraints:
    - field: "log_store.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "log_store.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "log_store.backend.type"
      type: "string"
      enum: ["elasticsearch", "loki", "clickhouse", "s3", "hdfs"]
```

### 6.2 存储验证规则

```yaml
storage_validation:
  backend_consistency:
    - rule: "backend type must be supported"
    - rule: "backend endpoint must be accessible"
    - rule: "backend authentication must be valid"
  
  index_validation:
    - rule: "index name must be valid"
    - rule: "index settings must be consistent"
    - rule: "index mapping must be valid"
  
  lifecycle_validation:
    - rule: "lifecycle phases must be valid"
    - rule: "retention periods must be positive"
    - rule: "backup schedules must be valid"
```

## 7. 最佳实践

### 7.1 存储设计模式

```dsl
# 基础存储模式
log_store "basic_store" {
  description: "基础日志存储"
  version: "1.0.0"
  
  backend: {
    type: "elasticsearch"
    endpoint: "http://elasticsearch:9200"
  }
  
  index: {
    name: "logs"
    pattern: "logs-{YYYY.MM.DD}"
  }
  
  lifecycle: {
    enabled: true
    phases: [
      {
        name: "hot"
        min_age: "0ms"
        actions: {
          rollover: {
            max_size: "10GB"
            max_age: "1d"
          }
        }
      },
      {
        name: "delete"
        min_age: "30d"
        actions: {
          delete: {}
        }
      }
    ]
  }
}

# 分层存储模式
log_store "tiered_store" {
  description: "分层日志存储"
  version: "1.0.0"
  
  tiers: [
    {
      name: "hot"
      backend: {
        type: "elasticsearch"
        endpoint: "http://es-hot:9200"
      }
      retention: "7d"
    },
    {
      name: "warm"
      backend: {
        type: "elasticsearch"
        endpoint: "http://es-warm:9200"
      }
      retention: "30d"
    },
    {
      name: "cold"
      backend: {
        type: "s3"
        bucket: "logs-cold"
      }
      retention: "365d"
    }
  ]
}
```

### 7.2 存储命名规范

```dsl
# 推荐命名模式
log_store "service_environment_store" {
  # 服务_环境_存储
}

log_store "tier_purpose_store" {
  # 层级_用途_存储
}

log_store "region_cluster_store" {
  # 区域_集群_存储
}
```

## 8. 与主流标准的映射

| DSL元素 | Elasticsearch | Loki | ClickHouse | S3/HDFS |
|---------|---------------|------|------------|---------|
| log_store | index | stream | table | bucket |
| backend | cluster | instance | cluster | storage |
| index | mapping | label | schema | prefix |
| partitioning | shard | stream | partition | prefix |
| lifecycle | ilm | retention | ttl | lifecycle |
| backup | snapshot | backup | backup | versioning |

## 9. 工程实践示例

```dsl
# 生产环境日志存储配置示例
log_store "production_log_storage" {
  description: "生产环境日志存储"
  version: "1.0.0"
  author: "system"
  
  backend: {
    type: "elasticsearch"
    endpoints: [
      "http://es-node-1:9200",
      "http://es-node-2:9200",
      "http://es-node-3:9200"
    ]
    cluster_name: "production-cluster"
    version: "8.5.0"
    authentication: {
      enabled: true
      type: "service_account"
      service_account: "elasticsearch"
      namespace: "logging"
    }
    tls: {
      enabled: true
      verify_hostname: true
      ca_cert: "/etc/ssl/certs/ca.crt"
    }
  }
  
  index: {
    name: "production-logs"
    pattern: "production-logs-{YYYY.MM.DD}"
    settings: {
      number_of_shards: 6
      number_of_replicas: 2
      refresh_interval: "1s"
      max_result_window: 10000
    }
    mapping: {
      dynamic: "strict"
      properties: {
        timestamp: {
          type: "date"
          format: "strict_date_optional_time||epoch_millis"
        }
        level: {
          type: "keyword"
        }
        message: {
          type: "text"
          analyzer: "standard"
          fields: {
            keyword: {
              type: "keyword"
              ignore_above: 256
            }
          }
        }
        service: {
          type: "keyword"
        }
        environment: {
          type: "keyword"
        }
        trace_id: {
          type: "keyword"
        }
      }
    }
  }
  
  partitioning: {
    enabled: true
    strategy: "time_based"
    field: "timestamp"
    interval: "daily"
    format: "YYYY.MM.DD"
    timezone: "UTC"
  }
  
  lifecycle: {
    enabled: true
    phases: [
      {
        name: "hot"
        min_age: "0ms"
        actions: {
          rollover: {
            max_size: "100GB"
            max_age: "1d"
          }
        }
      },
      {
        name: "warm"
        min_age: "1d"
        actions: {
          forcemerge: {
            max_num_segments: 1
          }
        }
      },
      {
        name: "cold"
        min_age: "7d"
        actions: {
          freeze: {}
        }
      },
      {
        name: "delete"
        min_age: "365d"
        actions: {
          delete: {}
        }
      }
    ]
  }
  
  backup: {
    enabled: true
    strategy: "snapshot"
    schedule: "0 2 * * *"
    retention: {
      max_snapshots: 100
      max_age: "365d"
    }
    repositories: [
      {
        name: "s3_backup"
        type: "s3"
        settings: {
          bucket: "logs-backup"
          region: "us-east-1"
          base_path: "elasticsearch/snapshots"
        }
      }
    ]
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "index_size",
      "document_count",
      "search_rate",
      "indexing_rate",
      "disk_usage"
    ]
    alerts: [
      {
        name: "high_disk_usage"
        condition: "disk_usage > 0.9"
        duration: "5m"
        severity: "critical"
      },
      {
        name: "high_search_latency"
        condition: "query_latency > 1s"
        duration: "10m"
        severity: "warning"
      }
    ]
    dashboards: [
      "https://grafana.example.com/d/elasticsearch"
    ]
  }
  
  security: {
    enabled: true
    authentication: {
      enabled: true
      type: "service_account"
      service_account: "elasticsearch"
      namespace: "logging"
    }
    encryption: {
      enabled: true
      algorithm: "AES-256"
      key_rotation: "30d"
    }
  }
}
```

这个DSL设计为日志存储建模提供了完整的配置语言，支持基础存储、多级存储、分布式存储等多种模式，同时保持了良好的可扩展性和可维护性。
