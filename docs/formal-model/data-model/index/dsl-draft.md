# 索引建模DSL设计

## 设计目标

索引建模DSL旨在提供声明式语言定义复杂的数据索引配置，支持多种索引类型、优化策略、性能调优、维护管理，并与主流数据库平台无缝集成。

## 基本语法

### 核心结构

```dsl
index_model "ecommerce_indexes" {
  description: "电商系统索引模型"
  version: "1.0.0"
  
  namespace: "ecommerce"
  labels: {
    domain: "ecommerce"
    environment: "production"
  }
  
  indexes: [
    {
      name: "idx_user_email"
      table: "users"
      fields: ["email"]
      type: "unique"
    }
  ]
}
```

### 基础索引

```dsl
index "idx_user_email" {
  description: "用户邮箱唯一索引"
  
  table: "users"
  fields: ["email"]
  type: "unique"
  
  properties: {
    method: "btree"
    fillfactor: 90
    concurrent: true
  }
  
  constraints: [
    {
      name: "unique_email"
      type: "unique"
      fields: ["email"]
    }
  ]
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_interval: "1w"
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "index_size",
      "index_usage",
      "index_scans",
      "index_tuples_read"
    ]
  }
}
```

### 复合索引

```dsl
index "idx_order_customer_status" {
  description: "订单客户状态复合索引"
  
  table: "orders"
  fields: ["customer_id", "status", "created_at"]
  type: "btree"
  
  properties: {
    method: "btree"
    fillfactor: 85
    concurrent: true
  }
  
  query_patterns: [
    {
      name: "customer_orders"
      pattern: "WHERE customer_id = ? AND status = ?"
      selectivity: 0.01
      frequency: "high"
    },
    {
      name: "customer_orders_by_date"
      pattern: "WHERE customer_id = ? AND created_at >= ?"
      selectivity: 0.05
      frequency: "medium"
    }
  ]
  
  optimization: {
    field_order: "optimal"
    compression: true
    partial: false
  }
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_interval: "2w"
  }
}
```

### 部分索引

```dsl
index "idx_active_products" {
  description: "活跃商品部分索引"
  
  table: "products"
  fields: ["category_id", "price", "created_at"]
  type: "btree"
  
  partial: {
    enabled: true
    condition: "is_active = true"
  }
  
  properties: {
    method: "btree"
    fillfactor: 90
    concurrent: true
  }
  
  query_patterns: [
    {
      name: "active_products_by_category"
      pattern: "WHERE category_id = ? AND is_active = true"
      selectivity: 0.1
      frequency: "high"
    },
    {
      name: "active_products_by_price"
      pattern: "WHERE price BETWEEN ? AND ? AND is_active = true"
      selectivity: 0.2
      frequency: "medium"
    }
  ]
  
  benefits: [
    "reduced_index_size",
    "faster_maintenance",
    "better_cache_efficiency"
  ]
}
```

### 函数索引

```dsl
index "idx_user_email_domain" {
  description: "用户邮箱域名函数索引"
  
  table: "users"
  fields: ["SUBSTRING(email FROM '@(.*)$')"]
  type: "btree"
  
  properties: {
    method: "btree"
    fillfactor: 90
    concurrent: true
  }
  
  query_patterns: [
    {
      name: "users_by_domain"
      pattern: "WHERE SUBSTRING(email FROM '@(.*)$') = ?"
      selectivity: 0.05
      frequency: "medium"
    }
  ]
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_interval: "1w"
  }
}
```

## 高级用法

### 全文搜索索引

```dsl
fulltext_index "idx_product_search" {
  description: "商品全文搜索索引"
  
  table: "products"
  fields: ["name", "description", "tags"]
  
  properties: {
    method: "gin"
    language: "english"
    stop_words: "english"
  }
  
  configuration: {
    text_search_config: "english"
    dictionary: "english_stem"
    stop_words: true
  }
  
  query_patterns: [
    {
      name: "product_search"
      pattern: "WHERE to_tsvector('english', name || ' ' || description) @@ plainto_tsquery('english', ?)"
      selectivity: 0.1
      frequency: "high"
    },
    {
      name: "tag_search"
      pattern: "WHERE tags && ARRAY[?]"
      selectivity: 0.2
      frequency: "medium"
    }
  ]
  
  optimization: {
    gin_pending_list_limit: 4096
    fast_update: true
  }
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_interval: "1w"
  }
}
```

### 空间索引

```dsl
spatial_index "idx_store_location" {
  description: "商店位置空间索引"
  
  table: "stores"
  fields: ["location"]
  
  properties: {
    method: "gist"
    operator_class: "gist_geometry_ops"
  }
  
  spatial_configuration: {
    srid: 4326
    geometry_type: "POINT"
    dimensions: 2
  }
  
  query_patterns: [
    {
      name: "nearby_stores"
      pattern: "WHERE ST_DWithin(location, ST_Point(?, ?), ?)"
      selectivity: 0.01
      frequency: "high"
    },
    {
      name: "stores_in_polygon"
      pattern: "WHERE ST_Contains(ST_GeomFromText(?), location)"
      selectivity: 0.05
      frequency: "medium"
    }
  ]
  
  optimization: {
    buffer_size: 256
    fillfactor: 90
  }
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_interval: "1m"
  }
}
```

### 哈希索引

```dsl
hash_index "idx_user_session" {
  description: "用户会话哈希索引"
  
  table: "user_sessions"
  fields: ["session_token"]
  
  properties: {
    method: "hash"
    fillfactor: 90
  }
  
  query_patterns: [
    {
      name: "session_lookup"
      pattern: "WHERE session_token = ?"
      selectivity: 0.001
      frequency: "very_high"
    }
  ]
  
  benefits: [
    "exact_match_performance",
    "memory_efficient",
    "fast_inserts"
  ]
  
  limitations: [
    "no_range_queries",
    "no_sorting",
    "no_partial_matches"
  ]
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_interval: "1w"
  }
}
```

### 位图索引

```dsl
bitmap_index "idx_product_attributes" {
  description: "商品属性位图索引"
  
  table: "products"
  fields: ["category_id", "brand_id", "is_active", "has_discount"]
  
  properties: {
    method: "bitmap"
    compression: true
  }
  
  query_patterns: [
    {
      name: "product_filtering"
      pattern: "WHERE category_id = ? AND brand_id = ? AND is_active = true"
      selectivity: 0.01
      frequency: "high"
    },
    {
      name: "discount_products"
      pattern: "WHERE has_discount = true AND is_active = true"
      selectivity: 0.1
      frequency: "medium"
    }
  ]
  
  optimization: {
    bitmap_scan: true
    compression_ratio: 0.3
  }
  
  benefits: [
    "efficient_boolean_operations",
    "good_compression",
    "fast_intersections"
  ]
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_interval: "1w"
  }
}
```

## 代码生成模板

### PostgreSQL索引

```sql
-- 生成的PostgreSQL索引
-- 基础唯一索引
CREATE UNIQUE INDEX CONCURRENTLY idx_user_email 
ON users (email) 
WITH (fillfactor = 90);

-- 复合索引
CREATE INDEX CONCURRENTLY idx_order_customer_status 
ON orders (customer_id, status, created_at) 
WITH (fillfactor = 85);

-- 部分索引
CREATE INDEX CONCURRENTLY idx_active_products 
ON products (category_id, price, created_at) 
WHERE is_active = true 
WITH (fillfactor = 90);

-- 函数索引
CREATE INDEX CONCURRENTLY idx_user_email_domain 
ON users (SUBSTRING(email FROM '@(.*)$')) 
WITH (fillfactor = 90);

-- 全文搜索索引
CREATE INDEX CONCURRENTLY idx_product_search 
ON products USING gin (to_tsvector('english', name || ' ' || description));

-- 空间索引
CREATE INDEX CONCURRENTLY idx_store_location 
ON stores USING gist (location);

-- 哈希索引
CREATE INDEX CONCURRENTLY idx_user_session 
ON user_sessions USING hash (session_token);

-- 索引统计信息
ANALYZE users;
ANALYZE orders;
ANALYZE products;
ANALYZE stores;
ANALYZE user_sessions;

-- 索引维护
REINDEX INDEX CONCURRENTLY idx_user_email;
REINDEX INDEX CONCURRENTLY idx_order_customer_status;
REINDEX INDEX CONCURRENTLY idx_active_products;
```

### MySQL索引

```sql
-- 生成的MySQL索引
-- 基础唯一索引
CREATE UNIQUE INDEX idx_user_email 
ON users (email) 
USING BTREE;

-- 复合索引
CREATE INDEX idx_order_customer_status 
ON orders (customer_id, status, created_at) 
USING BTREE;

-- 部分索引（MySQL 8.0+）
CREATE INDEX idx_active_products 
ON products (category_id, price, created_at) 
WHERE is_active = true;

-- 函数索引（MySQL 8.0+）
CREATE INDEX idx_user_email_domain 
ON users ((SUBSTRING_INDEX(email, '@', -1)));

-- 全文搜索索引
CREATE FULLTEXT INDEX idx_product_search 
ON products (name, description);

-- 空间索引
CREATE SPATIAL INDEX idx_store_location 
ON stores (location);

-- 哈希索引（InnoDB不支持，使用BTREE）
CREATE INDEX idx_user_session 
ON user_sessions (session_token) 
USING BTREE;

-- 索引统计信息
ANALYZE TABLE users;
ANALYZE TABLE orders;
ANALYZE TABLE products;
ANALYZE TABLE stores;
ANALYZE TABLE user_sessions;

-- 索引维护
OPTIMIZE TABLE users;
OPTIMIZE TABLE orders;
OPTIMIZE TABLE products;
OPTIMIZE TABLE stores;
OPTIMIZE TABLE user_sessions;
```

### 索引监控脚本

```python
# 生成的索引监控脚本
import psycopg2
import json
from datetime import datetime
from typing import Dict, List, Any

class IndexMonitor:
    def __init__(self, connection_string: str):
        self.conn_string = connection_string
    
    def get_index_statistics(self) -> Dict[str, Any]:
        """获取索引统计信息"""
        with psycopg2.connect(self.conn_string) as conn:
            with conn.cursor() as cur:
                # 查询索引使用情况
                cur.execute("""
                    SELECT 
                        schemaname,
                        tablename,
                        indexname,
                        idx_scan as index_scans,
                        idx_tup_read as tuples_read,
                        idx_tup_fetch as tuples_fetched,
                        pg_size_pretty(pg_relation_size(indexrelid)) as index_size
                    FROM pg_stat_user_indexes
                    ORDER BY idx_scan DESC
                """)
                
                indexes = []
                for row in cur.fetchall():
                    indexes.append({
                        'schema': row[0],
                        'table': row[1],
                        'index': row[2],
                        'scans': row[3],
                        'tuples_read': row[4],
                        'tuples_fetched': row[5],
                        'size': row[6]
                    })
                
                return {
                    'timestamp': datetime.now().isoformat(),
                    'indexes': indexes
                }
    
    def get_unused_indexes(self) -> List[Dict[str, Any]]:
        """获取未使用的索引"""
        with psycopg2.connect(self.conn_string) as conn:
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT 
                        schemaname,
                        tablename,
                        indexname,
                        pg_size_pretty(pg_relation_size(indexrelid)) as index_size
                    FROM pg_stat_user_indexes
                    WHERE idx_scan = 0
                    ORDER BY pg_relation_size(indexrelid) DESC
                """)
                
                unused = []
                for row in cur.fetchall():
                    unused.append({
                        'schema': row[0],
                        'table': row[1],
                        'index': row[2],
                        'size': row[3]
                    })
                
                return unused
    
    def get_index_bloat(self) -> List[Dict[str, Any]]:
        """获取索引膨胀信息"""
        with psycopg2.connect(self.conn_string) as conn:
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT 
                        schemaname,
                        tablename,
                        indexname,
                        pg_size_pretty(pg_relation_size(indexrelid)) as index_size,
                        pg_size_pretty(pg_relation_size(indexrelid) - pg_relation_size(indexrelid)) as bloat_size
                    FROM pg_stat_user_indexes
                    WHERE pg_relation_size(indexrelid) > 0
                    ORDER BY pg_relation_size(indexrelid) DESC
                """)
                
                bloat = []
                for row in cur.fetchall():
                    bloat.append({
                        'schema': row[0],
                        'table': row[1],
                        'index': row[2],
                        'size': row[3],
                        'bloat_size': row[4]
                    })
                
                return bloat
    
    def reindex_index(self, index_name: str) -> bool:
        """重建索引"""
        try:
            with psycopg2.connect(self.conn_string) as conn:
                with conn.cursor() as cur:
                    cur.execute(f"REINDEX INDEX CONCURRENTLY {index_name}")
                    conn.commit()
                    return True
        except Exception as e:
            print(f"Error reindexing {index_name}: {e}")
            return False
    
    def generate_report(self) -> Dict[str, Any]:
        """生成索引报告"""
        stats = self.get_index_statistics()
        unused = self.get_unused_indexes()
        bloat = self.get_index_bloat()
        
        return {
            'timestamp': datetime.now().isoformat(),
            'summary': {
                'total_indexes': len(stats['indexes']),
                'unused_indexes': len(unused),
                'bloated_indexes': len(bloat)
            },
            'statistics': stats,
            'unused_indexes': unused,
            'bloat_analysis': bloat,
            'recommendations': self.generate_recommendations(stats, unused, bloat)
        }
    
    def generate_recommendations(self, stats: Dict, unused: List, bloat: List) -> List[str]:
        """生成优化建议"""
        recommendations = []
        
        # 未使用索引建议
        if unused:
            recommendations.append(f"考虑删除 {len(unused)} 个未使用的索引以节省空间")
        
        # 膨胀索引建议
        if bloat:
            recommendations.append(f"考虑重建 {len(bloat)} 个膨胀的索引以提高性能")
        
        # 扫描次数少的索引建议
        low_usage = [idx for idx in stats['indexes'] if idx['scans'] < 10]
        if low_usage:
            recommendations.append(f"检查 {len(low_usage)} 个使用频率低的索引")
        
        return recommendations

# 使用示例
if __name__ == "__main__":
    monitor = IndexMonitor("postgresql://user:pass@localhost/dbname")
    
    # 生成报告
    report = monitor.generate_report()
    print(json.dumps(report, indent=2))
    
    # 重建特定索引
    success = monitor.reindex_index("idx_user_email")
    print(f"Reindex result: {success}")
```

## 验证规则

### 语法验证

```dsl
validation_rules "index_validation" {
  syntax: [
    {
      rule: "required_fields"
      fields: ["name", "table", "fields", "type"]
      message: "必须包含名称、表名、字段和类型"
    },
    {
      rule: "valid_index_type"
      allowed_types: ["btree", "hash", "gin", "gist", "spgist", "brin"]
      message: "索引类型必须是支持的类型"
    },
    {
      rule: "valid_field_reference"
      condition: "all fields exist in table"
      message: "所有字段必须在表中存在"
    }
  ]
  
  semantic: [
    {
      rule: "index_uniqueness"
      condition: "index names are unique within table"
      message: "索引名称在表内必须唯一"
    },
    {
      rule: "field_order_optimization"
      condition: "field order is optimal for query patterns"
      message: "字段顺序应该针对查询模式进行优化"
    }
  ]
}
```

### 性能验证

```dsl
performance_validation "index_performance" {
  constraints: [
    {
      metric: "index_size"
      threshold: "1GB"
      action: "warn"
    },
    {
      metric: "index_scan_ratio"
      threshold: 0.1
      action: "error"
    },
    {
      metric: "index_maintenance_time"
      threshold: "5m"
      action: "warn"
    }
  ]
  
  optimization: [
    {
      strategy: "index_consolidation"
      enabled: true
      target_reduction: 0.2
    },
    {
      strategy: "query_optimization"
      enabled: true
      target_improvement: 0.5
    }
  ]
}
```

## 最佳实践

### 设计模式

```dsl
best_practices "index_patterns" {
  patterns: [
    {
      name: "covering_index"
      description: "覆盖索引模式"
      implementation: {
        strategy: "include_all_columns"
        benefits: ["no_table_lookup", "faster_queries"]
        tradeoffs: ["larger_index", "slower_inserts"]
      }
    },
    {
      name: "partial_index"
      description: "部分索引模式"
      implementation: {
        strategy: "conditional_indexing"
        benefits: ["smaller_size", "faster_maintenance"]
        tradeoffs: ["limited_usage"]
      }
    },
    {
      name: "composite_index"
      description: "复合索引模式"
      implementation: {
        strategy: "multi_column_indexing"
        benefits: ["efficient_queries", "reduced_io"]
        tradeoffs: ["complex_ordering"]
      }
    }
  ]
  
  anti_patterns: [
    {
      name: "over_indexing"
      description: "过度索引"
      symptoms: ["slow_inserts", "large_storage", "maintenance_overhead"]
      solution: "consolidate_indexes"
    },
    {
      name: "under_indexing"
      description: "索引不足"
      symptoms: ["slow_queries", "table_scans", "poor_performance"]
      solution: "add_missing_indexes"
    }
  ]
}
```

### 监控和告警

```dsl
monitoring "index_monitoring" {
  metrics: [
    {
      name: "index_size_bytes"
      type: "gauge"
      labels: ["table_name", "index_name"]
      unit: "bytes"
    },
    {
      name: "index_scan_count"
      type: "counter"
      labels: ["table_name", "index_name"]
    },
    {
      name: "index_usage_ratio"
      type: "gauge"
      labels: ["table_name", "index_name"]
      range: [0, 1]
    }
  ]
  
  alerts: [
    {
      name: "index_size_growth"
      condition: "index_size_bytes > 1GB"
      severity: "warning"
      action: "review_index"
    },
    {
      name: "unused_index"
      condition: "index_usage_ratio < 0.01"
      severity: "info"
      action: "consider_removal"
    }
  ]
}
```

## 主流标准映射

### 数据库集成

```dsl
database_integration "postgresql_indexes" {
  database: {
    type: "postgresql"
    version: "14"
    connection: {
      host: "localhost"
      port: 5432
      database: "ecommerce"
      username: "${DB_USERNAME}"
      password: "${DB_PASSWORD}"
    }
  }
  
  index_types: [
    {
      name: "btree"
      description: "B-tree索引"
      use_cases: ["equality", "range", "sorting"]
      performance: "good"
    },
    {
      name: "hash"
      description: "哈希索引"
      use_cases: ["equality_only"]
      performance: "excellent"
    },
    {
      name: "gin"
      description: "GIN索引"
      use_cases: ["full_text", "arrays", "json"]
      performance: "good"
    },
    {
      name: "gist"
      description: "GiST索引"
      use_cases: ["spatial", "geometric"]
      performance: "good"
    }
  ]
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_schedule: "weekly"
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "index_size",
      "index_usage",
      "index_scans",
      "index_tuples_read"
    ]
  }
}
```

## 工程实践示例

### 电商索引模型

```dsl
ecommerce_index_model "complete_ecommerce" {
  description: "完整电商索引模型"
  
  namespace: "ecommerce"
  
  indexes: [
    {
      name: "idx_user_email"
      table: "users"
      fields: ["email"]
      type: "unique"
      properties: {
        method: "btree"
        fillfactor: 90
        concurrent: true
      }
    },
    {
      name: "idx_user_username"
      table: "users"
      fields: ["username"]
      type: "unique"
      properties: {
        method: "btree"
        fillfactor: 90
        concurrent: true
      }
    },
    {
      name: "idx_user_status"
      table: "users"
      fields: ["status", "created_at"]
      type: "btree"
      properties: {
        method: "btree"
        fillfactor: 85
        concurrent: true
      }
    },
    {
      name: "idx_product_sku"
      table: "products"
      fields: ["sku"]
      type: "unique"
      properties: {
        method: "btree"
        fillfactor: 90
        concurrent: true
      }
    },
    {
      name: "idx_product_category"
      table: "products"
      fields: ["category_id", "is_active", "price"]
      type: "btree"
      properties: {
        method: "btree"
        fillfactor: 85
        concurrent: true
      }
    },
    {
      name: "idx_product_search"
      table: "products"
      fields: ["to_tsvector('english', name || ' ' || description)"]
      type: "gin"
      properties: {
        method: "gin"
        language: "english"
      }
    },
    {
      name: "idx_order_customer"
      table: "orders"
      fields: ["customer_id", "status", "created_at"]
      type: "btree"
      properties: {
        method: "btree"
        fillfactor: 85
        concurrent: true
      }
    },
    {
      name: "idx_order_number"
      table: "orders"
      fields: ["order_number"]
      type: "unique"
      properties: {
        method: "btree"
        fillfactor: 90
        concurrent: true
      }
    },
    {
      name: "idx_order_status"
      table: "orders"
      fields: ["status", "payment_status", "created_at"]
      type: "btree"
      properties: {
        method: "btree"
        fillfactor: 85
        concurrent: true
      }
    },
    {
      name: "idx_order_item_order"
      table: "order_items"
      fields: ["order_id", "product_id"]
      type: "btree"
      properties: {
        method: "btree"
        fillfactor: 85
        concurrent: true
      }
    }
  ]
  
  partial_indexes: [
    {
      name: "idx_active_products"
      table: "products"
      fields: ["category_id", "price", "created_at"]
      condition: "is_active = true"
      type: "btree"
    },
    {
      name: "idx_paid_orders"
      table: "orders"
      fields: ["customer_id", "created_at"]
      condition: "payment_status = 'paid'"
      type: "btree"
    }
  ]
  
  function_indexes: [
    {
      name: "idx_user_email_domain"
      table: "users"
      fields: ["SUBSTRING(email FROM '@(.*)$')"]
      type: "btree"
    },
    {
      name: "idx_product_name_lower"
      table: "products"
      fields: ["LOWER(name)"]
      type: "btree"
    }
  ]
  
  maintenance: {
    auto_vacuum: true
    auto_analyze: true
    reindex_schedule: "weekly"
    vacuum_schedule: "daily"
  }
  
  monitoring: {
    enabled: true
    metrics: [
      "index_size",
      "index_usage",
      "index_scans",
      "index_tuples_read",
      "index_bloat"
    ]
    alerting: {
      on_index_size_growth: {
        threshold: "1GB"
        severity: "warning"
        notification: "slack"
      }
      on_unused_index: {
        threshold: 0.01
        severity: "info"
        notification: "email"
      }
      on_index_bloat: {
        threshold: 0.3
        severity: "warning"
        notification: "pagerduty"
      }
    }
  }
  
  optimization: {
    enabled: true
    strategies: [
      {
        name: "index_consolidation"
        target_reduction: 0.2
        frequency: "monthly"
      },
      {
        name: "query_optimization"
        target_improvement: 0.5
        frequency: "weekly"
      },
      {
        name: "index_cleanup"
        target_removal: 0.1
        frequency: "monthly"
      }
    ]
  }
}
```

这个DSL设计提供了完整的索引建模能力，支持多种索引类型、优化策略、性能调优、维护管理，并能够与主流数据库平台无缝集成。
