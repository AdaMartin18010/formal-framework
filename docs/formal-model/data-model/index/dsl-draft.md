# 索引建模DSL草案（完整版）

## 1. 设计目标

- 用统一DSL描述单列、多列、唯一、全文、空间、函数、部分、覆盖等索引要素，支持递归组合
- 支持自动生成SQL索引DDL、性能分析、优化建议、变更脚本、冗余检测等
- 支持权限、安全、审计、AI自动化、性能监控等高级特性
- 提供完整的索引类型系统、性能分析系统、优化建议系统支持

## 2. 基本语法结构

### 2.1 基础索引定义

```dsl
// 单列索引
index idx_user_email on User(email)
index idx_user_created_at on User(created_at)

// 多列索引
index idx_user_status_created on User(status, created_at)
index idx_order_customer_status on Order(customer_id, status, created_at)

// 唯一索引
unique index idx_user_email on User(email)
unique index idx_product_sku on Product(sku)

// 复合唯一索引
unique index idx_user_username_email on User(username, email)
```

### 2.2 高级索引类型

```dsl
// 全文搜索索引
fulltext index idx_post_content on Post(title, content)
fulltext index idx_product_search on Product(name, description, tags)

// 空间索引（地理位置）
spatial index idx_location_coords on Location(latitude, longitude)
spatial index idx_delivery_route on DeliveryRoute(path)

// 哈希索引
hash index idx_user_id_hash on User(id)
hash index idx_session_token on Session(token)

// 位图索引
bitmap index idx_user_active on User(is_active)
bitmap index idx_product_category on Product(category_id)
```

### 2.3 函数索引和表达式索引

```dsl
// 函数索引
index idx_user_email_domain on User(lower(email))
index idx_user_created_date on User(date(created_at))
index idx_user_created_month on User(year(created_at), month(created_at))

// 表达式索引
index idx_user_full_name on User(concat(first_name, ' ', last_name))
index idx_product_price_range on Product(
  case 
    when price < 10 then 'low'
    when price < 50 then 'medium'
    else 'high'
  end
)

// 条件索引
index idx_user_active_recent on User(created_at) where (is_active = true)
index idx_order_pending_recent on Order(created_at) where (status = 'pending')
```

## 3. 高级特性

### 3.1 部分索引和过滤索引

```dsl
// 部分索引（只索引满足条件的行）
index idx_user_active_email on User(email) where (is_active = true)
index idx_order_paid_amount on Order(total_amount) where (status = 'paid')
index idx_product_in_stock on Product(price) where (stock_quantity > 0)

// 复杂条件索引
index idx_user_premium_recent on User(created_at) 
  where (is_active = true and subscription_tier = 'premium')

index idx_order_high_value on Order(customer_id, created_at) 
  where (total_amount > 1000 and status in ('confirmed', 'shipped'))
```

### 3.2 覆盖索引和包含索引

```dsl
// 覆盖索引（包含查询所需的所有列）
index idx_user_profile on User(id, username, email, is_active)
index idx_order_summary on Order(id, customer_id, status, total_amount, created_at)

// 包含索引（PostgreSQL风格）
index idx_user_details on User(id) include (username, email, created_at)
index idx_order_info on Order(id) include (customer_id, status, total_amount)

// 复合覆盖索引
index idx_product_catalog on Product(category_id, is_active) 
  include (id, name, price, stock_quantity)
```

### 3.3 分区索引和全局索引

```dsl
// 分区表索引
entity Order {
  id: int primary key auto_increment
  customer_id: int references Customer(id)
  status: enum("pending", "confirmed", "shipped", "delivered", "cancelled")
  total_amount: decimal(10,2) not null
  created_at: datetime default now()
  
  // 分区配置
  partition by range (year(created_at)) {
    partition p2023 values less than (2024),
    partition p2024 values less than (2025),
    partition p2025 values less than (2026)
  }
  
  // 分区索引
  index idx_order_customer_partitioned on (customer_id, created_at) 
    partition by hash(customer_id)
  
  // 全局索引
  global index idx_order_status_global on (status, created_at)
}
```

### 3.4 索引选项和参数

```dsl
// 索引选项配置
index idx_user_email_optimized on User(email) {
  type: "btree"
  fillfactor: 90
  concurrent: true
  tablespace: "fast_storage"
  compression: "lz4"
}

// 全文索引选项
fulltext index idx_document_content on Document(content) {
  language: "english"
  stopwords: ["the", "a", "an", "and", "or"]
  stemmer: "porter"
  analyzer: "standard"
}

// 空间索引选项
spatial index idx_location_geo on Location(coordinates) {
  srid: 4326
  precision: "high"
  compression: "gzip"
}
```

## 4. 性能优化和监控

### 4.1 索引性能分析

```dsl
// 索引使用统计
index_usage_analysis {
  target: "User"
  period: "30d"
  
  statistics: {
    idx_user_email: {
      scans: 15420,
      tuples_returned: 15420,
      tuples_fetched: 15420,
      selectivity: 0.0001,
      avg_scan_time_ms: 0.5
    },
    idx_user_status_created: {
      scans: 8920,
      tuples_returned: 445600,
      tuples_fetched: 445600,
      selectivity: 0.05,
      avg_scan_time_ms: 2.1
    }
  }
  
  recommendations: [
    "idx_user_email is highly selective and well-utilized",
    "Consider adding covering index for user profile queries",
    "idx_user_status_created could benefit from partial index"
  ]
}
```

### 4.2 索引优化建议

```dsl
// AI驱动的索引优化
ai_index_optimization {
  target: "Order"
  analysis_period: "90d"
  
  query_patterns: [
    {
      pattern: "SELECT * FROM orders WHERE customer_id = ? AND status = ? ORDER BY created_at DESC",
      frequency: 1250,
      avg_execution_time_ms: 45.2,
      suggested_index: "idx_order_customer_status_created"
    },
    {
      pattern: "SELECT customer_id, COUNT(*) FROM orders WHERE created_at >= ? GROUP BY customer_id",
      frequency: 320,
      avg_execution_time_ms: 125.8,
      suggested_index: "idx_order_created_customer"
    }
  ]
  
  recommendations: [
    {
      action: "create_index",
      index: "idx_order_customer_status_created on Order(customer_id, status, created_at)",
      expected_improvement: "85%",
      priority: "high"
    },
    {
      action: "drop_index", 
      index: "idx_order_customer",
      reason: "redundant with new covering index",
      priority: "medium"
    }
  ]
}
```

### 4.3 索引维护和重建

```dsl
// 索引维护策略
index_maintenance {
  target: "User"
  
  maintenance_schedule: {
    analyze: "daily"
    vacuum: "weekly"
    reindex: "monthly"
  }
  
  auto_maintenance: {
    fragmentation_threshold: 30,  // 碎片率超过30%时重建
    bloat_threshold: 50,          // 膨胀率超过50%时重建
    auto_rebuild: true
  }
  
  monitoring: {
    fragmentation_monitor: true
    performance_monitor: true
    size_monitor: true
  }
}

// 索引重建策略
index_rebuild_strategy {
  target: "Order"
  
  rebuild_triggers: [
    "fragmentation > 40%",
    "performance_degradation > 50%",
    "size_increase > 200%"
  ]
  
  rebuild_method: "concurrent"  // 在线重建
  rebuild_window: "02:00-04:00" // 维护窗口
  rollback_plan: "keep_old_index_until_verification"
}
```

## 5. 索引安全和权限

### 5.1 索引权限控制

```dsl
// 索引级权限
index idx_sensitive_user_data on User(ssn, credit_score) {
  permission read: "admin"
  permission write: "admin"
  permission drop: "admin"
  
  audit: true
  audit_events: ["create", "drop", "rebuild"]
  
  encryption: "aes256"
  masking: "partial"
}
```

### 5.2 索引审计和监控

```dsl
// 索引审计配置
index_audit {
  target: "all"
  
  audit_events: [
    "index_creation",
    "index_drop", 
    "index_rebuild",
    "index_usage",
    "performance_degradation"
  ]
  
  retention_period: "2y"
  alert_thresholds: {
    performance_degradation: 50,
    size_increase: 200,
    fragmentation: 40
  }
}
```

## 6. 自动化生成和部署

### 6.1 索引DDL生成

```sql
-- 自动生成的索引DDL
CREATE INDEX CONCURRENTLY idx_user_email ON users(email);
CREATE INDEX CONCURRENTLY idx_user_status_created ON users(status, created_at);
CREATE UNIQUE INDEX CONCURRENTLY idx_user_username_email ON users(username, email);

-- 全文索引
CREATE INDEX idx_post_content_fts ON posts USING gin(to_tsvector('english', title || ' ' || content));

-- 部分索引
CREATE INDEX idx_user_active_email ON users(email) WHERE is_active = true;

-- 函数索引
CREATE INDEX idx_user_email_domain ON users(lower(email));
CREATE INDEX idx_user_created_date ON users(date(created_at));

-- 空间索引
CREATE INDEX idx_location_coords ON locations USING gist(coordinates);
```

### 6.2 索引变更脚本

```sql
-- 索引变更脚本
-- 添加新索引
CREATE INDEX CONCURRENTLY idx_order_customer_status_created 
ON orders(customer_id, status, created_at);

-- 删除冗余索引
DROP INDEX CONCURRENTLY idx_order_customer;

-- 重建索引
REINDEX INDEX CONCURRENTLY idx_user_email;

-- 更新统计信息
ANALYZE users;
ANALYZE orders;
```

### 6.3 索引部署策略

```dsl
// 索引部署配置
index_deployment {
  environment: "production"
  
  deployment_strategy: {
    method: "rolling"
    batch_size: 5
    health_check: true
    rollback_threshold: 5  // 5%性能下降时回滚
  }
  
  pre_deployment: [
    "backup_database",
    "analyze_query_patterns", 
    "estimate_index_size",
    "validate_disk_space"
  ]
  
  post_deployment: [
    "verify_index_creation",
    "update_statistics",
    "monitor_performance",
    "cleanup_old_indexes"
  ]
}
```

## 7. 索引最佳实践

### 7.1 索引设计原则

```dsl
// 索引设计指南
index_design_guidelines {
  principles: [
    "为WHERE子句中的列创建索引",
    "为ORDER BY子句中的列创建索引", 
    "为GROUP BY子句中的列创建索引",
    "为JOIN条件中的列创建索引",
    "避免为低基数列创建索引",
    "使用复合索引减少索引数量",
    "考虑查询的选择性",
    "监控索引使用情况"
  ]
  
  anti_patterns: [
    "为所有列创建索引",
    "创建过多的小索引",
    "忽略索引维护成本",
    "不考虑查询模式变化"
  ]
}
```

### 7.2 索引优化策略

```dsl
// 索引优化策略
index_optimization_strategy {
  target: "ecommerce_system"
  
  optimization_phases: [
    {
      phase: "analysis",
      activities: [
        "collect_query_statistics",
        "analyze_execution_plans", 
        "identify_missing_indexes",
        "detect_redundant_indexes"
      ]
    },
    {
      phase: "design",
      activities: [
        "design_covering_indexes",
        "optimize_composite_indexes",
        "plan_partial_indexes",
        "consider_functional_indexes"
      ]
    },
    {
      phase: "implementation",
      activities: [
        "create_indexes_concurrently",
        "monitor_performance_impact",
        "validate_improvements",
        "cleanup_old_indexes"
      ]
    }
  ]
}
```

## 8. 工程实践示例

### 8.1 电商系统索引设计

```dsl
// 电商系统完整索引设计
entity Product {
  id: int primary key auto_increment
  name: string not null max_length(200)
  sku: string unique not null
  category_id: int references Category(id)
  brand_id: int nullable references Brand(id)
  price: decimal(10,2) not null
  stock_quantity: int not null default(0)
  is_active: boolean default(true)
  created_at: datetime default now()
  
  // 基础索引
  index idx_product_sku on (sku)
  index idx_product_category on (category_id, is_active)
  index idx_product_brand on (brand_id, is_active)
  index idx_product_price on (price, is_active)
  
  // 复合索引
  index idx_product_category_price on (category_id, price, is_active)
  index idx_product_brand_price on (brand_id, price, is_active)
  
  // 部分索引
  index idx_product_in_stock on (category_id, price) where (stock_quantity > 0)
  index idx_product_active_recent on (created_at) where (is_active = true)
  
  // 全文搜索索引
  fulltext index idx_product_search on (name, description, tags)
  
  // 覆盖索引
  index idx_product_catalog on (category_id, is_active) 
    include (id, name, price, stock_quantity)
}

entity Order {
  id: int primary key auto_increment
  customer_id: int references Customer(id)
  order_number: string unique not null
  status: enum("pending", "confirmed", "shipped", "delivered", "cancelled")
  total_amount: decimal(10,2) not null
  created_at: datetime default now()
  
  // 基础索引
  index idx_order_customer on (customer_id, created_at)
  index idx_order_status on (status, created_at)
  index idx_order_number on (order_number)
  
  // 复合索引
  index idx_order_customer_status on (customer_id, status, created_at)
  index idx_order_status_amount on (status, total_amount, created_at)
  
  // 部分索引
  index idx_order_pending_recent on (customer_id, created_at) 
    where (status = 'pending')
  index idx_order_high_value on (customer_id, created_at) 
    where (total_amount > 1000)
  
  // 覆盖索引
  index idx_order_summary on (customer_id, status, created_at) 
    include (id, order_number, total_amount)
}
```

### 8.2 社交媒体系统索引设计

```dsl
// 社交媒体系统索引设计
entity Post {
  id: int primary key auto_increment
  user_id: int references User(id)
  content: text not null
  visibility: enum("public", "friends", "private")
  created_at: datetime default now()
  updated_at: datetime default now() on_update(now())
  
  // 基础索引
  index idx_post_user on (user_id, created_at)
  index idx_post_visibility on (visibility, created_at)
  
  // 复合索引
  index idx_post_user_visibility on (user_id, visibility, created_at)
  
  // 部分索引
  index idx_post_public_recent on (created_at) where (visibility = 'public')
  index idx_post_user_public on (user_id, created_at) where (visibility = 'public')
  
  // 全文搜索索引
  fulltext index idx_post_content on (content)
  
  // 函数索引
  index idx_post_created_date on (date(created_at))
  index idx_post_created_month on (year(created_at), month(created_at))
}

entity Comment {
  id: int primary key auto_increment
  post_id: int references Post(id) on_delete(cascade)
  user_id: int references User(id)
  content: text not null
  parent_id: int nullable references Comment(id)
  created_at: datetime default now()
  
  // 基础索引
  index idx_comment_post on (post_id, created_at)
  index idx_comment_user on (user_id, created_at)
  index idx_comment_parent on (parent_id, created_at)
  
  // 复合索引
  index idx_comment_post_user on (post_id, user_id, created_at)
  
  // 部分索引
  index idx_comment_recent on (post_id, created_at) where (parent_id is null)
  
  // 全文搜索索引
  fulltext index idx_comment_content on (content)
}
```

## 9. 监控和告警

### 9.1 索引性能监控

```dsl
// 索引性能监控配置
index_monitoring {
  targets: ["all"]
  
  metrics: [
    "index_scan_count",
    "index_tuples_returned", 
    "index_tuples_fetched",
    "index_scan_time",
    "index_size",
    "index_fragmentation",
    "index_bloat"
  ]
  
  thresholds: {
    scan_time_ms: 100,
    fragmentation_percent: 30,
    bloat_percent: 50,
    size_growth_percent: 200
  }
  
  alerts: [
    {
      condition: "scan_time > threshold",
      action: "notify_dba",
      severity: "warning"
    },
    {
      condition: "fragmentation > threshold", 
      action: "schedule_rebuild",
      severity: "critical"
    }
  ]
}
```

### 9.2 索引健康检查

```dsl
// 索引健康检查
index_health_check {
  schedule: "daily"
  
  checks: [
    {
      name: "unused_indexes",
      query: "SELECT indexname FROM pg_stat_user_indexes WHERE idx_scan = 0",
      threshold: 10,
      action: "review_for_removal"
    },
    {
      name: "duplicate_indexes", 
      query: "SELECT duplicate_indexes()",
      threshold: 0,
      action: "remove_duplicates"
    },
    {
      name: "missing_indexes",
      query: "SELECT slow_queries_without_indexes()", 
      threshold: 5,
      action: "analyze_and_create"
    }
  ]
  
  reports: [
    "index_usage_summary",
    "performance_impact_analysis",
    "storage_usage_report",
    "optimization_recommendations"
  ]
}
```

## 10. 总结

本DSL为索引建模提供了完整的形式化描述框架，支持：

- **完整的索引类型系统**：B-tree、Hash、GiST、GIN、BRIN等
- **丰富的索引特性**：唯一索引、复合索引、部分索引、覆盖索引、函数索引
- **强大的性能分析**：使用统计、性能监控、优化建议
- **完善的维护系统**：自动重建、碎片整理、统计更新
- **全面的安全控制**：权限管理、审计日志、加密保护
- **智能的自动化**：AI优化建议、自动部署、健康检查
- **标准的映射支持**：SQL DDL、监控脚本、部署工具

通过这个DSL，可以实现索引的统一描述、自动化管理、性能优化和持续监控，为数据库性能提供强大的索引管理基础。
