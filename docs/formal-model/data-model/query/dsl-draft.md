# 查询建模DSL草案（完整版）

## 1. 设计目标

- 用统一DSL描述SQL、NoSQL、GraphQL等查询要素，支持递归嵌套、复杂组合
- 支持自动生成SQL语句、NoSQL查询、GraphQL请求等，便于多数据源集成
- 支持权限、审计、安全、AI自动化、性能优化等高级特性
- 提供完整的查询类型系统、优化系统、安全系统支持

## 2. 基本语法结构

### 2.1 基础查询定义

```dsl
// 简单查询
query GetUserById {
  select: [id, name, email, created_at]
  from: User
  where: { id = $id }
  limit: 1
}

// 列表查询
query ListOrders {
  select: [id, user_id, product_id, quantity, total_amount, status, created_at]
  from: Order
  where: { 
    and: [
      { status in ["pending", "confirmed"] },
      { created_at >= $start_date },
      { created_at <= $end_date }
    ]
  }
  order_by: [created_at desc]
  limit: 50
  offset: $offset
}

// 聚合查询
query UserStats {
  select: [
    count(*) as total_users,
    avg(age) as avg_age,
    max(created_at) as latest_user,
    sum(case when status = 'active' then 1 else 0 end) as active_users
  ]
  from: User
  where: { age >= 18 }
  group_by: []
}

// 分组查询
query SalesByCategory {
  select: [
    category_id,
    category_name,
    count(*) as order_count,
    sum(total_amount) as total_sales,
    avg(total_amount) as avg_order_value
  ]
  from: Order
  join: {
    Product: { on: "Order.product_id = Product.id" }
  }
  where: { 
    and: [
      { status = "completed" },
      { created_at >= $start_date }
    ]
  }
  group_by: [category_id, category_name]
  having: { total_sales > 10000 }
  order_by: [total_sales desc]
}
```

### 2.2 复杂查询结构

```dsl
// 多表连接查询
query OrdersWithUserAndProduct {
  select: [
    Order.id,
    Order.total_amount,
    Order.status,
    Order.created_at,
    User.name as user_name,
    User.email as user_email,
    Product.name as product_name,
    Product.price as product_price
  ]
  from: Order
  join: {
    User: { 
      type: "inner",
      on: "Order.user_id = User.id"
    },
    Product: { 
      type: "left",
      on: "Order.product_id = Product.id"
    }
  }
  where: { 
    and: [
      { Order.status in ["pending", "confirmed", "shipped"] },
      { Order.total_amount >= $min_amount },
      { User.status = "active" }
    ]
  }
  order_by: [Order.created_at desc]
  limit: 100
}

// 子查询
query HighValueCustomers {
  select: [
    User.id,
    User.name,
    User.email,
    User.total_orders,
    User.total_spent
  ]
  from: User
  where: { 
    User.total_spent > (
      select: avg(total_spent)
      from: User
      where: { status = "active" }
    )
  }
  order_by: [User.total_spent desc]
  limit: 20
}

// 窗口函数查询
query UserRanking {
  select: [
    User.id,
    User.name,
    User.total_spent,
    rank() over (order by User.total_spent desc) as spending_rank,
    dense_rank() over (order by User.total_spent desc) as dense_rank,
    lag(User.total_spent, 1) over (order by User.total_spent desc) as prev_spending,
    lead(User.total_spent, 1) over (order by User.total_spent desc) as next_spending
  ]
  from: User
  where: { status = "active" }
  order_by: [User.total_spent desc]
}
```

### 2.3 递归查询

```dsl
// 递归查询 - 组织架构
query OrganizationHierarchy {
  select: [
    Employee.id,
    Employee.name,
    Employee.position,
    Employee.level,
    Employee.manager_id
  ]
  from: Employee
  where: { department_id = $dept_id }
  recursive: {
    cte: "OrgTree",
    anchor: {
      select: [id, name, position, 1 as level, manager_id]
      from: Employee
      where: { manager_id is null }
    },
    recursive: {
      select: [
        e.id,
        e.name,
        e.position,
        ot.level + 1,
        e.manager_id
      ]
      from: Employee e
      join: {
        OrgTree ot: { on: "e.manager_id = ot.id" }
      }
    }
  }
  order_by: [level, name]
}

// 递归查询 - 评论树
query CommentTree {
  select: [
    Comment.id,
    Comment.content,
    Comment.author_id,
    Comment.parent_id,
    Comment.created_at,
    Comment.level
  ]
  from: Comment
  where: { post_id = $post_id }
  recursive: {
    cte: "CommentTree",
    anchor: {
      select: [id, content, author_id, parent_id, created_at, 0 as level]
      from: Comment
      where: { parent_id is null and post_id = $post_id }
    },
    recursive: {
      select: [
        c.id,
        c.content,
        c.author_id,
        c.parent_id,
        c.created_at,
        ct.level + 1
      ]
      from: Comment c
      join: {
        CommentTree ct: { on: "c.parent_id = ct.id" }
      }
    }
  }
  order_by: [level, created_at]
}
```

## 3. 高级特性

### 3.1 动态查询构建

```dsl
// 动态查询构建
query DynamicUserSearch {
  select: [id, name, email, status, created_at]
  from: User
  where: {
    dynamic: {
      conditions: [
        { field: "name", operator: "like", value: "$name_pattern", enabled: "$search_name" },
        { field: "email", operator: "like", value: "$email_pattern", enabled: "$search_email" },
        { field: "status", operator: "=", value: "$status", enabled: "$filter_status" },
        { field: "age", operator: ">=", value: "$min_age", enabled: "$filter_age" },
        { field: "created_at", operator: ">=", value: "$start_date", enabled: "$filter_date" }
      ],
      logic: "and"
    }
  }
  order_by: {
    dynamic: {
      fields: [
        { field: "created_at", direction: "desc", enabled: "$sort_by_date" },
        { field: "name", direction: "asc", enabled: "$sort_by_name" },
        { field: "total_spent", direction: "desc", enabled: "$sort_by_spending" }
      ],
      default: { field: "created_at", direction: "desc" }
    }
  }
  limit: $limit
  offset: $offset
}
```

### 3.2 查询模板和参数化

```dsl
// 查询模板
template SalesReport {
  parameters: {
    start_date: "date",
    end_date: "date",
    category_id: "int?",
    user_id: "int?",
    group_by: "string[]",
    order_by: "string[]"
  }
  
  query: {
    select: [
      $group_by,
      count(*) as order_count,
      sum(total_amount) as total_sales,
      avg(total_amount) as avg_order_value
    ]
    from: Order
    join: {
      Product: { on: "Order.product_id = Product.id" },
      User: { on: "Order.user_id = User.id" }
    }
    where: {
      and: [
        { Order.created_at >= $start_date },
        { Order.created_at <= $end_date },
        { Order.status = "completed" },
        { Product.category_id = $category_id, enabled: "$category_id" },
        { Order.user_id = $user_id, enabled: "$user_id" }
      ]
    }
    group_by: $group_by
    order_by: $order_by
  }
}

// 使用模板
query MonthlySalesReport {
  use: SalesReport
  parameters: {
    start_date: "2024-01-01",
    end_date: "2024-01-31",
    group_by: ["Product.category_id", "Product.category_name"],
    order_by: ["total_sales desc"]
  }
}
```

### 3.3 查询优化和性能

```dsl
// 查询优化配置
query OptimizedUserSearch {
  select: [id, name, email, status]
  from: User
  where: { 
    and: [
      { status = "active" },
      { created_at >= $start_date }
    ]
  }
  order_by: [created_at desc]
  limit: 100
  
  // 优化提示
  optimization: {
    use_index: ["idx_user_status_created", "idx_user_email"],
    force_index: false,
    cache: true,
    cache_ttl: 300,  // 5分钟
    parallel: true,
    max_parallel_workers: 4
  }
  
  // 性能监控
  monitoring: {
    track_performance: true,
    alert_threshold_ms: 1000,
    log_slow_queries: true,
    collect_execution_plan: true
  }
}
```

### 3.4 查询安全和权限

```dsl
// 安全查询
query SecureUserData {
  select: [
    id,
    name,
    email,
    status,
    created_at
  ]
  from: User
  where: { 
    and: [
      { id = $user_id },
      { status = "active" }
    ]
  }
  
  // 权限控制
  security: {
    permission: "user_read_own_data",
    row_level_security: true,
    data_masking: {
      email: "partial",  // 显示前3位和后2位
      phone: "full"      // 完全隐藏
    },
    audit: true,
    audit_fields: ["id", "email", "status"]
  }
  
  // 参数验证
  validation: {
    user_id: {
      type: "int",
      required: true,
      range: [1, 999999],
      sanitize: true
    }
  }
}
```

## 4. 多数据源查询

### 4.1 SQL数据库查询

```dsl
// PostgreSQL查询
query PostgresUserQuery {
  data_source: "postgres_main"
  select: [id, name, email, created_at]
  from: users
  where: { status = "active" }
  order_by: [created_at desc]
  limit: 100
}

// MySQL查询
query MySQLOrderQuery {
  data_source: "mysql_orders"
  select: [
    o.id,
    o.user_id,
    o.total_amount,
    o.status,
    o.created_at,
    u.name as user_name
  ]
  from: orders o
  join: {
    users u: { on: "o.user_id = u.id" }
  }
  where: { o.status = "completed" }
  order_by: [o.created_at desc]
}
```

### 4.2 NoSQL查询

```dsl
// MongoDB查询
query MongoUserQuery {
  data_source: "mongodb_users"
  collection: "users"
  find: {
    status: "active",
    created_at: { $gte: "$start_date" }
  }
  project: {
    id: 1,
    name: 1,
    email: 1,
    created_at: 1
  }
  sort: { created_at: -1 }
  limit: 100
}

// Elasticsearch查询
query ElasticProductSearch {
  data_source: "elasticsearch_products"
  index: "products"
  query: {
    bool: {
      must: [
        { match: { name: "$search_term" } },
        { range: { price: { gte: "$min_price", lte: "$max_price" } } }
      ],
      filter: [
        { term: { category_id: "$category_id" } },
        { term: { status: "active" } }
      ]
    }
  }
  sort: [
    { price: { order: "asc" } },
    { _score: { order: "desc" } }
  ]
  size: 50
}
```

### 4.3 GraphQL查询

```dsl
// GraphQL查询
query GraphQLUserOrders {
  data_source: "graphql_api"
  query: """
    query GetUserOrders($userId: ID!) {
      user(id: $userId) {
        id
        name
        email
        orders {
          id
          totalAmount
          status
          createdAt
          products {
            id
            name
            price
          }
        }
      }
    }
  """
  variables: {
    userId: "$user_id"
  }
}
```

## 5. 自动化生成示例

### 5.1 查询生成器

```python
# 动态查询生成器
class QueryGenerator:
    def __init__(self, data_source):
        self.data_source = data_source
        self.query_templates = self.load_query_templates()
    
    def generate_select_query(self, table, fields, conditions=None, order_by=None, limit=None):
        """生成SELECT查询"""
        
        query = {
            "select": fields,
            "from": table,
            "data_source": self.data_source
        }
        
        if conditions:
            query["where"] = self.build_where_clause(conditions)
        
        if order_by:
            query["order_by"] = order_by
        
        if limit:
            query["limit"] = limit
        
        return query
    
    def build_where_clause(self, conditions):
        """构建WHERE子句"""
        
        if len(conditions) == 1:
            return conditions[0]
        
        return {
            "and": conditions
        }
    
    def generate_join_query(self, main_table, joins, fields, conditions=None):
        """生成JOIN查询"""
        
        query = {
            "select": fields,
            "from": main_table,
            "join": joins,
            "data_source": self.data_source
        }
        
        if conditions:
            query["where"] = self.build_where_clause(conditions)
        
        return query
    
    def generate_aggregate_query(self, table, aggregations, group_by=None, having=None):
        """生成聚合查询"""
        
        query = {
            "select": aggregations,
            "from": table,
            "data_source": self.data_source
        }
        
        if group_by:
            query["group_by"] = group_by
        
        if having:
            query["having"] = having
        
        return query

# 使用示例
generator = QueryGenerator("postgres_main")

# 生成简单查询
simple_query = generator.generate_select_query(
    table="users",
    fields=["id", "name", "email"],
    conditions=[{"status": "active"}],
    order_by=["created_at desc"],
    limit=100
)

# 生成JOIN查询
join_query = generator.generate_join_query(
    main_table="orders",
    joins={
        "users": {"on": "orders.user_id = users.id"}
    },
    fields=["orders.id", "orders.total_amount", "users.name"],
    conditions=[{"orders.status": "completed"}]
)
```

### 5.2 查询优化器

```python
# 查询优化器
class QueryOptimizer:
    def __init__(self, database_schema):
        self.schema = database_schema
        self.indexes = self.load_indexes()
    
    def optimize_query(self, query):
        """优化查询"""
        
        optimized_query = query.copy()
        
        # 分析查询计划
        execution_plan = self.analyze_execution_plan(query)
        
        # 添加索引提示
        if execution_plan.get('full_table_scan'):
            suggested_indexes = self.suggest_indexes(query)
            optimized_query['optimization'] = {
                'use_index': suggested_indexes,
                'force_index': False
            }
        
        # 优化JOIN顺序
        if 'join' in query:
            optimized_query['join'] = self.optimize_join_order(query['join'])
        
        # 添加查询提示
        optimized_query['hints'] = self.generate_query_hints(query)
        
        return optimized_query
    
    def analyze_execution_plan(self, query):
        """分析执行计划"""
        
        # 模拟执行计划分析
        plan = {
            'estimated_cost': 1000,
            'full_table_scan': False,
            'index_usage': [],
            'join_strategy': 'nested_loop'
        }
        
        # 检查是否使用索引
        if 'where' in query:
            used_indexes = self.find_used_indexes(query['where'])
            plan['index_usage'] = used_indexes
            
            if not used_indexes:
                plan['full_table_scan'] = True
        
        return plan
    
    def suggest_indexes(self, query):
        """建议索引"""
        
        suggested = []
        
        if 'where' in query:
            # 分析WHERE子句中的字段
            fields = self.extract_fields_from_where(query['where'])
            
            for field in fields:
                if not self.has_index(field):
                    suggested.append(f"idx_{field['table']}_{field['column']}")
        
        return suggested
    
    def optimize_join_order(self, joins):
        """优化JOIN顺序"""
        
        # 基于表大小和索引情况优化JOIN顺序
        optimized_joins = {}
        
        # 按表大小排序（小表在前）
        sorted_joins = sorted(joins.items(), key=lambda x: self.get_table_size(x[0]))
        
        for table, join_condition in sorted_joins:
            optimized_joins[table] = join_condition
        
        return optimized_joins
    
    def generate_query_hints(self, query):
        """生成查询提示"""
        
        hints = []
        
        if 'limit' in query and query['limit'] < 100:
            hints.append("Use index for LIMIT queries")
        
        if 'order_by' in query:
            hints.append("Consider covering index for ORDER BY")
        
        if 'group_by' in query:
            hints.append("Use index for GROUP BY operations")
        
        return hints

# 使用示例
optimizer = QueryOptimizer(database_schema)

# 优化查询
original_query = {
    "select": ["id", "name", "email"],
    "from": "users",
    "where": {"status": "active"},
    "order_by": ["created_at desc"],
    "limit": 100
}

optimized_query = optimizer.optimize_query(original_query)
```

### 5.3 查询安全验证器

```python
# 查询安全验证器
class QuerySecurityValidator:
    def __init__(self, security_policies):
        self.policies = security_policies
    
    def validate_query(self, query, user_context):
        """验证查询安全性"""
        
        validation_result = {
            'valid': True,
            'errors': [],
            'warnings': [],
            'suggestions': []
        }
        
        # 检查SQL注入
        sql_injection_risk = self.check_sql_injection(query)
        if sql_injection_risk:
            validation_result['valid'] = False
            validation_result['errors'].append(f"SQL injection risk: {sql_injection_risk}")
        
        # 检查权限
        permission_check = self.check_permissions(query, user_context)
        if not permission_check['allowed']:
            validation_result['valid'] = False
            validation_result['errors'].append(f"Permission denied: {permission_check['reason']}")
        
        # 检查数据访问范围
        scope_check = self.check_data_scope(query, user_context)
        if not scope_check['valid']:
            validation_result['warnings'].append(f"Data scope warning: {scope_check['message']}")
        
        # 检查性能风险
        performance_risk = self.check_performance_risk(query)
        if performance_risk:
            validation_result['warnings'].append(f"Performance risk: {performance_risk}")
        
        return validation_result
    
    def check_sql_injection(self, query):
        """检查SQL注入风险"""
        
        # 检查参数化查询
        if 'parameters' not in query:
            return "Query should use parameterized statements"
        
        # 检查动态SQL构建
        if 'dynamic' in query.get('where', {}):
            return "Dynamic SQL construction detected"
        
        return None
    
    def check_permissions(self, query, user_context):
        """检查用户权限"""
        
        required_permission = query.get('security', {}).get('permission')
        if not required_permission:
            return {'allowed': True}
        
        user_permissions = user_context.get('permissions', [])
        
        if required_permission not in user_permissions:
            return {
                'allowed': False,
                'reason': f"User lacks permission: {required_permission}"
            }
        
        return {'allowed': True}
    
    def check_data_scope(self, query, user_context):
        """检查数据访问范围"""
        
        # 检查行级安全
        if query.get('security', {}).get('row_level_security'):
            user_id = user_context.get('user_id')
            if not user_id:
                return {
                    'valid': False,
                    'message': "Row-level security requires user_id"
                }
        
        return {'valid': True}
    
    def check_performance_risk(self, query):
        """检查性能风险"""
        
        # 检查无限制查询
        if 'limit' not in query and 'where' not in query:
            return "Query without LIMIT or WHERE clause"
        
        # 检查大表查询
        if 'from' in query and self.is_large_table(query['from']):
            return f"Querying large table: {query['from']}"
        
        return None

# 使用示例
validator = QuerySecurityValidator(security_policies)

# 验证查询
query_to_validate = {
    "select": ["id", "name", "email"],
    "from": "users",
    "where": {"status": "active"},
    "security": {
        "permission": "user_read",
        "row_level_security": True
    },
    "parameters": {
        "user_id": 123
    }
}

user_context = {
    "user_id": 123,
    "permissions": ["user_read", "user_write"]
}

validation_result = validator.validate_query(query_to_validate, user_context)
```

## 6. 验证和测试

### 6.1 DSL验证器

```python
class QueryDSLValidator:
    def validate_query(self, query):
        """验证查询DSL"""
        errors = []
        
        # 检查必需字段
        if 'select' not in query:
            errors.append("Query must have 'select' clause")
        
        if 'from' not in query:
            errors.append("Query must have 'from' clause")
        
        # 检查字段格式
        if 'select' in query:
            select_errors = self.validate_select_clause(query['select'])
            errors.extend(select_errors)
        
        # 检查WHERE子句
        if 'where' in query:
            where_errors = self.validate_where_clause(query['where'])
            errors.extend(where_errors)
        
        # 检查JOIN子句
        if 'join' in query:
            join_errors = self.validate_join_clause(query['join'])
            errors.extend(join_errors)
        
        return errors
    
    def validate_select_clause(self, select):
        """验证SELECT子句"""
        errors = []
        
        if not isinstance(select, list):
            errors.append("SELECT clause must be a list")
            return errors
        
        for field in select:
            if isinstance(field, str):
                # 简单字段
                if not field.strip():
                    errors.append("Empty field in SELECT clause")
            elif isinstance(field, dict):
                # 别名字段
                if 'as' not in field:
                    errors.append("Alias field must have 'as' keyword")
        
        return errors
    
    def validate_where_clause(self, where):
        """验证WHERE子句"""
        errors = []
        
        if isinstance(where, dict):
            # 检查逻辑操作符
            logical_operators = ['and', 'or', 'not']
            for key in where.keys():
                if key in logical_operators:
                    if not isinstance(where[key], list):
                        errors.append(f"{key} operator must have a list of conditions")
                else:
                    # 检查条件格式
                    if not self.is_valid_condition(where[key]):
                        errors.append(f"Invalid condition format: {key}")
        
        return errors
    
    def validate_join_clause(self, join):
        """验证JOIN子句"""
        errors = []
        
        if not isinstance(join, dict):
            errors.append("JOIN clause must be a dictionary")
            return errors
        
        for table, join_condition in join.items():
            if not isinstance(join_condition, dict):
                errors.append(f"Join condition for {table} must be a dictionary")
                continue
            
            if 'on' not in join_condition:
                errors.append(f"Join condition for {table} must have 'on' clause")
        
        return errors
    
    def is_valid_condition(self, condition):
        """检查条件格式是否有效"""
        if isinstance(condition, (str, int, float, bool)):
            return True
        
        if isinstance(condition, dict):
            # 检查操作符
            operators = ['=', '!=', '>', '<', '>=', '<=', 'in', 'like', 'is']
            for key in condition.keys():
                if key not in operators:
                    return False
        
        return True
```

### 6.2 性能测试

```python
class QueryPerformanceTest:
    def test_query_performance(self, query, expected_time_ms=1000):
        """测试查询性能"""
        import time
        
        # 执行查询
        start_time = time.time()
        result = execute_query(query)
        end_time = time.time()
        
        execution_time_ms = (end_time - start_time) * 1000
        
        # 性能断言
        assert execution_time_ms < expected_time_ms, \
            f"Query took {execution_time_ms}ms, expected < {expected_time_ms}ms"
        
        # 检查结果
        assert result is not None, "Query should return results"
        
        return {
            'execution_time_ms': execution_time_ms,
            'result_count': len(result) if result else 0,
            'performance_rating': self.calculate_performance_rating(execution_time_ms)
        }
    
    def test_query_optimization(self, original_query, optimized_query):
        """测试查询优化效果"""
        
        # 测试原始查询
        original_performance = self.test_query_performance(original_query)
        
        # 测试优化查询
        optimized_performance = self.test_query_performance(optimized_query)
        
        # 计算改进
        improvement = (original_performance['execution_time_ms'] - 
                      optimized_performance['execution_time_ms']) / \
                      original_performance['execution_time_ms'] * 100
        
        # 断言改进
        assert improvement > 0, f"Optimization should improve performance, got {improvement}%"
        
        return {
            'original_time': original_performance['execution_time_ms'],
            'optimized_time': optimized_performance['execution_time_ms'],
            'improvement_percent': improvement
        }
    
    def calculate_performance_rating(self, execution_time_ms):
        """计算性能评级"""
        if execution_time_ms < 100:
            return "excellent"
        elif execution_time_ms < 500:
            return "good"
        elif execution_time_ms < 1000:
            return "acceptable"
        else:
            return "poor"
```

## 7. 总结

本DSL为查询建模提供了完整的形式化描述框架，支持：

- **完整的查询类型系统**：SELECT、JOIN、聚合、窗口函数、递归查询
- **丰富的查询特性**：动态查询、查询模板、参数化查询、查询优化
- **强大的安全控制**：权限验证、SQL注入防护、数据脱敏、审计日志
- **多数据源支持**：SQL、NoSQL、GraphQL、Elasticsearch等
- **智能的自动化**：查询生成、查询优化、性能监控、安全验证
- **标准的映射支持**：SQL生成、NoSQL转换、GraphQL转换

通过这个DSL，可以实现查询的统一描述、自动化生成、性能优化和安全控制，为数据访问提供强大的查询管理基础。
