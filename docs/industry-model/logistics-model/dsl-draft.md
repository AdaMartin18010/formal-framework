# 物流模型DSL草案（完整版）

## 1. 概述

物流模型DSL用于统一描述智能物流系统：仓储管理、运输调度、配送优化、供应链可视化、成本控制、智能预测等，支持与WMS、TMS、OMS、ERP、IoT设备、AI算法等系统对接。

## 2. 核心语法定义

### 2.1 仓储管理系统

```yaml
warehouse_management:
  warehouses:
    - id: "wh_001"
      name: "上海主仓"
      type: "distribution_center"
      location: [121.4737, 31.2304]
      capacity_m3: 50000
      operating_hours: ["08:00", "22:00"]
      
      # 仓库分区
      zones:
        - name: "A区"
          type: "fast_moving"
          rack_type: "narrow_aisle"
          capacity_m3: 15000
          temperature_range: [15, 25]
          humidity_range: [40, 60]
          
        - name: "B区"
          type: "slow_moving"
          rack_type: "wide_aisle"
          capacity_m3: 20000
          temperature_range: [10, 30]
          
        - name: "C区"
          type: "bulk"
          rack_type: "floor_storage"
          capacity_m3: 10000
          temperature_range: [5, 35]
          
        - name: "D区"
          type: "cold_storage"
          rack_type: "refrigerated"
          capacity_m3: 5000
          temperature_range: [-20, -5]
      
      # 设备配置
      equipment:
        - type: "forklift"
          count: 8
          capacity_kg: 2000
          fuel_type: "electric"
          maintenance_schedule: "weekly"
          
        - type: "conveyor"
          length_m: 200
          speed_mps: 0.5
          capacity_kg_per_hour: 5000
          
        - type: "asrs"
          aisles: 4
          levels: 12
          positions: 480
          throughput_per_hour: 200
          
        - type: "agv"
          count: 5
          capacity_kg: 500
          navigation: "laser_guided"
          
        - type: "picking_robot"
          count: 3
          accuracy: 0.999
          speed_picks_per_hour: 300
      
      # 安全配置
      safety:
        fire_suppression: "sprinkler_system"
        emergency_exits: 8
        evacuation_plan: "standard"
        security_cameras: 24
        access_control: "card_based"
        
      # 环境监控
      environmental_monitoring:
        temperature_sensors: 12
        humidity_sensors: 8
        air_quality_sensors: 4
        alert_thresholds:
          temperature_high: 30
          temperature_low: 5
          humidity_high: 80
          humidity_low: 30
```

### 2.2 库存管理系统

```yaml
inventory_management:
  skus:
    - sku: "SKU-001"
      name: "商品A"
      category: "electronics"
      dimensions: [30, 20, 15]  # cm
      weight_kg: 2.5
      volume_m3: 0.009
      storage_type: "rack"
      abc_class: "A"
      
      # 库存策略
      inventory_policy:
        min_stock: 100
        max_stock: 1000
        reorder_point: 150
        reorder_quantity: 500
        lead_time_days: 7
        safety_stock: 50
        
      # 存储要求
      storage_requirements:
        temperature_range: [15, 25]
        humidity_range: [40, 60]
        light_sensitive: false
        fragile: false
        hazardous: false
        
      # 包装信息
      packaging:
        unit_package: "box"
        unit_dimensions: [30, 20, 15]
        unit_weight: 2.5
        units_per_case: 12
        case_dimensions: [60, 40, 30]
        case_weight: 30
        
      # 供应商信息
      suppliers:
        - supplier_id: "SUP-001"
          name: "供应商A"
          lead_time_days: 7
          reliability_pct: 95
          cost_per_unit: 10.5
          
    - sku: "SKU-002"
      name: "商品B"
      category: "clothing"
      dimensions: [25, 15, 5]
      weight_kg: 0.8
      volume_m3: 0.001875
      storage_type: "hanging"
      abc_class: "B"
      
      inventory_policy:
        min_stock: 50
        max_stock: 500
        reorder_point: 75
        reorder_quantity: 200
        lead_time_days: 14
        safety_stock: 25
```

### 2.3 运输调度系统

```yaml
transportation_scheduling:
  vehicles:
    - id: "truck_001"
      type: "box_truck"
      capacity_m3: 30
      capacity_kg: 5000
      dimensions: [6, 2.5, 2.5]  # m
      fuel_type: "diesel"
      fuel_efficiency_km_per_l: 8
      max_speed_km_per_h: 80
      
      # 司机信息
      driver: "driver_001"
      driver_license: "A2"
      experience_years: 5
      
      # 可用性
      availability: ["Mon", "Tue", "Wed", "Thu", "Fri"]
      operating_hours: ["08:00", "18:00"]
      max_daily_hours: 10
      rest_requirements: "11_hours_between_shifts"
      
      # 维护信息
      maintenance:
        last_service: "2024-01-15"
        next_service: "2024-02-15"
        service_interval_km: 10000
        current_mileage_km: 85000
        
    - id: "van_001"
      type: "delivery_van"
      capacity_m3: 15
      capacity_kg: 2000
      dimensions: [4, 2, 2]
      fuel_type: "electric"
      battery_capacity_kwh: 75
      range_km: 300
      
      driver: "driver_002"
      availability: ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
      operating_hours: ["09:00", "19:00"]
      
  routes:
    - id: "route_001"
      name: "上海-南京-苏州"
      vehicle: "truck_001"
      driver: "driver_001"
      distance_km: 450
      estimated_time_h: 6
      fuel_cost: 225  # 假设柴油价格5元/升
      
      # 停靠点
      stops:
        - location: "上海仓库"
          type: "pickup"
          time: "09:00"
          duration_min: 60
          coordinates: [121.4737, 31.2304]
          
        - location: "南京配送中心"
          type: "delivery"
          time: "12:00"
          duration_min: 45
          coordinates: [118.7969, 32.0603]
          
        - location: "苏州门店"
          type: "delivery"
          time: "15:00"
          duration_min: 30
          coordinates: [120.5853, 31.2990]
      
      # 约束条件
      constraints:
        - type: "time_window"
          location: "南京配送中心"
          window: ["11:00", "13:00"]
          
        - type: "capacity"
          max_weight_kg: 4000
          max_volume_m3: 25
          
        - type: "driver_hours"
          max_hours: 10
          
        - type: "vehicle_restrictions"
          city_center_access: false
          low_emission_zone: true
```

### 2.4 配送优化系统

```yaml
delivery_optimization:
  orders:
    - id: "order_001"
      customer: "cust_001"
      customer_name: "客户A"
      location: [121.4737, 31.2304]
      address: "上海市浦东新区XX路XX号"
      time_window: ["09:00", "17:00"]
      priority: "high"
      service_time_min: 15
      
      # 订单商品
      items:
        - sku: "SKU-001"
          qty: 10
          weight_kg: 25
          volume_m3: 0.09
          
        - sku: "SKU-002"
          qty: 5
          weight_kg: 4
          volume_m3: 0.009375
      
      # 特殊要求
      special_requirements:
        - fragile_handling: true
        - temperature_controlled: false
        - signature_required: true
        - insurance_required: false
        
    - id: "order_002"
      customer: "cust_002"
      customer_name: "客户B"
      location: [120.1551, 30.2741]
      address: "杭州市西湖区XX路XX号"
      time_window: ["10:00", "18:00"]
      priority: "medium"
      service_time_min: 10
      
      items:
        - sku: "SKU-001"
          qty: 3
          weight_kg: 7.5
          volume_m3: 0.027
      
      special_requirements:
        - fragile_handling: false
        - temperature_controlled: false
        - signature_required: false
        - insurance_required: false
  
  # 优化算法配置
  optimization:
    algorithm: "genetic_algorithm"
    population_size: 100
    generations: 50
    mutation_rate: 0.1
    crossover_rate: 0.8
    
    # 优化目标
    objectives:
      - minimize_distance
      - minimize_time
      - maximize_vehicle_utilization
      - minimize_fuel_consumption
      - maximize_customer_satisfaction
      
    # 约束条件
    constraints:
      - time_windows
      - vehicle_capacity
      - driver_hours
      - vehicle_restrictions
      - customer_priorities
      
    # 权重配置
    weights:
      distance: 0.3
      time: 0.25
      utilization: 0.2
      fuel: 0.15
      satisfaction: 0.1
```

### 2.5 供应链可视化系统

```yaml
supply_chain_visibility:
  nodes:
    - id: "supplier_001"
      name: "供应商A"
      type: "manufacturer"
      location: [116.4074, 39.9042]
      coordinates: [116.4074, 39.9042]
      address: "北京市朝阳区XX路XX号"
      
      # 供应商能力
      capabilities:
        - product_categories: ["electronics", "components"]
        - production_capacity: 10000
        - lead_time_days: 14
        - reliability_pct: 95
        - quality_rating: 4.5
        
      # 联系信息
      contact:
        phone: "+86-10-12345678"
        email: "contact@suppliera.com"
        website: "https://suppliera.com"
        
    - id: "dc_001"
      name: "上海配送中心"
      type: "distribution_center"
      location: [121.4737, 31.2304]
      coordinates: [121.4737, 31.2304]
      address: "上海市浦东新区XX路XX号"
      
      capabilities:
        - storage_capacity_m3: 100000
        - throughput_per_day: 5000
        - value_added_services: ["kitting", "labeling", "packaging"]
        
    - id: "store_001"
      name: "杭州门店"
      type: "retail_store"
      location: [120.1551, 30.2741]
      coordinates: [120.1551, 30.2741]
      address: "杭州市西湖区XX路XX号"
      
      capabilities:
        - daily_demand: 50
        - storage_capacity_m3: 1000
        - service_hours: ["09:00", "21:00"]
  
  # 物流流
  flows:
    - id: "flow_001"
      from: "supplier_001"
      to: "dc_001"
      product: "SKU-001"
      frequency: "weekly"
      batch_size: 1000
      transport_mode: "truck"
      lead_time_days: 3
      
      # 成本信息
      costs:
        transportation: 5000
        handling: 1000
        insurance: 200
        total: 6200
        
    - id: "flow_002"
      from: "dc_001"
      to: "store_001"
      product: "SKU-001"
      frequency: "daily"
      batch_size: 100
      transport_mode: "van"
      lead_time_days: 1
      
      costs:
        transportation: 300
        handling: 50
        insurance: 10
        total: 360
```

### 2.6 成本控制系统

```yaml
cost_control:
  cost_centers:
    - name: "warehousing"
      description: "仓储成本中心"
      components:
        - labor_cost_per_hour: 25
        - equipment_cost_per_hour: 15
        - space_cost_per_m3_month: 50
        - utilities_cost_per_month: 5000
        - maintenance_cost_per_month: 2000
        
      # 成本分配
      allocation_method: "activity_based"
      activities:
        - receiving: 0.2
        - storage: 0.4
        - picking: 0.25
        - shipping: 0.15
        
    - name: "transportation"
      description: "运输成本中心"
      components:
        - fuel_cost_per_km: 2.5
        - driver_cost_per_hour: 30
        - vehicle_depreciation_per_km: 1.0
        - maintenance_cost_per_km: 0.5
        - insurance_cost_per_month: 1000
        
      allocation_method: "distance_based"
      
    - name: "inventory"
      description: "库存成本中心"
      components:
        - holding_cost_percent: 20  # 年化库存持有成本
        - obsolescence_cost_percent: 5
        - insurance_cost_percent: 2
        - storage_cost_per_m3_month: 50
        
      allocation_method: "value_based"
  
  # 关键绩效指标
  kpis:
    - name: "inventory_turnover"
      target: 12
      calculation: "annual_sales / average_inventory"
      unit: "times_per_year"
      
    - name: "order_fulfillment_rate"
      target: 98
      calculation: "orders_fulfilled / total_orders * 100"
      unit: "percent"
      
    - name: "delivery_on_time_rate"
      target: 95
      calculation: "on_time_deliveries / total_deliveries * 100"
      unit: "percent"
      
    - name: "warehouse_utilization"
      target: 85
      calculation: "used_space / total_space * 100"
      unit: "percent"
      
    - name: "transportation_cost_per_km"
      target: 3.5
      calculation: "total_transportation_cost / total_distance"
      unit: "yuan_per_km"
      
    - name: "order_cycle_time"
      target: 24
      calculation: "average_time_from_order_to_delivery"
      unit: "hours"
```

## 3. 高级特性

### 3.1 智能预测系统

```yaml
intelligent_forecasting:
  demand_forecasting:
    models:
      - name: "time_series_forecast"
        algorithm: "arima"
        parameters:
          p: 1
          d: 1
          q: 1
        forecast_horizon_days: 30
        confidence_interval: 0.95
        
      - name: "machine_learning_forecast"
        algorithm: "random_forest"
        features:
          - historical_demand
          - seasonality
          - promotions
          - weather
          - events
        forecast_horizon_days: 90
        
    # 预测结果
    forecasts:
      - sku: "SKU-001"
        period: "2024-02-01 to 2024-02-28"
        predicted_demand: 1200
        confidence_lower: 1100
        confidence_upper: 1300
        accuracy_pct: 92
        
  # 库存优化
  inventory_optimization:
    algorithm: "dynamic_programming"
    objectives:
      - minimize_total_cost
      - maximize_service_level
      - minimize_stockouts
      
    constraints:
      - storage_capacity
      - budget_limits
      - supplier_constraints
      
    # 优化结果
    recommendations:
      - sku: "SKU-001"
        recommended_stock: 800
        reorder_point: 200
        reorder_quantity: 600
        expected_cost_savings: 15000
```

### 3.2 实时监控系统

```yaml
real_time_monitoring:
  # 车辆跟踪
  vehicle_tracking:
    tracking_method: "gps"
    update_frequency_seconds: 30
    
    metrics:
      - location
      - speed
      - fuel_level
      - engine_status
      - driver_behavior
      
    alerts:
      - name: "speeding_alert"
        condition: "speed > max_speed * 1.1"
        action: "notify_driver"
        
      - name: "fuel_low_alert"
        condition: "fuel_level < 20%"
        action: "suggest_refueling"
        
      - name: "route_deviation_alert"
        condition: "distance_from_route > 1km"
        action: "notify_dispatcher"
        
  # 库存监控
  inventory_monitoring:
    update_frequency_minutes: 15
    
    metrics:
      - stock_levels
      - movement_velocity
      - aging_analysis
      - space_utilization
      
    alerts:
      - name: "low_stock_alert"
        condition: "stock_level < reorder_point"
        action: "trigger_reorder"
        
      - name: "overstock_alert"
        condition: "stock_level > max_stock * 1.2"
        action: "review_forecast"
        
      - name: "aging_alert"
        condition: "days_in_stock > 90"
        action: "markdown_promotion"
        
  # 性能监控
  performance_monitoring:
    warehouse_metrics:
      - orders_per_hour
      - picking_accuracy
      - cycle_time
      - space_utilization
      
    transportation_metrics:
      - deliveries_per_day
      - on_time_delivery_rate
      - fuel_efficiency
      - vehicle_utilization
      
    customer_metrics:
      - order_fulfillment_rate
      - delivery_satisfaction
      - return_rate
      - customer_complaints
```

### 3.3 自动化决策系统

```yaml
automated_decision_making:
  # 自动补货
  auto_replenishment:
    enabled: true
    algorithm: "machine_learning"
    
    triggers:
      - stock_level_below_reorder_point
      - forecasted_demand_increase
      - supplier_promotion
      
    decisions:
      - action: "reorder"
        conditions:
          - "stock_level < reorder_point"
          - "supplier_available"
          - "budget_available"
        parameters:
          quantity: "reorder_quantity"
          supplier: "best_supplier"
          delivery_date: "earliest_available"
          
  # 动态定价
  dynamic_pricing:
    enabled: true
    algorithm: "reinforcement_learning"
    
    factors:
      - demand_level
      - competitor_prices
      - inventory_level
      - seasonality
      - costs
      
    constraints:
      - min_margin: 0.15
      - max_price_change: 0.2
      - price_floor: "cost * 1.1"
      
  # 路线优化
  route_optimization:
    enabled: true
    algorithm: "genetic_algorithm"
    
    real_time_updates: true
    update_triggers:
      - new_order
      - traffic_condition_change
      - vehicle_breakdown
      - weather_change
      
    optimization_criteria:
      - minimize_total_distance
      - minimize_total_time
      - maximize_vehicle_utilization
      - minimize_fuel_consumption
      - respect_time_windows
```

## 4. 集成和接口

### 4.1 系统集成

```yaml
system_integration:
  # ERP系统集成
  erp_integration:
    system: "SAP"
    interface: "REST_API"
    sync_frequency: "real_time"
    
    data_mappings:
      - erp_field: "material_code"
        dsl_field: "sku"
        
      - erp_field: "plant"
        dsl_field: "warehouse_id"
        
      - erp_field: "storage_location"
        dsl_field: "zone_id"
        
  # WMS系统集成
  wms_integration:
    system: "Manhattan_Associates"
    interface: "EDI"
    sync_frequency: "batch_hourly"
    
    transactions:
      - inbound_receipt
      - outbound_shipment
      - inventory_adjustment
      - cycle_count
      
  # TMS系统集成
  tms_integration:
    system: "Oracle_Transportation"
    interface: "SOAP_API"
    sync_frequency: "real_time"
    
    data_exchanges:
      - route_optimization
      - shipment_tracking
      - cost_allocation
      - performance_metrics
      
  # IoT设备集成
  iot_integration:
    devices:
      - type: "rfid_reader"
        location: "receiving_dock"
        data: ["sku", "quantity", "timestamp"]
        
      - type: "temperature_sensor"
        location: "cold_storage"
        data: ["temperature", "humidity", "timestamp"]
        
      - type: "weight_sensor"
        location: "shipping_dock"
        data: ["weight", "dimensions", "timestamp"]
        
      - type: "gps_tracker"
        location: "vehicle"
        data: ["location", "speed", "fuel_level", "timestamp"]
```

### 4.2 API接口定义

```yaml
api_interfaces:
  # 订单管理API
  order_management:
    base_url: "https://api.logistics.com/v1"
    
    endpoints:
      - path: "/orders"
        method: "GET"
        description: "获取订单列表"
        parameters:
          - customer_id: "string"
          - status: "enum"
          - date_from: "datetime"
          - date_to: "datetime"
          
      - path: "/orders"
        method: "POST"
        description: "创建新订单"
        body:
          customer_id: "string"
          items: "array"
          delivery_address: "object"
          time_window: "object"
          
      - path: "/orders/{order_id}"
        method: "PUT"
        description: "更新订单"
        
      - path: "/orders/{order_id}/track"
        method: "GET"
        description: "获取订单跟踪信息"
        
  # 库存管理API
  inventory_management:
    base_url: "https://api.logistics.com/v1"
    
    endpoints:
      - path: "/inventory"
        method: "GET"
        description: "获取库存信息"
        
      - path: "/inventory/{sku}"
        method: "GET"
        description: "获取特定SKU库存"
        
      - path: "/inventory/adjustments"
        method: "POST"
        description: "创建库存调整"
        
  # 运输管理API
  transportation_management:
    base_url: "https://api.logistics.com/v1"
    
    endpoints:
      - path: "/routes"
        method: "GET"
        description: "获取路线信息"
        
      - path: "/routes/optimize"
        method: "POST"
        description: "优化路线"
        
      - path: "/vehicles"
        method: "GET"
        description: "获取车辆信息"
        
      - path: "/vehicles/{vehicle_id}/track"
        method: "GET"
        description: "获取车辆跟踪信息"
```

## 5. 自动化生成示例

### 5.1 路线优化算法

```python
# 基于订单和车辆信息自动生成最优配送路线
def optimize_delivery_routes(orders, vehicles):
    """使用遗传算法优化配送路线"""
    
    # 适应度函数
    def fitness_function(route):
        total_distance = calculate_total_distance(route)
        total_time = calculate_total_time(route)
        vehicle_utilization = calculate_vehicle_utilization(route)
        fuel_consumption = calculate_fuel_consumption(route)
        
        # 综合评分（权重可配置）
        score = (
            0.3 * (1 / (1 + total_distance)) +
            0.25 * (1 / (1 + total_time)) +
            0.2 * vehicle_utilization +
            0.15 * (1 / (1 + fuel_consumption)) +
            0.1 * calculate_customer_satisfaction(route)
        )
        return score
    
    # 生成初始种群
    population = generate_initial_population(orders, vehicles)
    
    # 迭代优化
    for generation in range(50):
        # 选择
        population = selection(population, fitness_function)
        
        # 交叉
        population = crossover(population)
        
        # 变异
        population = mutation(population)
        
        # 评估
        population = evaluate_population(population, fitness_function)
    
    return get_best_route(population)

def calculate_total_distance(route):
    """计算路线总距离"""
    total_distance = 0
    current_location = route.start_location
    
    for stop in route.stops:
        distance = calculate_distance(current_location, stop.location)
        total_distance += distance
        current_location = stop.location
    
    return total_distance

def calculate_total_time(route):
    """计算路线总时间"""
    total_time = 0
    
    for i, stop in enumerate(route.stops):
        if i > 0:
            # 行驶时间
            travel_time = calculate_travel_time(route.stops[i-1], stop)
            total_time += travel_time
        
        # 服务时间
        total_time += stop.service_time
    
    return total_time
```

### 5.2 库存预测算法

```python
# 基于历史数据预测库存需求
def forecast_inventory_demand(historical_data, forecast_period=30):
    """使用时间序列分析预测库存需求"""
    
    import pandas as pd
    from statsmodels.tsa.arima.model import ARIMA
    from sklearn.ensemble import RandomForestRegressor
    
    # 数据预处理
    df = pd.DataFrame(historical_data)
    df['date'] = pd.to_datetime(df['date'])
    df = df.set_index('date')
    
    # 时间序列预测（ARIMA）
    model_arima = ARIMA(df['demand'], order=(1, 1, 1))
    model_fit = model_arima.fit()
    forecast_arima = model_fit.forecast(steps=forecast_period)
    
    # 机器学习预测（随机森林）
    features = ['day_of_week', 'month', 'season', 'promotion', 'weather']
    X = df[features]
    y = df['demand']
    
    model_rf = RandomForestRegressor(n_estimators=100, random_state=42)
    model_rf.fit(X, y)
    
    # 生成未来特征
    future_features = generate_future_features(forecast_period)
    forecast_rf = model_rf.predict(future_features)
    
    # 组合预测结果
    combined_forecast = 0.6 * forecast_arima + 0.4 * forecast_rf
    
    return {
        'forecast': combined_forecast,
        'confidence_interval': calculate_confidence_interval(combined_forecast),
        'accuracy': calculate_forecast_accuracy(historical_data)
    }

def calculate_reorder_parameters(forecast, lead_time, service_level=0.95):
    """计算补货参数"""
    
    # 安全库存
    demand_std = np.std(forecast)
    safety_stock = demand_std * norm.ppf(service_level) * np.sqrt(lead_time)
    
    # 再订货点
    reorder_point = np.mean(forecast) * lead_time + safety_stock
    
    # 经济订货量
    annual_demand = np.sum(forecast) * 12
    ordering_cost = 100  # 假设每次订货成本
    holding_cost_rate = 0.2  # 假设年化持有成本率
    unit_cost = 10  # 假设单位成本
    
    eoq = np.sqrt((2 * annual_demand * ordering_cost) / (unit_cost * holding_cost_rate))
    
    return {
        'safety_stock': safety_stock,
        'reorder_point': reorder_point,
        'economic_order_quantity': eoq
    }
```

### 5.3 成本优化算法

```python
# 优化物流成本
def optimize_logistics_costs(warehouses, suppliers, customers, orders):
    """使用线性规划优化物流成本"""
    
    from pulp import *
    
    # 创建优化问题
    prob = LpProblem("Logistics_Cost_Optimization", LpMinimize)
    
    # 决策变量
    # x[i,j,k] = 从供应商i到仓库j运输产品k的数量
    x = LpVariable.dicts("shipment",
                        [(i, j, k) for i in suppliers for j in warehouses for k in products],
                        lowBound=0)
    
    # 目标函数：最小化总成本
    prob += lpSum(
        x[i,j,k] * transportation_cost[i,j] * unit_cost[k]
        for i in suppliers for j in warehouses for k in products
    )
    
    # 约束条件
    # 1. 供应商产能约束
    for i in suppliers:
        for k in products:
            prob += lpSum(x[i,j,k] for j in warehouses) <= supplier_capacity[i,k]
    
    # 2. 仓库容量约束
    for j in warehouses:
        prob += lpSum(x[i,j,k] * volume[k] for i in suppliers for k in products) <= warehouse_capacity[j]
    
    # 3. 需求满足约束
    for j in warehouses:
        for k in products:
            prob += lpSum(x[i,j,k] for i in suppliers) >= demand[j,k]
    
    # 求解
    prob.solve()
    
    return {
        'status': LpStatus[prob.status],
        'total_cost': value(prob.objective),
        'shipment_plan': {var.name: var.varValue for var in prob.variables()}
    }
```

## 6. 验证和测试

### 6.1 DSL验证器

```python
class LogisticsDSLValidator:
    def validate_warehouse(self, warehouse):
        """验证仓库配置"""
        errors = []
        
        # 检查必需字段
        if not warehouse.get('id'):
            errors.append("Warehouse must have an ID")
        
        if not warehouse.get('name'):
            errors.append("Warehouse must have a name")
        
        if not warehouse.get('location'):
            errors.append("Warehouse must have a location")
        
        # 检查容量
        if warehouse.get('capacity_m3', 0) <= 0:
            errors.append("Warehouse capacity must be positive")
        
        # 检查分区
        zones = warehouse.get('zones', [])
        if not zones:
            errors.append("Warehouse must have at least one zone")
        
        total_zone_capacity = sum(zone.get('capacity_m3', 0) for zone in zones)
        if total_zone_capacity > warehouse.get('capacity_m3', 0):
            errors.append("Total zone capacity cannot exceed warehouse capacity")
        
        return errors
    
    def validate_route(self, route):
        """验证路线配置"""
        errors = []
        
        if not route.get('id'):
            errors.append("Route must have an ID")
        
        if not route.get('stops') or len(route['stops']) < 2:
            errors.append("Route must have at least 2 stops")
        
        # 检查时间窗口
        for stop in route.get('stops', []):
            if 'time_window' in stop:
                start_time, end_time = stop['time_window']
                if start_time >= end_time:
                    errors.append(f"Invalid time window for stop {stop.get('location', 'unknown')}")
        
        return errors
    
    def validate_inventory_policy(self, policy):
        """验证库存策略"""
        errors = []
        
        if policy.get('min_stock', 0) < 0:
            errors.append("Minimum stock cannot be negative")
        
        if policy.get('max_stock', 0) <= policy.get('min_stock', 0):
            errors.append("Maximum stock must be greater than minimum stock")
        
        if policy.get('reorder_point', 0) < policy.get('min_stock', 0):
            errors.append("Reorder point should be at least minimum stock")
        
        if policy.get('lead_time_days', 0) < 0:
            errors.append("Lead time cannot be negative")
        
        return errors
```

### 6.2 性能测试

```python
# 性能测试用例
class LogisticsPerformanceTest:
    def test_route_optimization_performance(self):
        """测试路线优化性能"""
        import time
        
        # 准备测试数据
        orders = generate_test_orders(100)
        vehicles = generate_test_vehicles(10)
        
        # 测试优化时间
        start_time = time.time()
        optimal_route = optimize_delivery_routes(orders, vehicles)
        end_time = time.time()
        
        optimization_time = end_time - start_time
        
        # 性能断言
        assert optimization_time < 30, f"Route optimization took {optimization_time}s, expected < 30s"
        assert optimal_route is not None, "Should return a valid route"
        
        # 测试优化质量
        total_distance = calculate_total_distance(optimal_route)
        assert total_distance < 1000, f"Total distance {total_distance}km is too high"
    
    def test_inventory_forecast_accuracy(self):
        """测试库存预测准确性"""
        # 准备历史数据
        historical_data = generate_historical_demand_data(365)
        
        # 分割训练和测试数据
        train_data = historical_data[:-30]
        test_data = historical_data[-30:]
        
        # 训练模型并预测
        forecast = forecast_inventory_demand(train_data, forecast_period=30)
        
        # 计算准确性
        actual_demand = [d['demand'] for d in test_data]
        predicted_demand = forecast['forecast']
        
        mape = calculate_mape(actual_demand, predicted_demand)
        
        # 准确性断言
        assert mape < 0.15, f"Forecast accuracy {mape} is too low, expected < 15%"
    
    def test_cost_optimization(self):
        """测试成本优化"""
        # 准备测试数据
        warehouses = generate_test_warehouses(5)
        suppliers = generate_test_suppliers(10)
        customers = generate_test_customers(20)
        orders = generate_test_orders(50)
        
        # 运行优化
        result = optimize_logistics_costs(warehouses, suppliers, customers, orders)
        
        # 验证结果
        assert result['status'] == 'Optimal', f"Optimization failed: {result['status']}"
        assert result['total_cost'] > 0, "Total cost should be positive"
        
        # 验证约束满足
        assert validate_constraints(result['shipment_plan'], warehouses, suppliers, orders)

def calculate_mape(actual, predicted):
    """计算平均绝对百分比误差"""
    return np.mean(np.abs((np.array(actual) - np.array(predicted)) / np.array(actual))) * 100
```

## 7. 总结

本DSL为物流系统提供了完整的形式化描述框架，支持：

- **完整的仓储管理**：分区管理、设备配置、环境监控、安全控制
- **智能库存管理**：库存策略、供应商管理、包装信息、ABC分类
- **高效运输调度**：车辆管理、路线规划、约束处理、成本控制
- **优化配送系统**：订单管理、算法优化、多目标优化、实时调整
- **供应链可视化**：节点管理、物流流、成本分析、性能监控
- **智能预测系统**：需求预测、库存优化、实时监控、自动决策
- **自动化工具**：路线优化、成本优化、性能测试、验证工具

通过这个DSL，可以实现物流系统的统一描述、自动化管理、智能优化和持续改进，为现代物流提供强大的数字化管理基础。
