# 物流模型DSL草案

## 1. 概述

物流模型DSL用于统一描述物流系统：仓储管理、运输调度、配送优化、供应链可视化、成本控制等，支持与WMS、TMS、OMS、ERP系统对接。

## 2. 核心语法定义

### 2.1 仓储管理

```yaml
warehouse_management:
  warehouses:
    - id: "wh_001"
      name: "上海主仓"
      location: [121.4737, 31.2304]
      capacity_m3: 50000
      zones:
        - name: "A区"; type: "fast_moving"; rack_type: "narrow_aisle"
        - name: "B区"; type: "slow_moving"; rack_type: "wide_aisle"
        - name: "C区"; type: "bulk"; rack_type: "floor_storage"
      equipment:
        - type: "forklift"; count: 8; capacity_kg: 2000
        - type: "conveyor"; length_m: 200; speed_mps: 0.5
        - type: "asrs"; aisles: 4; levels: 12; positions: 480

  inventory:
    skus:
      - sku: "SKU-001"
        name: "商品A"
        dimensions: [30, 20, 15]  # cm
        weight_kg: 2.5
        storage_type: "rack"
        abc_class: "A"
        min_stock: 100
        max_stock: 1000
        reorder_point: 150
        lead_time_days: 7
```

### 2.2 运输调度

```yaml
transportation:
  vehicles:
    - id: "truck_001"
      type: "box_truck"
      capacity_m3: 30
      capacity_kg: 5000
      fuel_type: "diesel"
      driver: "driver_001"
      availability: ["Mon", "Tue", "Wed", "Thu", "Fri"]
      operating_hours: ["08:00", "18:00"]
  
  routes:
    - id: "route_001"
      name: "上海-南京-苏州"
      distance_km: 450
      estimated_time_h: 6
      stops:
        - location: "上海"; type: "pickup"; time: "09:00"
        - location: "南京"; type: "delivery"; time: "12:00"
        - location: "苏州"; type: "delivery"; time: "15:00"
      constraints:
        - type: "time_window"; location: "南京"; window: ["11:00", "13:00"]
        - type: "capacity"; max_weight_kg: 4000
```

### 2.3 配送优化

```yaml
delivery_optimization:
  orders:
    - id: "order_001"
      customer: "cust_001"
      location: [121.4737, 31.2304]
      time_window: ["09:00", "17:00"]
      priority: "high"
      items:
        - sku: "SKU-001"; qty: 10
        - sku: "SKU-002"; qty: 5
  
  optimization:
    algorithm: "genetic_algorithm"
    objectives:
      - minimize_distance
      - minimize_time
      - maximize_vehicle_utilization
    constraints:
      - time_windows
      - vehicle_capacity
      - driver_hours
    parameters:
      population_size: 100
      generations: 50
      mutation_rate: 0.1
```

### 2.4 供应链可视化

```yaml
supply_chain_visibility:
  nodes:
    - id: "supplier_001"
      type: "supplier"
      location: [116.4074, 39.9042]
      lead_time_days: 14
      reliability_pct: 95
    - id: "dc_001"
      type: "distribution_center"
      location: [121.4737, 31.2304]
      capacity_m3: 100000
    - id: "store_001"
      type: "retail_store"
      location: [120.1551, 30.2741]
      daily_demand: 50
  
  flows:
    - from: "supplier_001"
      to: "dc_001"
      product: "SKU-001"
      frequency: "weekly"
      batch_size: 1000
    - from: "dc_001"
      to: "store_001"
      product: "SKU-001"
      frequency: "daily"
      batch_size: 100
```

### 2.5 成本控制

```yaml
cost_control:
  cost_centers:
    - name: "warehousing"
      components:
        - labor_cost_per_hour: 25
        - equipment_cost_per_hour: 15
        - space_cost_per_m3_month: 50
    - name: "transportation"
      components:
        - fuel_cost_per_km: 2.5
        - driver_cost_per_hour: 30
        - vehicle_depreciation_per_km: 1.0
  
  kpis:
    - name: "inventory_turnover"
      target: 12
      calculation: "annual_sales / average_inventory"
    - name: "order_fulfillment_rate"
      target: 98
      calculation: "orders_fulfilled / total_orders * 100"
    - name: "delivery_on_time_rate"
      target: 95
      calculation: "on_time_deliveries / total_deliveries * 100"
```

## 3. 自动化生成示例

```python
# 基于订单和车辆信息自动生成最优配送路线
def optimize_delivery_routes(orders, vehicles):
    # 使用遗传算法优化路线
    def fitness_function(route):
        total_distance = calculate_total_distance(route)
        total_time = calculate_total_time(route)
        return 1 / (total_distance + total_time * 10)
    
    # 生成初始种群
    population = generate_initial_population(orders, vehicles)
    
    # 迭代优化
    for generation in range(50):
        population = evolve_population(population, fitness_function)
    
    return get_best_route(population)
```

## 4. 验证与测试

```python
class LogisticsDSLValidator:
    def validate_warehouse(self, warehouse):
        assert warehouse["capacity_m3"] > 0, "warehouse capacity must be positive"
        assert len(warehouse["zones"]) > 0, "warehouse must have at least one zone"
    
    def validate_route(self, route):
        assert route["distance_km"] > 0, "route distance must be positive"
        assert len(route["stops"]) >= 2, "route must have at least 2 stops"
```

## 5. 总结

本DSL覆盖物流领域的核心业务要素，支持仓储管理、运输调度、配送优化、供应链可视化与成本控制的自动化配置生成，可与WMS、TMS、ERP系统无缝集成。
