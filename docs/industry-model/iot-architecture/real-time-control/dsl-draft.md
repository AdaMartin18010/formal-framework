# 实时控制DSL草案

## 1. 概述

实时控制DSL旨在提供一种统一的方式来描述和配置实时控制系统，包括控制算法、反馈机制、实时调度等核心概念。该DSL支持主流实时控制平台如ROS、OpenHAB、Node-RED等的统一建模。

## 2. 核心语法定义

### 2.1 控制算法定义

```yaml
# 控制算法配置
control_algorithm:
  name: "temperature_controller"
  type: "pid"  # pid, fuzzy, predictive, adaptive
  
  pid_control:
    kp: 2.5  # 比例系数
    ki: 0.1  # 积分系数
    kd: 0.05  # 微分系数
    setpoint: 25.0  # 设定值
    output_limits:
      min: 0.0
      max: 100.0
    anti_windup: true
    deadband: 0.5
    
  fuzzy_control:
    membership_functions:
      temperature_error:
        - name: "negative_large"
          range: [-10, -5]
          function: "trapezoid"
        - name: "negative_small"
          range: [-5, 0]
          function: "triangle"
        - name: "zero"
          range: [-2, 2]
          function: "triangle"
        - name: "positive_small"
          range: [0, 5]
          function: "triangle"
        - name: "positive_large"
          range: [5, 10]
          function: "trapezoid"
    
    rules:
      - if: ["temperature_error", "negative_large"]
        then: ["output", "positive_large"]
      - if: ["temperature_error", "negative_small"]
        then: ["output", "positive_small"]
      - if: ["temperature_error", "zero"]
        then: ["output", "zero"]
      - if: ["temperature_error", "positive_small"]
        then: ["output", "negative_small"]
      - if: ["temperature_error", "positive_large"]
        then: ["output", "negative_large"]
  
  predictive_control:
    prediction_horizon: 10
    control_horizon: 3
    model_type: "linear"
    constraints:
      - variable: "output"
        min: 0.0
        max: 100.0
      - variable: "rate_of_change"
        min: -10.0
        max: 10.0
```

### 2.2 反馈系统定义

```yaml
# 反馈系统配置
feedback_system:
  name: "sensor_feedback"
  type: "closed_loop"  # open_loop, closed_loop, feedforward
  
  sensors:
    - name: "temperature_sensor"
      type: "analog"
      unit: "celsius"
      range: [-40, 125]
      accuracy: 0.1
      sampling_rate: "10Hz"
      calibration:
        offset: 0.0
        scale: 1.0
        valid_range: [-40, 125]
    
    - name: "humidity_sensor"
      type: "digital"
      unit: "percent"
      range: [0, 100]
      accuracy: 1.0
      sampling_rate: "1Hz"
      calibration:
        offset: 0.0
        scale: 1.0
        valid_range: [0, 100]
  
  state_estimation:
    method: "kalman_filter"  # kalman_filter, particle_filter, observer
    process_noise: 0.01
    measurement_noise: 0.1
    state_variables:
      - "temperature"
      - "temperature_rate"
      - "humidity"
    
  error_handling:
    sensor_failure:
      detection_method: "timeout"
      timeout: "5s"
      fallback_action: "use_last_valid_value"
    data_validation:
      range_check: true
      rate_of_change_check: true
      outlier_detection: true
      outlier_threshold: 3.0  # standard deviations
```

### 2.3 实时调度定义

```yaml
# 实时调度配置
real_time_scheduling:
  name: "control_scheduler"
  type: "rate_monotonic"  # rate_monotonic, earliest_deadline, priority_based
  
  tasks:
    - name: "sensor_reading"
      priority: 10
      period: "100ms"
      deadline: "100ms"
      execution_time: "5ms"
      cpu_affinity: 0
      memory_requirement: "1MB"
      
    - name: "control_computation"
      priority: 9
      period: "50ms"
      deadline: "50ms"
      execution_time: "10ms"
      cpu_affinity: 0
      memory_requirement: "2MB"
      
    - name: "actuator_output"
      priority: 8
      period: "50ms"
      deadline: "50ms"
      execution_time: "2ms"
      cpu_affinity: 0
      memory_requirement: "0.5MB"
      
    - name: "data_logging"
      priority: 5
      period: "1s"
      deadline: "1s"
      execution_time: "20ms"
      cpu_affinity: 1
      memory_requirement: "5MB"
  
  scheduling_policy:
    preemption: true
    priority_inheritance: true
    resource_sharing: "priority_ceiling"
    
  timing_constraints:
    jitter_tolerance: "1ms"
    deadline_miss_tolerance: 0.01  # 1% deadline miss rate
    response_time_requirement: "20ms"
```

### 2.4 执行器定义

```yaml
# 执行器配置
actuator:
  name: "heater_control"
  type: "pwm"  # pwm, analog, digital, servo
  
  pwm_actuator:
    pin: 12
    frequency: "1kHz"
    resolution: 12  # bits
    duty_cycle_range: [0, 100]
    dead_time: "1us"
    
  analog_actuator:
    pin: "A0"
    voltage_range: [0, 5]
    current_limit: "2A"
    protection:
      overcurrent: true
      overvoltage: true
      undervoltage: true
    
  servo_actuator:
    pin: 9
    pulse_range: [1000, 2000]  # microseconds
    angle_range: [0, 180]  # degrees
    speed_limit: "60deg/s"
    
  safety:
    emergency_stop: true
    safe_state: "off"
    watchdog_timeout: "1s"
    fault_detection:
      overcurrent: true
      overvoltage: true
      communication_loss: true
```

### 2.5 控制回路定义

```yaml
# 控制回路配置
control_loop:
  name: "temperature_control_loop"
  type: "single_input_single_output"  # siso, mimo, cascade
  
  input:
    sensor: "temperature_sensor"
    setpoint_source: "user_input"
    setpoint_value: 25.0
    setpoint_ramp:
      enabled: true
      rate: "1deg/min"
      
  output:
    actuator: "heater_control"
    output_scale: 1.0
    output_offset: 0.0
    
  controller:
    algorithm: "temperature_controller"
    tuning_method: "ziegler_nichols"  # manual, ziegler_nichols, auto_tune
    auto_tune:
      enabled: true
      method: "relay_feedback"
      test_duration: "5min"
      safety_margin: 0.8
      
  performance:
    settling_time: "30s"
    overshoot: 0.05  # 5%
    steady_state_error: 0.1
    rise_time: "10s"
    
  monitoring:
    metrics:
      - "setpoint_tracking_error"
      - "control_output"
      - "actuator_position"
      - "system_response_time"
    logging:
      enabled: true
      interval: "100ms"
      retention: "24h"
```

## 3. 高级特性

### 3.1 多变量控制

```yaml
# 多变量控制系统
multivariable_control:
  name: "climate_control_system"
  type: "mimo"  # multiple input multiple output
  
  inputs:
    - name: "temperature"
      sensor: "temperature_sensor"
      setpoint: 25.0
      unit: "celsius"
    - name: "humidity"
      sensor: "humidity_sensor"
      setpoint: 50.0
      unit: "percent"
    - name: "air_quality"
      sensor: "co2_sensor"
      setpoint: 800.0
      unit: "ppm"
      
  outputs:
    - name: "heater"
      actuator: "heater_control"
      influence: ["temperature"]
    - name: "humidifier"
      actuator: "humidifier_control"
      influence: ["humidity"]
    - name: "ventilator"
      actuator: "ventilator_control"
      influence: ["air_quality", "humidity"]
      
  coupling_matrix:
    - row: [1.0, 0.0, 0.0]  # heater influence
    - row: [0.0, 1.0, 0.0]  # humidifier influence
    - row: [0.0, 0.3, 1.0]  # ventilator influence
      
  decoupling:
    method: "feedforward"
    matrix_inverse: true
    adaptive_decoupling: true
```

### 3.2 自适应控制

```yaml
# 自适应控制系统
adaptive_control:
  name: "adaptive_temperature_control"
  type: "model_reference"  # model_reference, self_tuning, gain_scheduling
  
  reference_model:
    type: "second_order"
    natural_frequency: 0.5
    damping_ratio: 0.7
    steady_state_gain: 1.0
    
  adaptation:
    method: "gradient_descent"
    learning_rate: 0.01
    adaptation_gain: 0.1
    parameter_bounds:
      min: [0.1, 0.1, 0.1]
      max: [10.0, 10.0, 10.0]
      
  parameter_estimation:
    method: "recursive_least_squares"
    forgetting_factor: 0.95
    covariance_reset: true
    reset_threshold: 0.1
    
  stability_monitoring:
    lyapunov_function: true
    parameter_drift_detection: true
    stability_margin: 0.1
```

### 3.3 故障诊断

```yaml
# 故障诊断系统
fault_diagnosis:
  name: "system_fault_detection"
  
  fault_models:
    - name: "sensor_bias"
      type: "additive"
      affected_sensor: "temperature_sensor"
      detection_method: "residual_analysis"
      threshold: 2.0
      
    - name: "actuator_saturation"
      type: "nonlinear"
      affected_actuator: "heater_control"
      detection_method: "output_monitoring"
      threshold: 95.0
      
    - name: "system_drift"
      type: "slow_varying"
      affected_system: "temperature_control_loop"
      detection_method: "trend_analysis"
      window_size: "1h"
      
  diagnosis:
    method: "fault_tree_analysis"
    confidence_threshold: 0.8
    isolation_time: "10s"
    
  recovery:
    automatic_recovery: true
    recovery_strategies:
      - fault: "sensor_bias"
        action: "sensor_calibration"
      - fault: "actuator_saturation"
        action: "reduce_setpoint"
      - fault: "system_drift"
        action: "controller_retuning"
```

## 4. 平台特定扩展

### 4.1 ROS扩展

```yaml
# ROS特定配置
ros_control:
  name: "ros_control_system"
  
  nodes:
    - name: "temperature_controller_node"
      package: "control_pkg"
      executable: "temperature_controller"
      parameters:
        - name: "kp"
          value: 2.5
        - name: "ki"
          value: 0.1
        - name: "kd"
          value: 0.05
          
  topics:
    - name: "/temperature/sensor"
      type: "std_msgs/Float32"
      queue_size: 10
      latch: false
    - name: "/temperature/setpoint"
      type: "std_msgs/Float32"
      queue_size: 10
      latch: true
    - name: "/heater/command"
      type: "std_msgs/Float32"
      queue_size: 10
      latch: false
      
  services:
    - name: "/controller/tune"
      type: "control_pkg/TuneController"
    - name: "/controller/status"
      type: "control_pkg/ControllerStatus"
      
  actions:
    - name: "/controller/auto_tune"
      type: "control_pkg/AutoTune"
      goal:
        duration: "5min"
        safety_margin: 0.8
      feedback:
        progress: "float32"
        current_parameters: "float32[]"
      result:
        final_parameters: "float32[]"
        performance_metrics: "float32[]"
```

### 4.2 OpenHAB扩展

```yaml
# OpenHAB特定配置
openhab_control:
  name: "openhab_control_system"
  
  items:
    - name: "Temperature_Sensor"
      type: "Number"
      unit: "°C"
      persistence: "rrd4j"
      
    - name: "Temperature_Setpoint"
      type: "Number"
      unit: "°C"
      persistence: "rrd4j"
      
    - name: "Heater_Control"
      type: "Switch"
      persistence: "rrd4j"
      
  rules:
    - name: "Temperature_Control_Rule"
      trigger:
        - item: "Temperature_Sensor"
          state: "changed"
        - item: "Temperature_Setpoint"
          state: "changed"
      condition:
        - item: "Temperature_Sensor"
          state: "!= null"
      action:
        - type: "script"
          script: |
            val currentTemp = Temperature_Sensor.state as Number
            val setpoint = Temperature_Setpoint.state as Number
            val error = setpoint - currentTemp
            
            if (error > 0.5) {
              Heater_Control.sendCommand(ON)
            } else if (error < -0.5) {
              Heater_Control.sendCommand(OFF)
            }
            
  sitemaps:
    - name: "control"
      label: "Control Panel"
      frame:
        - item: "Temperature_Sensor"
          label: "Current Temperature"
        - item: "Temperature_Setpoint"
          label: "Setpoint"
        - item: "Heater_Control"
          label: "Heater"
```

### 4.3 Node-RED扩展

```yaml
# Node-RED特定配置
nodered_control:
  name: "nodered_control_system"
  
  flows:
    - name: "temperature_control_flow"
      nodes:
        - id: "sensor_input"
          type: "mqtt in"
          topic: "sensor/temperature"
          qos: 1
          
        - id: "setpoint_input"
          type: "inject"
          payload: "25"
          topic: "control/setpoint"
          
        - id: "pid_controller"
          type: "pid"
          kp: 2.5
          ki: 0.1
          kd: 0.05
          setpoint: "{{msg.payload}}"
          
        - id: "actuator_output"
          type: "mqtt out"
          topic: "actuator/heater"
          qos: 1
          
      connections:
        - from: "sensor_input"
          to: "pid_controller"
        - from: "setpoint_input"
          to: "pid_controller"
        - from: "pid_controller"
          to: "actuator_output"
          
  dashboards:
    - name: "control_dashboard"
      groups:
        - name: "Temperature Control"
          width: "6"
          height: "4"
          nodes:
            - id: "temp_gauge"
              type: "gauge"
              label: "Temperature"
              min: 0
              max: 50
            - id: "setpoint_slider"
              type: "slider"
              label: "Setpoint"
              min: 0
              max: 50
            - id: "heater_status"
              type: "switch"
              label: "Heater"
```

## 5. 自动化生成示例

### 5.1 控制算法自动调参

```python
# 控制算法自动调参
def auto_tune_controller(plant_model, performance_requirements):
    """根据被控对象模型和性能要求自动调参"""
    
    # 分析被控对象特性
    plant_analysis = analyze_plant_characteristics(plant_model)
    
    # 选择控制算法
    if plant_analysis["type"] == "first_order":
        controller_type = "pid"
        tuning_method = "ziegler_nichols"
    elif plant_analysis["type"] == "second_order":
        controller_type = "pid"
        tuning_method = "cohen_coon"
    elif plant_analysis["type"] == "nonlinear":
        controller_type = "fuzzy"
        tuning_method = "expert_rules"
    
    # 自动调参
    if tuning_method == "ziegler_nichols":
        parameters = ziegler_nichols_tuning(plant_analysis)
    elif tuning_method == "cohen_coon":
        parameters = cohen_coon_tuning(plant_analysis)
    elif tuning_method == "expert_rules":
        parameters = fuzzy_expert_tuning(plant_analysis)
    
    # 验证性能
    performance = validate_control_performance(parameters, performance_requirements)
    
    return {
        "controller_type": controller_type,
        "parameters": parameters,
        "performance": performance
    }
```

### 5.2 实时调度自动配置

```python
# 实时调度自动配置
def generate_scheduling_config(control_tasks, system_constraints):
    """根据控制任务和系统约束生成调度配置"""
    
    # 分析任务特性
    task_analysis = analyze_task_characteristics(control_tasks)
    
    # 选择调度算法
    if task_analysis["utilization"] < 0.69:
        scheduling_algorithm = "rate_monotonic"
    elif task_analysis["deadline_constraints"]:
        scheduling_algorithm = "earliest_deadline_first"
    else:
        scheduling_algorithm = "priority_based"
    
    # 分配优先级
    priorities = assign_task_priorities(control_tasks, scheduling_algorithm)
    
    # 验证可调度性
    schedulability = check_schedulability(control_tasks, priorities, system_constraints)
    
    if not schedulability["feasible"]:
        # 调整任务参数
        adjusted_tasks = adjust_task_parameters(control_tasks, schedulability["bottlenecks"])
        priorities = assign_task_priorities(adjusted_tasks, scheduling_algorithm)
        schedulability = check_schedulability(adjusted_tasks, priorities, system_constraints)
    
    return {
        "scheduling_algorithm": scheduling_algorithm,
        "task_configurations": adjusted_tasks,
        "priorities": priorities,
        "schedulability": schedulability
    }
```

### 5.3 故障诊断自动配置

```python
# 故障诊断自动配置
def generate_fault_diagnosis_config(system_model, historical_data):
    """根据系统模型和历史数据生成故障诊断配置"""
    
    # 分析系统结构
    system_analysis = analyze_system_structure(system_model)
    
    # 识别关键组件
    critical_components = identify_critical_components(system_analysis)
    
    # 生成故障模型
    fault_models = []
    for component in critical_components:
        fault_types = analyze_component_fault_types(component, historical_data)
        for fault_type in fault_types:
            fault_model = {
                "name": f"{component['name']}_{fault_type['name']}",
                "type": fault_type["type"],
                "affected_component": component["name"],
                "detection_method": select_detection_method(fault_type),
                "threshold": calculate_detection_threshold(fault_type, historical_data)
            }
            fault_models.append(fault_model)
    
    # 生成诊断策略
    diagnosis_strategy = generate_diagnosis_strategy(fault_models, system_analysis)
    
    # 生成恢复策略
    recovery_strategies = generate_recovery_strategies(fault_models, system_analysis)
    
    return {
        "fault_models": fault_models,
        "diagnosis_strategy": diagnosis_strategy,
        "recovery_strategies": recovery_strategies
    }
```

## 6. 验证和测试

### 6.1 控制性能验证

```python
# 控制性能验证器
class ControlPerformanceValidator:
    def __init__(self, control_system):
        self.control_system = control_system
    
    def validate_settling_time(self, setpoint_change, max_settling_time):
        """验证调节时间"""
        response = self.control_system.step_response(setpoint_change)
        settling_time = calculate_settling_time(response, 0.05)  # 5% band
        return settling_time <= max_settling_time
    
    def validate_overshoot(self, setpoint_change, max_overshoot):
        """验证超调量"""
        response = self.control_system.step_response(setpoint_change)
        overshoot = calculate_overshoot(response)
        return overshoot <= max_overshoot
    
    def validate_steady_state_error(self, setpoint, max_error):
        """验证稳态误差"""
        steady_state = self.control_system.steady_state(setpoint)
        error = abs(steady_state - setpoint)
        return error <= max_error
    
    def validate_rise_time(self, setpoint_change, max_rise_time):
        """验证上升时间"""
        response = self.control_system.step_response(setpoint_change)
        rise_time = calculate_rise_time(response)
        return rise_time <= max_rise_time
```

### 6.2 实时性能测试

```python
# 实时性能测试器
class RealTimePerformanceTester:
    def __init__(self, real_time_system):
        self.system = real_time_system
    
    def test_deadline_compliance(self, duration):
        """测试截止时间遵守情况"""
        deadline_misses = 0
        total_tasks = 0
        
        start_time = time.time()
        while time.time() - start_time < duration:
            for task in self.system.tasks:
                execution_start = time.time()
                task.execute()
                execution_time = time.time() - execution_start
                
                if execution_time > task.deadline:
                    deadline_misses += 1
                total_tasks += 1
        
        miss_rate = deadline_misses / total_tasks
        return miss_rate <= 0.01  # 1% miss rate
    
    def test_jitter(self, task_name, samples):
        """测试任务抖动"""
        execution_times = []
        
        for _ in range(samples):
            start_time = time.time()
            self.system.execute_task(task_name)
            execution_time = time.time() - start_time
            execution_times.append(execution_time)
        
        jitter = calculate_jitter(execution_times)
        return jitter <= self.system.tasks[task_name].jitter_tolerance
    
    def test_response_time(self, event_type, max_response_time):
        """测试响应时间"""
        response_times = []
        
        for _ in range(100):
            event_time = time.time()
            self.system.handle_event(event_type)
            response_time = time.time() - event_time
            response_times.append(response_time)
        
        max_observed_response = max(response_times)
        return max_observed_response <= max_response_time
```

## 7. 总结

实时控制DSL提供了一种统一的方式来描述和配置实时控制系统。通过结构化的配置语言，可以：

1. **统一建模**：支持多种实时控制平台的统一建模
2. **自动调参**：根据被控对象特性自动选择控制算法和参数
3. **实时调度**：自动生成实时任务调度配置
4. **故障诊断**：提供完整的故障检测和诊断能力

该DSL为实时控制系统的标准化和自动化提供了强有力的支撑，有助于提高控制系统的性能和可靠性。
