# 物联网行业模型 - 案例库

**本节要点**：（1）设备接入、边缘计算、数据采集、实时控制、安全与隐私五类核心领域；（2）与 L3 运行时、控制调度、监控模型的映射及 EdgeX、KubeEdge、OPC UA 等；（3）行业案例库与标准映射关系；（4）设备管理与边缘计算最佳实践。  
**预计阅读时间**：全文约 28–38 分钟；仅读「核心业务领域」+「技术架构组件」约 10 分钟。

## 概述

物联网行业模型基于通用形式化建模体系，为物联网系统提供统一的理论基础和工程实践框架。本模型涵盖设备接入、边缘计算、数据采集、实时控制、安全通信等核心物联网技术要素。

**行业↔通用模型对齐一览表**：本行业与通用 L2/L3 的映射见 [formal-model 通用形式化建模](../../formal-model/)（运行时、控制调度、监控等）；对象/属性/不变式级对齐见 [L2↔L3 映射总表](../../formal-model/alignment-L2-L3-matrix.md)。L4 索引与权威对标见 [L4_D92_IOT_行业索引与对标](../../L4_D92_IOT_行业索引与对标.md)。

## 目录

- [1. 核心业务领域](#1-核心业务领域)
- [2. 技术架构组件](#2-技术架构组件)
- [3. 行业案例库](#3-行业案例库)
- [4. 标准映射关系](#4-标准映射关系)
- [5. 最佳实践](#5-最佳实践)

## 1. 核心业务领域

### 1.1 设备接入与管理 (Device Access & Management)

- **多协议支持**：MQTT、CoAP、HTTP、Modbus、OPC UA等
- **设备注册**：设备身份认证、设备证书管理、设备生命周期
- **设备监控**：设备状态监控、健康检查、故障诊断
- **远程控制**：设备配置、固件升级、远程操作

### 1.2 边缘计算 (Edge Computing)

- **边缘节点**：边缘网关、边缘服务器、边缘设备
- **数据处理**：实时数据处理、本地计算、数据过滤
- **边缘智能**：AI推理、机器学习、决策制定
- **资源管理**：计算资源调度、存储管理、网络优化

### 1.3 数据采集与传输 (Data Collection & Transmission)

- **数据采集**：传感器数据、设备状态、环境参数
- **数据传输**：实时传输、批量传输、离线缓存
- **数据质量**：数据验证、异常检测、数据清洗
- **数据安全**：数据加密、访问控制、隐私保护

### 1.4 实时控制 (Real-time Control)

- **实时调度**：任务调度、资源分配、优先级管理
- **控制算法**：PID控制、模糊控制、智能控制
- **反馈控制**：闭环控制、状态反馈、误差校正
- **安全控制**：安全联锁、紧急停车、故障保护

### 1.5 安全与隐私 (Security & Privacy)

- **设备安全**：设备认证、安全启动、安全存储
- **通信安全**：加密传输、身份验证、访问控制
- **数据隐私**：数据脱敏、隐私保护、合规性
- **网络安全**：网络隔离、入侵检测、安全监控

## 2. 技术架构组件

### 2.1 开源技术栈

| 组件类型 | 主流技术 | 功能描述 |
|---------|---------|---------|
| 设备接入 | Eclipse Mosquitto, CoAP, Modbus | 设备通信协议 |
| 边缘计算 | EdgeX Foundry, K3s, OpenYurt | 边缘计算平台 |
| 数据处理 | Apache Kafka, InfluxDB, TimescaleDB | 时序数据处理 |
| 设备管理 | AWS IoT Core, Azure IoT Hub, ThingsBoard | 设备管理平台 |
| 安全通信 | TLS/SSL, DTLS, OAuth 2.0 | 安全通信协议 |

### 2.2 物联网架构模式

```yaml
iot_architecture:
  device_layer:
    - sensors: "传感器设备"
    - actuators: "执行器设备"
    - gateways: "边缘网关"
  
  edge_layer:
    - edge_computing: "边缘计算节点"
    - local_storage: "本地存储"
    - edge_ai: "边缘AI推理"
  
  cloud_layer:
    - iot_platform: "IoT平台"
    - data_analytics: "数据分析"
    - application_services: "应用服务"
  
  security_layer:
    - device_security: "设备安全"
    - communication_security: "通信安全"
    - data_security: "数据安全"
```

## 3. 行业案例库

### 案例一：多协议设备接入（MQTT/Modbus）

#### 场景与目标

- **业务场景**：工业物联网设备接入，支持多种通信协议的统一管理
- **技术目标**：实现MQTT、Modbus、CoAP等协议的设备接入和数据采集
- **质量目标**：设备接入成功率 > 99%，数据采集准确率 > 99.9%

#### 术语与概念对齐

- **MQTT Broker** ↔ `L3_D01_交互标准模型.md` 消息代理
- **Modbus Master/Slave** ↔ `L3_D01_交互标准模型.md` 主从通信
- **Device Registry** ↔ `L3_D02_数据标准模型.md` 设备注册
- **Protocol Gateway** ↔ `L3_D01_交互标准模型.md` 协议网关

#### 结构与约束

- **协议一致性**：多协议设备状态一致性、数据格式标准化
- **设备管理**：设备注册、认证、生命周期管理
- **数据完整性**：数据采集完整性、传输可靠性、存储一致性

#### 接口与 DSL 片段

```yaml
device_access:
  protocols:
    - name: "mqtt"
      broker: "mqtt.broker.com:1883"
      qos: 1
      topics:
        - "devices/+/telemetry"
        - "devices/+/commands"
      
    - name: "modbus"
      master: "192.168.1.100:502"
      slave_address: 1
      registers:
        - address: 40001
          type: "holding"
          data_type: "float32"
      
    - name: "coap"
      server: "coap.server.com:5683"
      resources:
        - path: "/sensors/temperature"
          method: "GET"
  
  device_registry:
    - device_id: "sensor-001"
      protocol: "mqtt"
      device_type: "temperature_sensor"
      location: "building-a/floor-1"
      capabilities: ["temperature", "humidity"]
      
    - device_id: "actuator-001"
      protocol: "modbus"
      device_type: "motor_controller"
      location: "factory-line-1"
      capabilities: ["start", "stop", "speed_control"]
```

#### 验证与度量

- **设备接入指标**：设备注册成功率 > 99%，连接稳定性 > 99.5%
- **数据采集指标**：数据采集准确率 > 99.9%，数据丢失率 < 0.1%
- **协议性能指标**：MQTT消息延迟 < 100ms，Modbus响应时间 < 50ms

#### 证据与引用

- **evidence:IOT-DEVICE-ACCESS**：Eclipse Mosquitto官方文档
- **交叉链接**：`docs/formal-model/interaction-model/protocol/theory.md`
- **标准对齐**：`L3_D01_交互标准模型.md`

### 案例二：边缘控制与实时调度

#### 场景与目标

- **业务场景**：工业自动化控制系统，需要实时响应和精确控制
- **技术目标**：实现边缘计算、实时调度、闭环控制
- **质量目标**：控制响应时间 < 10ms，系统可用性 > 99.9%

#### 术语与概念对齐

- **Edge Controller** ↔ `L3_D04_运行时标准模型.md` 边缘控制器
- **Real-time Scheduler** ↔ `L3_D07_控制调度标准模型.md` 实时调度器
- **Control Loop** ↔ `L3_D03_功能标准模型.md` 控制循环
- **Feedback System** ↔ `L3_D03_功能标准模型.md` 反馈系统

#### 结构与约束

- **实时性约束**：任务截止时间、响应时间保证、优先级调度
- **控制约束**：控制精度、稳定性、鲁棒性
- **资源约束**：计算资源、存储资源、网络带宽

#### 接口与 DSL 片段

```yaml
edge_control:
  real_time_scheduler:
    scheduling_policy: "EDF"
    time_slice: "1ms"
    tasks:
      - name: "sensor_read"
        period: "10ms"
        deadline: "10ms"
        priority: 10
        cpu_time: "2ms"
        
      - name: "control_calc"
        period: "20ms"
        deadline: "20ms"
        priority: 20
        cpu_time: "5ms"
        
      - name: "actuator_write"
        period: "20ms"
        deadline: "20ms"
        priority: 15
        cpu_time: "1ms"
  
  control_systems:
    - name: "temperature_control"
      type: "PID"
      parameters:
        kp: 1.0
        ki: 0.1
        kd: 0.01
      setpoint: 25.0
      input_sensor: "temp_sensor_001"
      output_actuator: "heater_001"
      
    - name: "pressure_control"
      type: "fuzzy"
      rules: "pressure_rules.fcl"
      input_sensor: "pressure_sensor_001"
      output_actuator: "valve_001"
```

#### 验证与度量

- **实时性指标**：任务调度成功率 > 99.9%，响应时间 < 10ms
- **控制精度**：控制误差 < 1%，系统稳定性 > 95%
- **系统可靠性**：系统可用性 > 99.9%，故障恢复时间 < 1s

#### 证据与引用

- **evidence:IOT-EDGE-RT**：EdgeX Foundry官方文档
- **交叉链接**：`docs/formal-model/runtime-model/orchestration/theory.md`
- **标准对齐**：`L3_D07_控制调度标准模型.md`

### 案例三：数据采集与离线回传

#### 场景与目标

- **业务场景**：远程监测系统，需要可靠的数据采集和离线缓存
- **技术目标**：实现数据采集、本地存储、批量上传、数据同步
- **质量目标**：数据完整性 > 99.99%，存储可靠性 > 99.9%

#### 术语与概念对齐

- **Data Collector** ↔ `L3_D02_数据标准模型.md` 数据收集器
- **Time Series DB** ↔ `L3_D02_数据标准模型.md` 时序数据库
- **Batch Upload** ↔ `L3_D01_交互标准模型.md` 批量上传
- **Data Sync** ↔ `L3_D02_数据标准模型.md` 数据同步

#### 结构与约束

- **数据完整性**：数据采集完整性、存储一致性、传输可靠性
- **存储约束**：存储容量、数据压缩、数据清理
- **同步约束**：数据一致性、冲突解决、版本管理

#### 接口与 DSL 片段

```yaml
data_collection:
  collectors:
    - name: "sensor_collector"
      data_sources:
        - sensor_id: "temp_001"
          sampling_rate: "1Hz"
          data_type: "float32"
        - sensor_id: "humidity_001"
          sampling_rate: "0.5Hz"
          data_type: "float32"
      storage:
        local_db: "influxdb"
        retention: "30d"
        compression: "gzip"
  
  batch_upload:
    schedule: "hourly"
    batch_size: 1000
    retry_policy:
      max_retries: 3
      backoff: "exponential"
    upload_targets:
      - endpoint: "https://api.iot.com/data"
        protocol: "https"
        authentication: "oauth2"
  
  data_sync:
    sync_strategy: "incremental"
    conflict_resolution: "timestamp_wins"
    sync_interval: "5m"
    sync_metrics:
      - name: "sync_success_rate"
        threshold: 0.99
      - name: "data_latency"
        threshold: "1h"
```

#### 验证与度量

- **数据完整性**：数据采集完整性 > 99.99%，数据丢失率 < 0.01%
- **存储性能**：写入性能 > 10000 points/s，查询延迟 < 100ms
- **同步效率**：同步成功率 > 99%，同步延迟 < 5分钟

#### 证据与引用

- **evidence:IOT-DATA-COLLECT**：InfluxDB官方文档
- **交叉链接**：`docs/formal-model/monitoring-model/theory.md`
- **标准对齐**：`L3_D06_监控标准模型.md`

## 4. 标准映射关系

### 4.1 与通用模型的映射

| IoT组件 | 通用模型映射 | 关键概念 |
|---------|-------------|---------|
| 设备接入 | L3_D01_交互标准模型 | 协议、消息、认证 |
| 边缘计算 | L3_D04_运行时标准模型 | 容器、编排、资源 |
| 数据采集 | L3_D02_数据标准模型 | 时序数据、存储、查询 |
| 实时控制 | L3_D07_控制调度标准模型 | 调度、控制、反馈 |
| 安全通信 | L3_D01_交互标准模型 | 加密、认证、授权 |

### 4.2 行业标准对齐

- **IoT标准**：MQTT、CoAP、OPC UA、Modbus等通信协议
- **边缘计算标准**：EdgeX Foundry、OpenYurt、K3s等平台
- **数据标准**：InfluxDB、TimescaleDB、OpenTSDB等时序数据库
- **安全标准**：TLS/SSL、DTLS、OAuth 2.0等安全协议

## 5. 最佳实践

### 5.1 设备接入最佳实践

- **协议选择**：根据应用场景选择合适的通信协议
- **设备管理**：建立完整的设备生命周期管理流程
- **安全认证**：实施设备身份认证和访问控制
- **监控告警**：建立设备状态监控和故障告警机制

### 5.2 边缘计算最佳实践

- **资源管理**：合理分配边缘计算资源
- **实时调度**：采用合适的实时调度算法
- **本地存储**：实现可靠的数据本地存储
- **故障恢复**：建立快速故障检测和恢复机制

### 5.3 数据管理最佳实践

- **数据质量**：建立数据质量检查和清洗流程
- **存储优化**：采用合适的数据压缩和存储策略
- **同步策略**：设计可靠的数据同步和备份机制
- **隐私保护**：实施数据脱敏和隐私保护措施

## 本行业权威来源一览

本行业与权威标准、课程及官方文档的对齐见下表；完整索引见 [reference/AUTHORITY_ALIGNMENT_INDEX](../../reference/AUTHORITY_ALIGNMENT_INDEX.md)。

| 类型 | 来源 | 与本行业映射 |
|------|------|--------------|
| 标准 | OPC UA、LwM2M、MQTT、ISO/IEC 27001 | 设备接入、数据采集、安全 |
| 课程 | 各校分布式系统、嵌入式/实时系统相关课程 | 见 AUTHORITY_ALIGNMENT_INDEX 第 3 节；ETH Distributed Systems |
| 官方文档 | EdgeX、KubeEdge、EMQX、ThingsBoard、Eclipse Mosquitto 等 | 见下方「本行业证据条目」 |

### 本行业证据条目

本行业相关 evidence 条目： [IOT-EDGEX-001](../../evidence/IOT-EDGEX-001.md)、[IOT-KUBEEDGE-001](../../evidence/IOT-KUBEEDGE-001.md)、[IOT-EMQX-001](../../evidence/IOT-EMQX-001.md)、[IOT-MOSQUITTO-001](../../evidence/IOT-MOSQUITTO-001.md)、[IOT-OPCUA-001](../../evidence/IOT-OPCUA-001.md)、[IOT-LWM2M-001](../../evidence/IOT-LWM2M-001.md)、[IOT-THINGSBOARD-001](../../evidence/IOT-THINGSBOARD-001.md)、[IOT-IOTDB-001](../../evidence/IOT-IOTDB-001.md)、[IOT-DATA-COLLECT](../../evidence/IOT-DATA-COLLECT.md)、[IOT-DEVICE-ACCESS](../../evidence/IOT-DEVICE-ACCESS.md)、[IOT-EDGE-RT](../../evidence/IOT-EDGE-RT.md)、[IOT-SMARTCITY-001](../../evidence/IOT-SMARTCITY-001.md)、[IOT-AGRICULTURE-001](../../evidence/IOT-AGRICULTURE-001.md) 等。更多见 [evidence/README](../../evidence/README.md)。
