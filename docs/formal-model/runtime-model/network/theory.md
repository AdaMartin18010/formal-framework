# 网络建模理论 (Network Modeling Theory)

## 目录（Table of Contents）

- [网络建模理论 (Network Modeling Theory)](#网络建模理论-network-modeling-theory)
  - [目录（Table of Contents）](#目录table-of-contents)
  - [概念定义](#概念定义)
    - [核心特征](#核心特征)
  - [理论基础](#理论基础)
    - [网络建模理论](#网络建模理论)
    - [网络设计层次理论](#网络设计层次理论)
  - [核心组件](#核心组件)
    - [网络拓扑模型](#网络拓扑模型)
    - [路由策略模型](#路由策略模型)
    - [负载均衡模型](#负载均衡模型)
    - [安全策略模型](#安全策略模型)
    - [性能优化模型](#性能优化模型)
  - [国际标准对标](#国际标准对标)
    - [网络协议标准](#网络协议标准)
      - [TCP/IP协议族](#tcpip协议族)
      - [路由协议标准](#路由协议标准)
      - [网络管理标准](#网络管理标准)
    - [软件定义网络标准](#软件定义网络标准)
      - [OpenFlow](#openflow)
      - [NETCONF/YANG](#netconfyang)
  - [著名大学课程对标](#著名大学课程对标)
    - [网络课程](#网络课程)
      - [MIT 6.033 - Computer System Engineering](#mit-6033---computer-system-engineering)
      - [Stanford CS144 - Introduction to Computer Networking](#stanford-cs144---introduction-to-computer-networking)
      - [CMU 15-441 - Computer Networks](#cmu-15-441---computer-networks)
    - [分布式系统课程](#分布式系统课程)
      - [MIT 6.824 - Distributed Systems](#mit-6824---distributed-systems)
  - [工程实践](#工程实践)
    - [网络设计模式](#网络设计模式)
      - [分层网络模式](#分层网络模式)
      - [软件定义网络模式](#软件定义网络模式)
    - [网络实现模式](#网络实现模式)
      - [高可用网络模式](#高可用网络模式)
      - [安全网络模式](#安全网络模式)
  - [最佳实践](#最佳实践)
    - [网络设计原则](#网络设计原则)
    - [网络实现原则](#网络实现原则)
    - [网络运维原则](#网络运维原则)
  - [应用案例](#应用案例)
    - [数据中心网络](#数据中心网络)
    - [云网络架构](#云网络架构)
  - [相关概念](#相关概念)
  - [参考文献](#参考文献)

## 概念定义

网络建模理论是一种形式化建模方法，用于描述和管理分布式系统中的网络架构和通信模式。它通过网络拓扑、路由策略、负载均衡、安全策略等方式，实现网络资源的优化配置和高效管理。

### 核心特征

1. **网络拓扑**：网络结构和连接关系的建模
2. **路由策略**：数据包路由和转发策略
3. **负载均衡**：网络流量分配和负载分散
4. **安全策略**：网络安全和访问控制
5. **性能优化**：网络性能和资源利用优化

## 理论基础

### 网络建模理论

网络建模基于以下理论：

```text
NetworkModel = (Topology, Routing, LoadBalancing, Security, Performance)
```

其中：

- Topology：网络拓扑（节点、链路、结构）
- Routing：路由策略（路径选择、转发规则）
- LoadBalancing：负载均衡（流量分配、资源调度）
- Security：安全策略（访问控制、加密传输）
- Performance：性能优化（带宽管理、延迟优化）

### 网络设计层次理论

```yaml
# 网络设计层次
network_design_hierarchy:
  physical_layer:
    - "物理连接"
    - "网络设备"
    - "传输介质"
    - "硬件配置"
    
  logical_layer:
    - "网络拓扑"
    - "IP地址规划"
    - "子网划分"
    - "路由配置"
    
  application_layer:
    - "服务发现"
    - "负载均衡"
    - "安全策略"
    - "监控告警"
    
  management_layer:
    - "配置管理"
    - "性能监控"
    - "故障处理"
    - "容量规划"
```

## 核心组件

### 网络拓扑模型

```yaml
# 网络拓扑定义
network_topology_definitions:
  - name: "mesh_topology"
    description: "网状拓扑"
    
    characteristics:
      - name: "connectivity"
        description: "连接性"
        value: "fully_connected"
        description: "每个节点都与其他节点直接连接"
        
      - name: "redundancy"
        description: "冗余性"
        value: "high"
        description: "高冗余，单点故障影响小"
        
      - name: "cost"
        description: "成本"
        value: "high"
        description: "连接数量多，成本高"
        
      - name: "scalability"
        description: "可扩展性"
        value: "low"
        description: "扩展时需要大量新连接"
        
    use_cases:
      - "数据中心内部网络"
      - "高可用性系统"
      - "关键业务网络"
      
  - name: "star_topology"
    description: "星形拓扑"
    
    characteristics:
      - name: "connectivity"
        description: "连接性"
        value: "centralized"
        description: "所有节点通过中心节点连接"
        
      - name: "redundancy"
        description: "冗余性"
        value: "low"
        description: "中心节点故障影响整个网络"
        
      - name: "cost"
        description: "成本"
        value: "low"
        description: "连接数量少，成本低"
        
      - name: "scalability"
        description: "可扩展性"
        value: "medium"
        description: "扩展时只需连接到中心节点"
        
    use_cases:
      - "小型办公网络"
      - "家庭网络"
      - "简单的分布式系统"
      
  - name: "ring_topology"
    description: "环形拓扑"
    
    characteristics:
      - name: "connectivity"
        description: "连接性"
        value: "circular"
        description: "节点形成环形连接"
        
      - name: "redundancy"
        description: "冗余性"
        value: "medium"
        description: "单点故障影响有限"
        
      - name: "cost"
        description: "成本"
        value: "medium"
        description: "连接数量适中"
        
      - name: "scalability"
        description: "可扩展性"
        value: "medium"
        description: "扩展时需要重新配置环形"
        
    use_cases:
      - "令牌环网络"
      - "光纤环网"
      - "分布式存储系统"
      
  - name: "tree_topology"
    description: "树形拓扑"
    
    characteristics:
      - name: "connectivity"
        description: "连接性"
        value: "hierarchical"
        description: "分层结构，树形连接"
        
      - name: "redundancy"
        description: "冗余性"
        value: "medium"
        description: "上级节点故障影响下级"
        
      - name: "cost"
        description: "成本"
        value: "medium"
        description: "连接数量适中"
        
      - name: "scalability"
        description: "可扩展性"
        value: "high"
        description: "易于扩展新分支"
        
    use_cases:
      - "企业网络"
      - "校园网络"
      - "分层管理系统"
```

### 路由策略模型

```yaml
# 路由策略定义
routing_strategy_definitions:
  - name: "static_routing"
    description: "静态路由"
    
    characteristics:
      - name: "configuration"
        description: "配置方式"
        value: "manual"
        description: "手动配置路由表"
        
      - name: "adaptability"
        description: "适应性"
        value: "low"
        description: "网络变化时需要手动更新"
        
      - name: "overhead"
        description: "开销"
        value: "low"
        description: "无路由协议开销"
        
      - name: "complexity"
        description: "复杂性"
        value: "low"
        description: "配置简单"
        
    use_cases:
      - "小型网络"
      - "稳定网络环境"
      - "安全要求高的网络"
      
  - name: "dynamic_routing"
    description: "动态路由"
    
    protocols:
      - name: "RIP"
        description: "路由信息协议"
        characteristics:
          - "距离向量协议"
          - "最大跳数15"
          - "30秒更新间隔"
          - "适用于小型网络"
          
      - name: "OSPF"
        description: "开放最短路径优先"
        characteristics:
          - "链路状态协议"
          - "分层设计"
          - "快速收敛"
          - "适用于大型网络"
          
      - name: "BGP"
        description: "边界网关协议"
        characteristics:
          - "路径向量协议"
          - "自治系统间路由"
          - "策略路由"
          - "互联网核心协议"
          
  - name: "software_defined_routing"
    description: "软件定义路由"
    
    characteristics:
      - name: "centralized_control"
        description: "集中控制"
        value: "high"
        description: "路由决策集中化"
        
      - name: "programmability"
        description: "可编程性"
        value: "high"
        description: "支持自定义路由策略"
        
      - name: "flexibility"
        description: "灵活性"
        value: "high"
        description: "快速适应网络变化"
        
      - name: "complexity"
        description: "复杂性"
        value: "high"
        description: "需要SDN控制器"
        
    use_cases:
      - "数据中心网络"
      - "云网络"
      - "企业网络"
```

### 负载均衡模型

```yaml
# 负载均衡定义
load_balancing_definitions:
  - name: "load_balancing_algorithms"
    description: "负载均衡算法"
    
    algorithms:
      - name: "round_robin"
        description: "轮询算法"
        characteristics:
          - "简单公平"
          - "无状态"
          - "均匀分布"
          - "不考虑服务器能力"
        use_cases:
          - "服务器能力相近"
          - "简单负载均衡"
          
      - name: "weighted_round_robin"
        description: "加权轮询"
        characteristics:
          - "考虑服务器权重"
          - "按权重分配"
          - "支持动态调整"
          - "相对公平"
        use_cases:
          - "服务器能力不同"
          - "需要权重控制"
          
      - name: "least_connections"
        description: "最少连接"
        characteristics:
          - "基于连接数"
          - "动态分配"
          - "负载均衡效果好"
          - "需要状态跟踪"
        use_cases:
          - "连接持续时间长"
          - "需要精确负载均衡"
          
      - name: "ip_hash"
        description: "IP哈希"
        characteristics:
          - "基于源IP"
          - "会话保持"
          - "简单高效"
          - "可能不均匀"
        use_cases:
          - "需要会话保持"
          - "缓存友好"
          
      - name: "least_response_time"
        description: "最少响应时间"
        characteristics:
          - "基于响应时间"
          - "性能优化"
          - "需要监控"
          - "复杂实现"
        use_cases:
          - "性能敏感应用"
          - "需要最优响应"
          
  - name: "load_balancing_modes"
    description: "负载均衡模式"
    
    modes:
      - name: "layer_4_load_balancing"
        description: "四层负载均衡"
        characteristics:
          - "基于IP和端口"
          - "高性能"
          - "简单实现"
          - "无应用层感知"
        protocols:
          - "TCP"
          - "UDP"
        use_cases:
          - "高性能要求"
          - "简单协议"
          
      - name: "layer_7_load_balancing"
        description: "七层负载均衡"
        characteristics:
          - "基于应用层信息"
          - "智能路由"
          - "功能丰富"
          - "性能较低"
        protocols:
          - "HTTP"
          - "HTTPS"
          - "FTP"
        use_cases:
          - "复杂路由需求"
          - "应用层优化"
          
      - name: "global_load_balancing"
        description: "全局负载均衡"
        characteristics:
          - "跨地域"
          - "基于地理位置"
          - "高可用性"
          - "复杂配置"
        strategies:
          - "地理位置"
          - "延迟"
          - "可用性"
        use_cases:
          - "全球服务"
          - "灾难恢复"
```

### 安全策略模型

```yaml
# 安全策略定义
security_strategy_definitions:
  - name: "network_security_zones"
    description: "网络安全区域"
    
    zones:
      - name: "public_zone"
        description: "公共区域"
        characteristics:
          - "面向互联网"
          - "高风险"
          - "严格访问控制"
          - "DMZ部署"
        services:
          - "Web服务器"
          - "邮件服务器"
          - "DNS服务器"
          
      - name: "private_zone"
        description: "私有区域"
        characteristics:
          - "内部网络"
          - "中等风险"
          - "适度访问控制"
          - "应用服务器"
        services:
          - "应用服务器"
          - "数据库服务器"
          - "文件服务器"
          
      - name: "secure_zone"
        description: "安全区域"
        characteristics:
          - "高安全要求"
          - "低风险"
          - "严格隔离"
          - "专用网络"
        services:
          - "核心数据库"
          - "身份认证"
          - "密钥管理"
          
  - name: "access_control_policies"
    description: "访问控制策略"
    
    policies:
      - name: "firewall_rules"
        description: "防火墙规则"
        types:
          - name: "packet_filtering"
            description: "包过滤"
            characteristics:
              - "基于IP和端口"
              - "高性能"
              - "简单规则"
            use_cases:
              - "基本访问控制"
              - "高性能要求"
              
          - name: "stateful_inspection"
            description: "状态检查"
            characteristics:
              - "跟踪连接状态"
              - "更安全"
              - "中等性能"
            use_cases:
              - "企业网络"
              - "安全要求高"
              
          - name: "application_layer_gateway"
            description: "应用层网关"
            characteristics:
              - "应用层检查"
              - "最安全"
              - "性能较低"
            use_cases:
              - "高安全要求"
              - "应用层保护"
              
      - name: "network_segmentation"
        description: "网络分段"
        strategies:
          - name: "vlan_segmentation"
            description: "VLAN分段"
            characteristics:
              - "二层隔离"
              - "简单实现"
              - "广播域隔离"
            use_cases:
              - "部门隔离"
              - "广播控制"
              
          - name: "subnet_segmentation"
            description: "子网分段"
            characteristics:
              - "三层隔离"
              - "路由控制"
              - "安全策略"
            use_cases:
              - "安全区域"
              - "访问控制"
              
          - name: "micro_segmentation"
            description: "微分段"
            characteristics:
              - "细粒度控制"
              - "零信任"
              - "复杂配置"
            use_cases:
              - "数据中心"
              - "高安全要求"
```

### 性能优化模型

```yaml
# 性能优化定义
performance_optimization_definitions:
  - name: "bandwidth_management"
    description: "带宽管理"
    
    strategies:
      - name: "traffic_shaping"
        description: "流量整形"
        characteristics:
          - "平滑流量"
          - "减少突发"
          - "提高稳定性"
          - "可能增加延迟"
        techniques:
          - "令牌桶"
          - "漏桶算法"
          - "队列管理"
          
      - name: "traffic_policing"
        description: "流量监管"
        characteristics:
          - "限制流量"
          - "丢弃超限"
          - "简单实现"
          - "可能丢包"
        techniques:
          - "速率限制"
          - "突发限制"
          - "优先级控制"
          
      - name: "quality_of_service"
        description: "服务质量"
        characteristics:
          - "差异化服务"
          - "优先级保证"
          - "复杂配置"
          - "端到端保证"
        classes:
          - "实时流量"
          - "交互流量"
          - "批量流量"
          - "尽力而为"
          
  - name: "latency_optimization"
    description: "延迟优化"
    
    strategies:
      - name: "route_optimization"
        description: "路由优化"
        techniques:
          - "最短路径"
          - "延迟感知"
          - "拥塞避免"
          - "动态调整"
        use_cases:
          - "实时应用"
          - "游戏服务"
          - "视频会议"
          
      - name: "caching_strategies"
        description: "缓存策略"
        techniques:
          - "CDN缓存"
          - "本地缓存"
          - "代理缓存"
          - "分布式缓存"
        use_cases:
          - "静态内容"
          - "频繁访问"
          - "带宽节省"
          
      - name: "compression_optimization"
        description: "压缩优化"
        techniques:
          - "数据压缩"
          - "图像压缩"
          - "视频压缩"
          - "协议压缩"
        use_cases:
          - "带宽受限"
          - "移动网络"
          - "成本优化"
```

## 国际标准对标

### 网络协议标准

#### TCP/IP协议族

- **标准**：RFC 791 (IP), RFC 793 (TCP), RFC 768 (UDP)
- **核心概念**：网络层、传输层、应用层协议
- **理论基础**：网络协议栈、分层架构
- **工具支持**：Wireshark、tcpdump、netstat

#### 路由协议标准

- **标准**：RFC 2453 (RIP), RFC 2328 (OSPF), RFC 4271 (BGP)
- **核心概念**：路由算法、路径选择、网络收敛
- **理论基础**：图论、最短路径算法
- **工具支持**：Quagga、BIRD、Cisco IOS

#### 网络管理标准

- **标准**：RFC 3411-3418 (SNMP), RFC 2863 (MIB)
- **核心概念**：网络监控、设备管理、性能统计
- **理论基础**：网络管理、监控系统
- **工具支持**：SNMP工具、网络管理系统

### 软件定义网络标准

#### OpenFlow

- **标准**：OpenFlow 1.5
- **核心概念**：流表、控制器、数据平面
- **理论基础**：软件定义网络、集中控制
- **工具支持**：Open vSwitch、Floodlight、ONOS

#### NETCONF/YANG

- **标准**：RFC 6241 (NETCONF), RFC 6020 (YANG)
- **核心概念**：网络配置、数据建模、自动化
- **理论基础**：网络自动化、配置管理
- **工具支持**：NETCONF工具、YANG编译器

## 著名大学课程对标

### 网络课程

#### MIT 6.033 - Computer System Engineering

- **课程内容**：计算机系统工程、网络设计、分布式系统
- **网络建模相关**：网络架构、协议设计、系统集成
- **实践项目**：网络协议实现和测试
- **相关技术**：TCP/IP、网络编程、系统设计

#### Stanford CS144 - Introduction to Computer Networking

- **课程内容**：计算机网络、协议设计、网络编程
- **网络建模相关**：网络协议、路由算法、网络编程
- **实践项目**：TCP协议实现
- **相关技术**：网络协议、Socket编程、网络分析

#### CMU 15-441 - Computer Networks

- **课程内容**：计算机网络、协议设计、网络应用
- **网络建模相关**：网络设计、协议实现、性能分析
- **实践项目**：网络协议和应用程序开发
- **相关技术**：网络协议、分布式系统、性能优化

### 分布式系统课程

#### MIT 6.824 - Distributed Systems

- **课程内容**：分布式系统、一致性、容错
- **网络建模相关**：网络通信、分布式算法、容错机制
- **实践项目**：分布式系统实现
- **相关技术**：RPC、网络协议、分布式算法

## 工程实践

### 网络设计模式

#### 分层网络模式

```yaml
# 分层网络模式
layered_network_pattern:
  description: "分层网络设计模式"
  structure:
    - name: "接入层"
      description: "用户接入"
      components:
        - "交换机"
        - "无线AP"
        - "用户设备"
      functions:
        - "用户接入"
        - "VLAN隔离"
        - "端口安全"
        
    - name: "汇聚层"
      description: "流量汇聚"
      components:
        - "三层交换机"
        - "路由器"
        - "防火墙"
      functions:
        - "流量汇聚"
        - "路由转发"
        - "安全控制"
        
    - name: "核心层"
      description: "高速转发"
      components:
        - "核心交换机"
        - "骨干路由器"
        - "负载均衡器"
      functions:
        - "高速转发"
        - "负载均衡"
        - "冗余备份"
        
  benefits:
    - "模块化设计"
    - "易于扩展"
    - "故障隔离"
    - "管理简单"
    
  use_cases:
    - "企业网络"
    - "校园网络"
    - "数据中心"
```

#### 软件定义网络模式

```yaml
# 软件定义网络模式
software_defined_network_pattern:
  description: "软件定义网络模式"
  structure:
    - name: "应用层"
      description: "网络应用"
      components:
        - "网络应用"
        - "编排系统"
        - "管理平台"
      functions:
        - "业务逻辑"
        - "策略定义"
        - "用户界面"
        
    - name: "控制层"
      description: "网络控制"
      components:
        - "SDN控制器"
        - "路由引擎"
        - "策略引擎"
      functions:
        - "集中控制"
        - "路由计算"
        - "策略执行"
        
    - name: "数据层"
      description: "数据转发"
      components:
        - "网络设备"
        - "虚拟交换机"
        - "转发引擎"
      functions:
        - "数据转发"
        - "流表匹配"
        - "动作执行"
        
  benefits:
    - "集中控制"
    - "可编程性"
    - "灵活性"
    - "自动化"
    
  use_cases:
    - "数据中心"
    - "云网络"
    - "企业网络"
```

### 网络实现模式

#### 高可用网络模式

```yaml
# 高可用网络模式
high_availability_network_pattern:
  description: "高可用网络实现模式"
  strategies:
    - name: "设备冗余"
      description: "设备级冗余"
      components:
        - "主备设备"
        - "负载分担"
        - "故障切换"
      techniques:
        - "VRRP"
        - "HSRP"
        - "GLBP"
        
    - name: "链路冗余"
      description: "链路级冗余"
      components:
        - "多条链路"
        - "链路聚合"
        - "路径备份"
      techniques:
        - "链路聚合"
        - "多路径"
        - "快速收敛"
        
    - name: "路径冗余"
      description: "路径级冗余"
      components:
        - "多条路径"
        - "动态路由"
        - "路径优化"
      techniques:
        - "动态路由"
        - "路径计算"
        - "负载分担"
        
  benefits:
    - "高可用性"
    - "故障恢复"
    - "负载分担"
    - "性能优化"
    
  use_cases:
    - "关键业务"
    - "数据中心"
    - "企业网络"
```

#### 安全网络模式

```yaml
# 安全网络模式
secure_network_pattern:
  description: "安全网络实现模式"
  strategies:
    - name: "纵深防御"
      description: "多层安全防护"
      layers:
        - "物理安全"
        - "网络安全"
        - "主机安全"
        - "应用安全"
      techniques:
        - "防火墙"
        - "入侵检测"
        - "访问控制"
        - "加密传输"
        
    - name: "零信任网络"
      description: "零信任安全模型"
      principles:
        - "永不信任"
        - "始终验证"
        - "最小权限"
      components:
        - "身份认证"
        - "设备验证"
        - "网络分段"
        - "持续监控"
        
    - name: "安全隔离"
      description: "网络安全隔离"
      techniques:
        - "VLAN隔离"
        - "子网隔离"
        - "微分段"
        - "物理隔离"
        
  benefits:
    - "安全防护"
    - "风险控制"
    - "合规要求"
    - "威胁防护"
    
  use_cases:
    - "金融网络"
    - "政府网络"
    - "企业网络"
```

## 最佳实践

### 网络设计原则

1. **模块化设计**：网络应该采用模块化设计
2. **分层架构**：使用分层架构简化管理
3. **冗余设计**：关键组件应该有冗余
4. **安全优先**：安全应该贯穿整个设计

### 网络实现原则

1. **标准化**：使用标准协议和技术
2. **可扩展性**：设计应该支持未来扩展
3. **可管理性**：网络应该易于管理
4. **性能优化**：关注网络性能指标

### 网络运维原则

1. **监控告警**：建立完善的监控体系
2. **文档管理**：维护详细的网络文档
3. **变更管理**：建立变更管理流程
4. **备份恢复**：建立备份和恢复机制

## 应用案例

### 数据中心网络

```yaml
# 数据中心网络
data_center_network:
  description: "数据中心网络架构"
  components:
    - name: "接入层"
      description: "服务器接入"
      design:
        - "ToR交换机"
        - "服务器直连"
        - "VLAN隔离"
      features:
        - "高密度端口"
        - "低延迟"
        - "简单管理"
        
    - name: "汇聚层"
      description: "流量汇聚"
      design:
        - "三层交换机"
        - "路由转发"
        - "负载均衡"
      features:
        - "高带宽"
        - "路由功能"
        - "冗余设计"
        
    - name: "核心层"
      description: "高速转发"
      design:
        - "核心交换机"
        - "骨干连接"
        - "冗余备份"
      features:
        - "超高带宽"
        - "低延迟"
        - "高可用性"
        
    - name: "管理网络"
      description: "管理网络"
      design:
        - "带外管理"
        - "管理VLAN"
        - "安全隔离"
      features:
        - "独立网络"
        - "安全访问"
        - "集中管理"
```

### 云网络架构

```yaml
# 云网络架构
cloud_network_architecture:
  description: "云网络架构设计"
  components:
    - name: "虚拟网络"
      description: "虚拟网络层"
      technologies:
        - "VXLAN"
        - "NVGRE"
        - "Geneve"
      features:
        - "网络虚拟化"
        - "租户隔离"
        - "灵活配置"
        
    - name: "SDN控制器"
      description: "软件定义网络"
      technologies:
        - "OpenFlow"
        - "OVSDB"
        - "NETCONF"
      features:
        - "集中控制"
        - "可编程性"
        - "自动化"
        
    - name: "负载均衡"
      description: "负载均衡服务"
      technologies:
        - "L4负载均衡"
        - "L7负载均衡"
        - "全局负载均衡"
      features:
        - "高可用性"
        - "自动扩展"
        - "健康检查"
        
    - name: "安全服务"
      description: "网络安全服务"
      technologies:
        - "安全组"
        - "网络ACL"
        - "DDoS防护"
      features:
        - "多层防护"
        - "自动防护"
        - "实时监控"
```

## 相关概念

- [容器建模](../container/theory.md)
- [编排建模](../orchestration/theory.md)
- [存储建模](../storage/theory.md)
- [运行时建模](../theory.md)

## 参考文献

1. Tanenbaum, A. S. (2010). "Computer Networks"
2. Kurose, J. F., & Ross, K. W. (2017). "Computer Networking: A Top-Down Approach"
3. Peterson, L. L., & Davie, B. S. (2011). "Computer Networks: A Systems Approach"
4. RFC 791 (1981). "Internet Protocol"
5. RFC 793 (1981). "Transmission Control Protocol"
6. OpenFlow Specification (2023). "OpenFlow Switch Specification"

## 与标准/课程对照要点

- **L2/L3 映射**：网络建模属运行时域，对应 [L2_D04 运行时元模型](../../../L2_D04_运行时元模型.md)、[L3_D04 运行时标准模型](../../../L3_D04_运行时标准模型.md)；对象/属性/不变式见 [alignment-L2-L3-matrix](../../alignment-L2-L3-matrix.md)。
- **标准与课程**：运行时与网络相关标准及课程对照见 [AUTHORITY_STANDARD_COURSE_L2L3_MATRIX](../../../reference/AUTHORITY_STANDARD_COURSE_L2L3_MATRIX.md)、[AUTHORITY_ALIGNMENT_INDEX](../../../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 2–4 节。
