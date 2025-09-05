# 运行时标准模型

## 概述

运行时标准模型定义了系统运行时环境的标准化实现，基于运行时元模型构建，提供统一的运行时管理、资源调度和性能优化机制。

## 标准运行时环境

### 1. 容器运行时

#### 标准容器配置

```yaml
ContainerRuntime:
  base_image: "alpine:3.18"
  runtime: "containerd"
  security:
    user: "1000:1000"
    capabilities:
      - "NET_BIND_SERVICE"
    seccomp_profile: "runtime/default"
  resources:
    limits:
      cpu: "1000m"
      memory: "512Mi"
    requests:
      cpu: "100m"
      memory: "128Mi"
  health_check:
    command: ["/bin/sh", "-c", "curl -f http://localhost:8080/health || exit 1"]
    interval: 30s
    timeout: 10s
    retries: 3
```

#### 实现示例

```python
import docker
from typing import Dict, Any, List
import yaml

class ContainerRuntime:
    """标准容器运行时"""
    
    def __init__(self, docker_client: docker.DockerClient):
        self.client = docker_client
    
    def create_container(self, config: Dict[str, Any]) -> str:
        """创建标准容器"""
        container_config = {
            "image": config["base_image"],
            "command": config.get("command"),
            "environment": config.get("environment", {}),
            "ports": config.get("ports", {}),
            "volumes": config.get("volumes", {}),
            "user": config.get("security", {}).get("user"),
            "mem_limit": config.get("resources", {}).get("limits", {}).get("memory"),
            "cpu_quota": self._parse_cpu_limit(
                config.get("resources", {}).get("limits", {}).get("cpu")
            ),
            "healthcheck": self._create_healthcheck(
                config.get("health_check", {})
            )
        }
        
        container = self.client.containers.run(**container_config, detach=True)
        return container.id
    
    def _parse_cpu_limit(self, cpu_limit: str) -> int:
        """解析CPU限制"""
        if not cpu_limit:
            return 0
        
        if cpu_limit.endswith('m'):
            return int(cpu_limit[:-1]) * 1000
        else:
            return int(float(cpu_limit) * 1000)
    
    def _create_healthcheck(self, health_config: Dict[str, Any]) -> Dict[str, Any]:
        """创建健康检查配置"""
        if not health_config:
            return None
        
        return {
            "test": health_config.get("command"),
            "interval": health_config.get("interval", 30),
            "timeout": health_config.get("timeout", 10),
            "retries": health_config.get("retries", 3)
        }
```

### 2. 虚拟机运行时

#### 标准虚拟机配置

```yaml
VirtualMachineRuntime:
  hypervisor: "kvm"
  cpu:
    cores: 2
    model: "host-passthrough"
  memory:
    size: "4Gi"
    balloon: true
  storage:
    type: "qcow2"
    size: "20Gi"
    cache: "writeback"
  network:
    type: "bridge"
    bridge: "virbr0"
  security:
    secure_boot: true
    tpm: true
```

#### 实现示例1

```python
import libvirt
from typing import Dict, Any
import xml.etree.ElementTree as ET

class VirtualMachineRuntime:
    """标准虚拟机运行时"""
    
    def __init__(self, connection_uri: str = "qemu:///system"):
        self.conn = libvirt.open(connection_uri)
    
    def create_vm(self, config: Dict[str, Any]) -> str:
        """创建标准虚拟机"""
        xml_config = self._generate_vm_xml(config)
        domain = self.conn.defineXML(xml_config)
        domain.create()
        return domain.UUIDString()
    
    def _generate_vm_xml(self, config: Dict[str, Any]) -> str:
        """生成虚拟机XML配置"""
        root = ET.Element("domain", type="kvm")
        
        # 基本信息
        name = ET.SubElement(root, "name")
        name.text = config.get("name", "standard-vm")
        
        memory = ET.SubElement(root, "memory", unit="KiB")
        memory.text = str(self._parse_memory(config.get("memory", {}).get("size", "4Gi")))
        
        vcpu = ET.SubElement(root, "vcpu")
        vcpu.text = str(config.get("cpu", {}).get("cores", 2))
        
        # CPU配置
        cpu = ET.SubElement(root, "cpu", mode="host-passthrough")
        
        # 存储配置
        devices = ET.SubElement(root, "devices")
        disk = ET.SubElement(devices, "disk", type="file", device="disk")
        driver = ET.SubElement(disk, "driver", name="qemu", type="qcow2")
        source = ET.SubElement(disk, "source", file=config.get("storage", {}).get("path"))
        target = ET.SubElement(disk, "target", dev="vda", bus="virtio")
        
        # 网络配置
        interface = ET.SubElement(devices, "interface", type="bridge")
        source = ET.SubElement(interface, "source", bridge=config.get("network", {}).get("bridge", "virbr0"))
        model = ET.SubElement(interface, "model", type="virtio")
        
        return ET.tostring(root, encoding="unicode")
    
    def _parse_memory(self, memory_str: str) -> int:
        """解析内存大小"""
        if memory_str.endswith('Gi'):
            return int(memory_str[:-2]) * 1024 * 1024
        elif memory_str.endswith('Mi'):
            return int(memory_str[:-2]) * 1024
        else:
            return int(memory_str)
```

### 3. 无服务器运行时

#### 标准函数配置

```yaml
ServerlessRuntime:
  runtime: "python3.9"
  handler: "main.handler"
  timeout: 30s
  memory: "256Mi"
  environment:
    NODE_ENV: "production"
    LOG_LEVEL: "info"
  triggers:
    - type: "http"
      path: "/api/function"
      method: "POST"
    - type: "cron"
      schedule: "0 0 * * *"
  vpc:
    security_groups: ["sg-12345"]
    subnets: ["subnet-12345"]
```

#### 实现示例2

```python
import boto3
from typing import Dict, Any, List
import json

class ServerlessRuntime:
    """标准无服务器运行时"""
    
    def __init__(self, region: str = "us-east-1"):
        self.lambda_client = boto3.client('lambda', region_name=region)
        self.events_client = boto3.client('events', region_name=region)
    
    def deploy_function(self, config: Dict[str, Any], code_zip: bytes) -> str:
        """部署标准函数"""
        function_config = {
            "FunctionName": config.get("name"),
            "Runtime": config.get("runtime", "python3.9"),
            "Role": config.get("role_arn"),
            "Handler": config.get("handler", "main.handler"),
            "Code": {"ZipFile": code_zip},
            "Timeout": self._parse_timeout(config.get("timeout", "30s")),
            "MemorySize": self._parse_memory(config.get("memory", "256Mi")),
            "Environment": {
                "Variables": config.get("environment", {})
            }
        }
        
        if config.get("vpc"):
            function_config["VpcConfig"] = {
                "SecurityGroupIds": config["vpc"].get("security_groups", []),
                "SubnetIds": config["vpc"].get("subnets", [])
            }
        
        response = self.lambda_client.create_function(**function_config)
        
        # 配置触发器
        for trigger in config.get("triggers", []):
            self._create_trigger(config.get("name"), trigger)
        
        return response["FunctionArn"]
    
    def _parse_timeout(self, timeout_str: str) -> int:
        """解析超时时间"""
        if timeout_str.endswith('s'):
            return int(timeout_str[:-1])
        elif timeout_str.endswith('m'):
            return int(timeout_str[:-1]) * 60
        else:
            return int(timeout_str)
    
    def _parse_memory(self, memory_str: str) -> int:
        """解析内存大小"""
        if memory_str.endswith('Mi'):
            return int(memory_str[:-2])
        elif memory_str.endswith('Gi'):
            return int(memory_str[:-2]) * 1024
        else:
            return int(memory_str)
    
    def _create_trigger(self, function_name: str, trigger_config: Dict[str, Any]):
        """创建触发器"""
        trigger_type = trigger_config.get("type")
        
        if trigger_type == "http":
            # 创建API Gateway触发器
            pass
        elif trigger_type == "cron":
            # 创建EventBridge规则
            rule_name = f"{function_name}-cron"
            self.events_client.put_rule(
                Name=rule_name,
                ScheduleExpression=f"cron({trigger_config.get('schedule')})"
            )
            self.events_client.put_targets(
                Rule=rule_name,
                Targets=[{
                    "Id": "1",
                    "Arn": f"arn:aws:lambda:{self.region}:{self.account}:function:{function_name}"
                }]
            )
```

## 标准资源管理

### 1. 资源调度器

#### 标准调度策略

```yaml
SchedulingPolicy:
  algorithms:
    - "round_robin"
    - "least_connections"
    - "weighted_round_robin"
    - "ip_hash"
  constraints:
    - type: "node_affinity"
      key: "zone"
      operator: "In"
      values: ["us-east-1a", "us-east-1b"]
    - type: "resource_requirements"
      cpu: "100m"
      memory: "128Mi"
  scaling:
    min_replicas: 1
    max_replicas: 10
    target_cpu_utilization: 70
    target_memory_utilization: 80
```

#### 实现示例3

```python
from typing import List, Dict, Any, Optional
from dataclasses import dataclass
from enum import Enum

class SchedulingAlgorithm(Enum):
    ROUND_ROBIN = "round_robin"
    LEAST_CONNECTIONS = "least_connections"
    WEIGHTED_ROUND_ROBIN = "weighted_round_robin"
    IP_HASH = "ip_hash"

@dataclass
class ResourceRequirement:
    cpu: str
    memory: str
    storage: Optional[str] = None

@dataclass
class Node:
    id: str
    zone: str
    available_cpu: str
    available_memory: str
    labels: Dict[str, str]

class ResourceScheduler:
    """标准资源调度器"""
    
    def __init__(self, algorithm: SchedulingAlgorithm = SchedulingAlgorithm.ROUND_ROBIN):
        self.algorithm = algorithm
        self.nodes: List[Node] = []
        self.round_robin_index = 0
    
    def add_node(self, node: Node):
        """添加节点"""
        self.nodes.append(node)
    
    def schedule_pod(self, requirements: ResourceRequirement, constraints: List[Dict[str, Any]] = None) -> Optional[str]:
        """调度Pod到节点"""
        suitable_nodes = self._filter_nodes(requirements, constraints or [])
        
        if not suitable_nodes:
            return None
        
        if self.algorithm == SchedulingAlgorithm.ROUND_ROBIN:
            return self._round_robin_schedule(suitable_nodes)
        elif self.algorithm == SchedulingAlgorithm.LEAST_CONNECTIONS:
            return self._least_connections_schedule(suitable_nodes)
        elif self.algorithm == SchedulingAlgorithm.WEIGHTED_ROUND_ROBIN:
            return self._weighted_round_robin_schedule(suitable_nodes)
        elif self.algorithm == SchedulingAlgorithm.IP_HASH:
            return self._ip_hash_schedule(suitable_nodes)
        
        return None
    
    def _filter_nodes(self, requirements: ResourceRequirement, constraints: List[Dict[str, Any]]) -> List[Node]:
        """过滤符合条件的节点"""
        suitable_nodes = []
        
        for node in self.nodes:
            # 检查资源需求
            if not self._check_resource_requirements(node, requirements):
                continue
            
            # 检查约束条件
            if not self._check_constraints(node, constraints):
                continue
            
            suitable_nodes.append(node)
        
        return suitable_nodes
    
    def _check_resource_requirements(self, node: Node, requirements: ResourceRequirement) -> bool:
        """检查资源需求"""
        # 简化的资源检查逻辑
        return True  # 实际实现中需要解析和比较资源
    
    def _check_constraints(self, node: Node, constraints: List[Dict[str, Any]]) -> bool:
        """检查约束条件"""
        for constraint in constraints:
            if constraint["type"] == "node_affinity":
                if not self._check_node_affinity(node, constraint):
                    return False
        return True
    
    def _check_node_affinity(self, node: Node, constraint: Dict[str, Any]) -> bool:
        """检查节点亲和性"""
        key = constraint["key"]
        operator = constraint["operator"]
        values = constraint["values"]
        
        node_value = node.labels.get(key)
        
        if operator == "In":
            return node_value in values
        elif operator == "NotIn":
            return node_value not in values
        elif operator == "Exists":
            return key in node.labels
        elif operator == "DoesNotExist":
            return key not in node.labels
        
        return False
    
    def _round_robin_schedule(self, nodes: List[Node]) -> str:
        """轮询调度"""
        if not nodes:
            return None
        
        selected_node = nodes[self.round_robin_index % len(nodes)]
        self.round_robin_index += 1
        return selected_node.id
    
    def _least_connections_schedule(self, nodes: List[Node]) -> str:
        """最少连接调度"""
        # 简化实现，实际需要跟踪连接数
        return nodes[0].id if nodes else None
    
    def _weighted_round_robin_schedule(self, nodes: List[Node]) -> str:
        """加权轮询调度"""
        # 简化实现，实际需要根据权重计算
        return nodes[0].id if nodes else None
    
    def _ip_hash_schedule(self, nodes: List[Node]) -> str:
        """IP哈希调度"""
        # 简化实现，实际需要根据客户端IP计算哈希
        return nodes[0].id if nodes else None
```

### 2. 资源监控

#### 标准监控指标

```yaml
ResourceMetrics:
  cpu:
    usage_percent: "gauge"
    load_average: "gauge"
    context_switches: "counter"
  
  memory:
    usage_bytes: "gauge"
    available_bytes: "gauge"
    swap_usage_bytes: "gauge"
  
  disk:
    usage_percent: "gauge"
    read_iops: "counter"
    write_iops: "counter"
    read_throughput: "counter"
    write_throughput: "counter"
  
  network:
    bytes_sent: "counter"
    bytes_received: "counter"
    packets_sent: "counter"
    packets_received: "counter"
    connection_count: "gauge"
```

#### 实现示例4

```python
import psutil
import time
from typing import Dict, Any, List
from dataclasses import dataclass
from prometheus_client import Gauge, Counter, start_http_server

@dataclass
class ResourceMetrics:
    cpu_usage_percent: float
    memory_usage_bytes: int
    memory_available_bytes: int
    disk_usage_percent: float
    network_bytes_sent: int
    network_bytes_received: int

class ResourceMonitor:
    """标准资源监控器"""
    
    def __init__(self, port: int = 8000):
        self.port = port
        self.metrics = self._init_metrics()
        self.previous_network_stats = None
    
    def _init_metrics(self) -> Dict[str, Any]:
        """初始化监控指标"""
        return {
            "cpu_usage_percent": Gauge("cpu_usage_percent", "CPU使用率百分比"),
            "memory_usage_bytes": Gauge("memory_usage_bytes", "内存使用字节数"),
            "memory_available_bytes": Gauge("memory_available_bytes", "可用内存字节数"),
            "disk_usage_percent": Gauge("disk_usage_percent", "磁盘使用率百分比"),
            "network_bytes_sent": Counter("network_bytes_sent_total", "网络发送字节数"),
            "network_bytes_received": Counter("network_bytes_received_total", "网络接收字节数"),
        }
    
    def start_monitoring(self):
        """开始监控"""
        start_http_server(self.port)
        
        while True:
            metrics = self.collect_metrics()
            self.update_metrics(metrics)
            time.sleep(10)  # 每10秒收集一次
    
    def collect_metrics(self) -> ResourceMetrics:
        """收集资源指标"""
        # CPU指标
        cpu_usage = psutil.cpu_percent(interval=1)
        
        # 内存指标
        memory = psutil.virtual_memory()
        
        # 磁盘指标
        disk = psutil.disk_usage('/')
        disk_usage_percent = (disk.used / disk.total) * 100
        
        # 网络指标
        network_stats = psutil.net_io_counters()
        
        return ResourceMetrics(
            cpu_usage_percent=cpu_usage,
            memory_usage_bytes=memory.used,
            memory_available_bytes=memory.available,
            disk_usage_percent=disk_usage_percent,
            network_bytes_sent=network_stats.bytes_sent,
            network_bytes_received=network_stats.bytes_recv
        )
    
    def update_metrics(self, metrics: ResourceMetrics):
        """更新监控指标"""
        self.metrics["cpu_usage_percent"].set(metrics.cpu_usage_percent)
        self.metrics["memory_usage_bytes"].set(metrics.memory_usage_bytes)
        self.metrics["memory_available_bytes"].set(metrics.memory_available_bytes)
        self.metrics["disk_usage_percent"].set(metrics.disk_usage_percent)
        
        # 网络指标需要计算增量
        if self.previous_network_stats:
            sent_delta = metrics.network_bytes_sent - self.previous_network_stats.bytes_sent
            received_delta = metrics.network_bytes_received - self.previous_network_stats.bytes_recv
            
            self.metrics["network_bytes_sent"].inc(sent_delta)
            self.metrics["network_bytes_received"].inc(received_delta)
        
        self.previous_network_stats = psutil.net_io_counters()
```

## 标准性能优化

### 1. 自动扩缩容

#### 扩缩容策略

```yaml
AutoScalingPolicy:
  horizontal:
    min_replicas: 1
    max_replicas: 10
    target_cpu_utilization: 70
    target_memory_utilization: 80
    scale_up_cooldown: 300s
    scale_down_cooldown: 600s
  
  vertical:
    min_cpu: "100m"
    max_cpu: "2000m"
    min_memory: "128Mi"
    max_memory: "4Gi"
    adjustment_step: "100m"
```

#### 实现示例5

```python
import time
from typing import Dict, Any, List
from dataclasses import dataclass
from enum import Enum

class ScalingDirection(Enum):
    SCALE_UP = "scale_up"
    SCALE_DOWN = "scale_down"
    NO_SCALE = "no_scale"

@dataclass
class ScalingDecision:
    direction: ScalingDirection
    target_replicas: int
    reason: str

class AutoScaler:
    """标准自动扩缩容器"""
    
    def __init__(self, policy: Dict[str, Any]):
        self.policy = policy
        self.current_replicas = policy.get("horizontal", {}).get("min_replicas", 1)
        self.last_scale_time = 0
    
    def should_scale(self, current_metrics: Dict[str, float]) -> ScalingDecision:
        """判断是否需要扩缩容"""
        horizontal_policy = self.policy.get("horizontal", {})
        
        # 检查冷却时间
        if not self._is_cooldown_ready(horizontal_policy):
            return ScalingDecision(ScalingDirection.NO_SCALE, self.current_replicas, "冷却时间未到")
        
        # 检查CPU使用率
        cpu_utilization = current_metrics.get("cpu_usage_percent", 0)
        target_cpu = horizontal_policy.get("target_cpu_utilization", 70)
        
        if cpu_utilization > target_cpu:
            return self._decide_scale_up(horizontal_policy, "CPU使用率过高")
        elif cpu_utilization < target_cpu * 0.5:  # 低于目标值50%时缩容
            return self._decide_scale_down(horizontal_policy, "CPU使用率过低")
        
        # 检查内存使用率
        memory_utilization = current_metrics.get("memory_usage_percent", 0)
        target_memory = horizontal_policy.get("target_memory_utilization", 80)
        
        if memory_utilization > target_memory:
            return self._decide_scale_up(horizontal_policy, "内存使用率过高")
        elif memory_utilization < target_memory * 0.5:
            return self._decide_scale_down(horizontal_policy, "内存使用率过低")
        
        return ScalingDecision(ScalingDirection.NO_SCALE, self.current_replicas, "指标正常")
    
    def _is_cooldown_ready(self, policy: Dict[str, Any]) -> bool:
        """检查冷却时间是否已过"""
        current_time = time.time()
        time_since_last_scale = current_time - self.last_scale_time
        
        # 根据上次扩缩容方向选择冷却时间
        if self.current_replicas > 1:  # 假设上次是扩容
            cooldown = policy.get("scale_up_cooldown", 300)
        else:  # 假设上次是缩容
            cooldown = policy.get("scale_down_cooldown", 600)
        
        return time_since_last_scale >= cooldown
    
    def _decide_scale_up(self, policy: Dict[str, Any], reason: str) -> ScalingDecision:
        """决定扩容"""
        max_replicas = policy.get("max_replicas", 10)
        target_replicas = min(self.current_replicas + 1, max_replicas)
        
        if target_replicas > self.current_replicas:
            return ScalingDecision(ScalingDirection.SCALE_UP, target_replicas, reason)
        else:
            return ScalingDecision(ScalingDirection.NO_SCALE, self.current_replicas, "已达到最大副本数")
    
    def _decide_scale_down(self, policy: Dict[str, Any], reason: str) -> ScalingDecision:
        """决定缩容"""
        min_replicas = policy.get("min_replicas", 1)
        target_replicas = max(self.current_replicas - 1, min_replicas)
        
        if target_replicas < self.current_replicas:
            return ScalingDecision(ScalingDirection.SCALE_DOWN, target_replicas, reason)
        else:
            return ScalingDecision(ScalingDirection.NO_SCALE, self.current_replicas, "已达到最小副本数")
    
    def execute_scaling(self, decision: ScalingDecision) -> bool:
        """执行扩缩容"""
        if decision.direction == ScalingDirection.NO_SCALE:
            return False
        
        # 这里应该调用实际的扩缩容API
        print(f"执行{decision.direction.value}: {self.current_replicas} -> {decision.target_replicas}")
        print(f"原因: {decision.reason}")
        
        self.current_replicas = decision.target_replicas
        self.last_scale_time = time.time()
        
        return True
```

### 2. 性能调优

#### 调优策略

```yaml
PerformanceTuning:
  jvm_tuning:
    heap_size: "2g"
    gc_algorithm: "G1GC"
    gc_tuning:
      - "-XX:+UseG1GC"
      - "-XX:MaxGCPauseMillis=200"
      - "-XX:G1HeapRegionSize=16m"
  
  database_tuning:
    connection_pool:
      max_connections: 100
      min_connections: 10
      connection_timeout: 30s
    query_optimization:
      enable_query_cache: true
      query_cache_size: "256m"
  
  cache_tuning:
    redis:
      max_memory: "1g"
      eviction_policy: "allkeys-lru"
      persistence: "aof"
```

## 标准故障恢复

### 1. 健康检查

#### 健康检查配置

```yaml
HealthCheck:
  liveness:
    command: ["/bin/sh", "-c", "curl -f http://localhost:8080/health || exit 1"]
    interval: 30s
    timeout: 10s
    retries: 3
    initial_delay: 60s
  
  readiness:
    command: ["/bin/sh", "-c", "curl -f http://localhost:8080/ready || exit 1"]
    interval: 10s
    timeout: 5s
    retries: 3
    initial_delay: 30s
  
  startup:
    command: ["/bin/sh", "-c", "curl -f http://localhost:8080/startup || exit 1"]
    interval: 10s
    timeout: 5s
    retries: 30
    initial_delay: 10s
```

### 2. 故障转移

#### 故障转移策略

```yaml
FailoverStrategy:
  detection:
    timeout: 30s
    retries: 3
    interval: 10s
  
  recovery:
    auto_restart: true
    max_restart_attempts: 3
    restart_delay: 30s
  
  load_balancing:
    algorithm: "round_robin"
    health_check: true
    failover_timeout: 60s
```

## 最佳实践

1. **资源规划**: 合理规划CPU、内存、存储资源
2. **监控告警**: 建立完善的监控和告警机制
3. **自动扩缩容**: 根据负载自动调整资源
4. **故障恢复**: 实现快速故障检测和恢复
5. **性能优化**: 持续优化运行时性能
6. **安全加固**: 加强运行时安全防护
7. **文档维护**: 保持运行时配置文档的更新

## 相关文档

- [运行时元模型](../meta-models/runtime-model/README.md)
- [验证脚本](../../tools/verification-scripts/README.md)
- [监控工具](../../tools/monitoring/README.md)
