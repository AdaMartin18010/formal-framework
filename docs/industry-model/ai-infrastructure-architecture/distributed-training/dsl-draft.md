# 分布式训练 DSL 草案

## 1. 概述

### 1.1 目标与范围

- 定义分布式训练系统的DSL规范
- 支持多种分布式训练策略和算法
- 提供训练配置、资源分配、通信模式的形式化描述

### 1.2 核心概念

- **训练节点**：参与分布式训练的单个计算单元
- **训练集群**：多个训练节点组成的计算集群
- **训练策略**：数据并行、模型并行、流水线并行等
- **通信模式**：节点间数据交换和同步机制

## 2. 结构定义

### 2.1 顶层对象

```yaml
distributed_training:
  name: string
  version: string
  strategy: TrainingStrategy
  cluster: TrainingCluster
  communication: CommunicationConfig
  resources: ResourceConfig
  monitoring: MonitoringConfig
```

### 2.2 训练策略（TrainingStrategy）

```yaml
training_strategy:
  type: "data_parallel" | "model_parallel" | "pipeline_parallel" | "hybrid"
  data_parallel:
    batch_size: int
    num_workers: int
    data_sharding: DataShardingConfig
  model_parallel:
    model_splitting: ModelSplittingConfig
    pipeline_stages: int
  pipeline_parallel:
    micro_batch_size: int
    pipeline_stages: int
    schedule: "1F1B" | "GPipe" | "Interleaved"
```

### 2.3 训练集群（TrainingCluster）

```yaml
training_cluster:
  nodes: Node[]
  topology: TopologyConfig
  node:
    id: string
    role: "master" | "worker" | "parameter_server"
    resources: NodeResources
    network: NetworkConfig
```

### 2.4 通信配置（CommunicationConfig）

```yaml
communication_config:
  protocol: "NCCL" | "MPI" | "gRPC" | "custom"
  collective_ops: CollectiveOpsConfig
  allreduce:
    algorithm: "ring" | "tree" | "butterfly"
    buffer_size: int
  broadcast:
    algorithm: "tree" | "linear"
  gather:
    algorithm: "linear" | "tree"
```

### 2.5 资源配置（ResourceConfig）

```yaml
resource_config:
  cpu:
    cores: int
    memory: string
  gpu:
    count: int
    memory: string
    type: string
  storage:
    local: StorageConfig
    shared: StorageConfig
  network:
    bandwidth: string
    latency: string
```

### 2.6 监控配置（MonitoringConfig）

```yaml
monitoring_config:
  metrics:
    - "throughput"
    - "latency"
    - "utilization"
    - "loss"
  logging:
    level: "INFO" | "DEBUG" | "WARN"
    format: "json" | "text"
  visualization:
    enabled: boolean
    dashboard: DashboardConfig
```

## 3. 字段说明

### 3.1 训练策略字段

- **type**: 训练策略类型，支持数据并行、模型并行、流水线并行或混合策略
- **batch_size**: 全局批次大小，在数据并行中分配给所有节点
- **num_workers**: 数据加载器的工作进程数量
- **data_sharding**: 数据分片配置，定义数据如何在节点间分配

### 3.2 模型并行字段

- **model_splitting**: 模型分割配置，定义模型层如何在节点间分配
- **pipeline_stages**: 流水线阶段数量，用于流水线并行
- **schedule**: 流水线调度策略，支持1F1B、GPipe、Interleaved等算法

### 3.3 集群配置字段

- **nodes**: 训练节点列表，每个节点包含ID、角色、资源配置
- **topology**: 网络拓扑配置，定义节点间的连接关系
- **role**: 节点角色，包括主节点、工作节点、参数服务器等

### 3.4 通信配置字段

- **protocol**: 通信协议，支持NCCL、MPI、gRPC等
- **collective_ops**: 集合操作配置，包括allreduce、broadcast、gather等
- **algorithm**: 通信算法，如ring、tree、butterfly等

## 4. 示例

### 4.1 数据并行训练示例

```yaml
distributed_training:
  name: "resnet50_data_parallel"
  version: "1.0.0"
  strategy:
    type: "data_parallel"
    data_parallel:
      batch_size: 256
      num_workers: 4
      data_sharding:
        method: "random"
        seed: 42
  cluster:
    nodes:
      - id: "node-1"
        role: "master"
        resources:
          gpu:
            count: 4
            memory: "16GB"
      - id: "node-2"
        role: "worker"
        resources:
          gpu:
            count: 4
            memory: "16GB"
  communication:
    protocol: "NCCL"
    allreduce:
      algorithm: "ring"
      buffer_size: 1048576
  resources:
    gpu:
      type: "V100"
  monitoring:
    metrics: ["throughput", "loss"]
    logging:
      level: "INFO"
```

### 4.2 模型并行训练示例

```yaml
distributed_training:
  name: "gpt3_model_parallel"
  version: "1.0.0"
  strategy:
    type: "model_parallel"
    model_parallel:
      model_splitting:
        method: "layer_wise"
        layers_per_node: 12
      pipeline_stages: 4
  cluster:
    nodes:
      - id: "node-1"
        role: "worker"
        resources:
          gpu:
            count: 8
            memory: "32GB"
      - id: "node-2"
        role: "worker"
        resources:
          gpu:
            count: 8
            memory: "32GB"
  communication:
    protocol: "NCCL"
    broadcast:
      algorithm: "tree"
  resources:
    gpu:
      type: "A100"
  monitoring:
    metrics: ["throughput", "latency", "utilization"]
```

### 4.3 流水线并行训练示例

```yaml
distributed_training:
  name: "bert_pipeline_parallel"
  version: "1.0.0"
  strategy:
    type: "pipeline_parallel"
    pipeline_parallel:
      micro_batch_size: 8
      pipeline_stages: 8
      schedule: "1F1B"
  cluster:
    nodes:
      - id: "node-1"
        role: "worker"
        resources:
          gpu:
            count: 4
            memory: "16GB"
      - id: "node-2"
        role: "worker"
        resources:
          gpu:
            count: 4
            memory: "16GB"
  communication:
    protocol: "gRPC"
  resources:
    gpu:
      type: "V100"
  monitoring:
    metrics: ["throughput", "bubble_time"]
```

## 5. 自动化推理伪代码

### 5.1 训练策略验证

```python
def validate_training_strategy(strategy):
    if strategy.type == "data_parallel":
        validate_data_parallel_config(strategy.data_parallel)
    elif strategy.type == "model_parallel":
        validate_model_parallel_config(strategy.model_parallel)
    elif strategy.type == "pipeline_parallel":
        validate_pipeline_parallel_config(strategy.pipeline_parallel)
    else:
        raise ValueError(f"Unsupported strategy type: {strategy.type}")

def validate_data_parallel_config(config):
    if config.batch_size <= 0:
        raise ValueError("Batch size must be positive")
    if config.num_workers <= 0:
        raise ValueError("Number of workers must be positive")
```

### 5.2 资源分配计算

```python
def calculate_resource_requirements(cluster, strategy):
    total_gpu_memory = 0
    total_cpu_cores = 0
    
    for node in cluster.nodes:
        if node.resources.gpu:
            total_gpu_memory += node.resources.gpu.count * parse_memory(node.resources.gpu.memory)
        if node.resources.cpu:
            total_cpu_cores += node.resources.cpu.cores
    
    return {
        "total_gpu_memory": total_gpu_memory,
        "total_cpu_cores": total_cpu_cores,
        "estimated_throughput": estimate_throughput(cluster, strategy)
    }
```

### 5.3 通信优化

```python
def optimize_communication_config(cluster, strategy):
    if strategy.type == "data_parallel":
        return optimize_allreduce_config(cluster)
    elif strategy.type == "model_parallel":
        return optimize_broadcast_config(cluster)
    elif strategy.type == "pipeline_parallel":
        return optimize_pipeline_communication(cluster)
    
def optimize_allreduce_config(cluster):
    node_count = len(cluster.nodes)
    if node_count <= 8:
        return {"algorithm": "ring", "buffer_size": 1048576}
    else:
        return {"algorithm": "tree", "buffer_size": 2097152}
```

## 6. 自动化生成脚本片段

### 6.1 训练脚本生成

```python
def generate_training_script(dsl_config):
    script = f"""
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP

def setup_distributed():
    dist.init_process_group(backend='{dsl_config.communication.protocol.lower()}')
    
def create_model():
    # Model creation logic based on strategy
    if '{dsl_config.strategy.type}' == 'data_parallel':
        return create_data_parallel_model()
    elif '{dsl_config.strategy.type}' == 'model_parallel':
        return create_model_parallel_model()
    
def train():
    setup_distributed()
    model = create_model()
    # Training loop implementation
"""
    return script
```

### 6.2 配置文件生成

```python
def generate_config_file(dsl_config):
    config = {
        "training": {
            "batch_size": dsl_config.strategy.data_parallel.batch_size,
            "num_workers": dsl_config.strategy.data_parallel.num_workers
        },
        "distributed": {
            "backend": dsl_config.communication.protocol.lower(),
            "world_size": len(dsl_config.cluster.nodes)
        },
        "resources": {
            "gpu_count": sum(node.resources.gpu.count for node in dsl_config.cluster.nodes)
        }
    }
    return config
```

## 7. 模板使用说明

### 7.1 复制此模板到新模型目录

- 将此DSL草案作为分布式训练模型的基础模板
- 根据具体需求修改结构定义和字段说明
- 补充实际示例和自动化推理伪代码

### 7.2 根据具体需求修改

- 调整训练策略类型和参数
- 修改集群配置和资源分配
- 优化通信协议和算法选择

### 7.3 补充实际示例

- 添加行业特定的训练场景
- 包含性能优化和故障处理案例
- 提供完整的端到端训练流程

### 7.4 删除可选部分

- 保留必要的结构定义和字段说明
- 删除不相关的示例和配置
- 确保DSL的简洁性和可读性
