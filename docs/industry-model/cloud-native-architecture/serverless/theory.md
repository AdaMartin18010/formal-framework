# 无服务器理论

## 概念定义

### 无服务器计算（Serverless）

以事件驱动与函数即服务（FaaS）为核心的云原生范式，开发者关注业务逻辑，平台负责弹性伸缩、运行时与计费。

### 核心概念

- **函数（Function）**: 部署与计费最小单元
- **事件（Event）**: 触发函数执行的输入
- **触发器（Trigger）**: 将事件源与函数绑定
- **并发（Concurrency）**: 并行执行度与资源隔离

## 理论基础

### 形式化建模理论

```yaml
serverless:
  function:
    definition: "f = (code, runtime, memory, timeout, env, perms)"
  trigger:
    definition: "t = (source, filter, mapping)"
  scaling:
    definition: "s = (min, max, concurrency, cooldown)"
```

### 公理化系统

```yaml
axioms:
  - name: "幂等性"
    rule: "for events possibly delivered >=1 times, f must be idempotent"
  - name: "最短冷启动路径"
    rule: "runtime.init <= configured_threshold"
  - name: "权限最小化"
    rule: "function.permissions subset_of required_permissions"
  - name: "背压与限流"
    rule: "queue_depth <= max_backlog and qps <= limit"
```

### 类型安全与配置示例

```yaml
# AWS SAM/CloudFormation（精简）
Resources:
  HelloFunction:
    Type: AWS::Serverless::Function
    Properties:
      CodeUri: src/
      Handler: app.handler
      Runtime: nodejs18.x
      MemorySize: 256
      Timeout: 10
      Policies:
        - AWSLambdaBasicExecutionRole
      Events:
        HttpApi:
          Type: HttpApi
          Properties:
            Path: /hello
            Method: get
```

```yaml
# Knative Service（精简）
apiVersion: serving.knative.dev/v1
kind: Service
metadata:
  name: hello
spec:
  template:
    spec:
      containers:
        - image: gcr.io/demo/hello:latest
          env:
            - name: TARGET
              value: "World"
      containerConcurrency: 100
  traffic:
    - latestRevision: true
      percent: 100
```

## 应用案例

### 案例1：事件驱动图像处理

```yaml
event_image_pipeline:
  triggers:
    - source: s3:ObjectCreated
      filter: { suffix: ".jpg" }
  functions:
    - name: resize
      memory: 512
      timeout: 15
    - name: classify
      memory: 1024
      timeout: 20
  queues:
    - name: image-jobs
      dlq: image-dlq
```

### 案例2：API后端

```yaml
serverless_api:
  http:
    base_path: /api
    routes:
      - path: /orders
        method: POST
        function: createOrder
      - path: /orders/{id}
        method: GET
        function: getOrder
  auth: oidc
  rate_limit:
    per_minute: 120
```

## 最佳实践

```yaml
best_practices:
  - name: 冷启动优化
    tips: ["预热", "轻量依赖", "较小镜像"]
  - name: 幂等与重试
    tips: ["幂等键", "指数退避", "DLQ"]
  - name: 观测性
    tips: ["结构化日志", "分布式追踪", "自定义指标"]
  - name: 安全
    tips: ["最小权限IAM", "密钥管理", "输入校验"]
  - name: 成本优化
    tips: ["右尺寸运行内存", "按需并发", "缓存复用"]
```

## 开源项目映射

- Knative, OpenFaaS, AWS SAM/Serverless Framework

## 相关链接

- 内部: `docs/industry-model/cloud-native-architecture/theory.md`
- 外部: `https://knative.dev/`, `https://www.serverless.com/`

## 总结

无服务器通过事件驱动与细粒度伸缩提升迭代效率与成本效率。遵循幂等、权限最小化与可观测性原则可显著提升可靠性。
