# 服务网格理论

## 目录（Table of Contents）

- [服务网格理论](#服务网格理论)
  - [目录（Table of Contents）](#目录table-of-contents)
  - [概念定义](#概念定义)
    - [服务网格](#服务网格)
    - [核心概念](#核心概念)
  - [理论基础](#理论基础)
    - [形式化建模](#形式化建模)
    - [公理化系统](#公理化系统)
    - [类型安全与配置示例（Istio）](#类型安全与配置示例istio)
  - [应用案例](#应用案例)
    - [案例1：跨版本金丝雀](#案例1跨版本金丝雀)
    - [案例2：零信任南北向网关](#案例2零信任南北向网关)
  - [最佳实践](#最佳实践)
  - [开源项目映射](#开源项目映射)
  - [相关链接](#相关链接)
  - [总结](#总结)

## 概念定义

### 服务网格

以Sidecar代理（如Envoy）与控制面（如Istio）分离架构实现的微服务网络治理层，提供流量管理、安全与可观测性。

### 核心概念

- 数据平面（Data Plane）：每个Pod旁路的代理，负责转发与策略落实
- 控制平面（Control Plane）：集中下发策略与配置
- 流量策略：路由、熔断、限流、超时、重试
- 安全策略：mTLS、认证授权、证书轮换

## 理论基础

### 形式化建模

```yaml
service_mesh:
  mesh:
    definition: "M = (D, C, T, S)"
    where:
      D: "数据平面代理集合"
      C: "控制面组件集合"
      T: "流量策略集合"
      S: "安全策略集合"
  route:
    definition: "t = (match, action, weight)"
```

### 公理化系统

```yaml
axioms:
  - name: "零信任默认拒绝"
    rule: "deny by default, allow by policy"
  - name: "端到端加密"
    rule: "all in-mesh traffic must use mTLS"
  - name: "金丝雀与回滚"
    rule: "traffic shifting must be reversible"
  - name: "最短路径与超时"
    rule: "timeouts must bound worst-case latency"
```

### 类型安全与配置示例（Istio）

```yaml
# 虚拟服务与目标规则（精简）
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: users
spec:
  hosts: ["users.svc.cluster.local"]
  http:
    - match: [{ uri: { prefix: "/api" } }]
      route:
        - destination: { host: users, subset: v1, port: { number: 8080 } }
          weight: 80
        - destination: { host: users, subset: v2, port: { number: 8080 } }
          weight: 20
---
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: users
spec:
  host: users
  subsets:
    - name: v1
      labels: { version: v1 }
    - name: v2
      labels: { version: v2 }
```

```yaml
# 授权策略（精简）
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: allow-get
spec:
  selector:
    matchLabels:
      app: users
  action: ALLOW
  rules:
    - to:
        - operation:
            methods: ["GET"]
            paths: ["/api/*"]
      when:
        - key: request.headers[":authority"]
          values: ["api.example.com"]
```

## 应用案例

### 案例1：跨版本金丝雀

```yaml
canary:
  users:
    v1_weight: 90
    v2_weight: 10
```

### 案例2：零信任南北向网关

```yaml
zero_trust_gateway:
  ingress: istio-ingressgateway
  tls: mTLS + TLS-termination
  waf: enabled
  oidc: enabled
```

## 最佳实践

```yaml
best_practices:
  - name: 分层策略
    description: "入口网关、命名空间、服务多层策略叠加"
  - name: 证书轮换
    description: "短生命周期证书+自动轮换"
  - name: 可回滚发布
    description: "金丝雀+流量镜像+快速回滚"
  - name: 一致观测
    description: "统一指标、日志、追踪；关联网关与服务指标"
```

## 开源项目映射

- Istio, Linkerd, Consul, Kuma

## 相关链接

- 内部: `docs/industry-model/cloud-native-architecture/theory.md`
- 外部: `https://istio.io/`, `https://linkerd.io/`

## 总结

服务网格以策略驱动实现微服务通信的安全、弹性与可观测，结合声明式配置与GitOps可实现稳定、可回滚的演进。
