# API网关理论

## 目录（Table of Contents）

- [API网关理论](#api网关理论)
  - [目录（Table of Contents）](#目录table-of-contents)
  - [概念定义](#概念定义)
    - [API网关](#api网关)
    - [核心概念](#核心概念)
  - [理论基础](#理论基础)
    - [形式化建模理论](#形式化建模理论)
    - [公理化系统](#公理化系统)
    - [类型安全理论](#类型安全理论)
  - [应用案例](#应用案例)
    - [案例1：零信任API访问控制](#案例1零信任api访问控制)
    - [案例2：灰度发布与金丝雀流量](#案例2灰度发布与金丝雀流量)
  - [最佳实践](#最佳实践)
  - [开源项目映射](#开源项目映射)
  - [相关链接](#相关链接)
  - [总结](#总结)

## 概念定义

### API网关

API网关是微服务架构中的统一入口，负责请求路由、协议转换、认证鉴权、限流熔断、可观测性等横切能力的集中治理。

### 核心概念

- **路由（Route）**: 将外部请求匹配并转发到后端服务
- **服务（Service）**: 后端上游目标的抽象，包含目标地址、协议等
- **插件（Plugin）**: 以插件化方式提供认证、限流、日志等能力
- **策略（Policy）**: 安全策略、CORS、WAF、缓存等

## 理论基础

### 形式化建模理论

```yaml
# API网关形式化定义
api_gateway:
  gateway:
    definition: "G = (R, S, P, A)"
    where:
      R: "路由集合 {r1, r2, ..., rn}"
      S: "服务集合 {s1, s2, ..., sm}"
      P: "插件/策略集合"
      A: "访问控制集合 (ACL/RBAC)"
  
  route:
    definition: "r = (match, filters, destination)"
    properties:
      - "匹配条件: host, path, headers, methods"
      - "过滤器/插件链: auth, rate-limit, rewrite, cors"
      - "目标服务: service/ref"
  
  policy:
    definition: "p = (type, rules, scope)"
    examples:
      - type: "authz"
        rules: ["allow", "deny", "conditions"]
      - type: "rate-limit"
        rules: ["requests_per_minute", "burst"]
```

### 公理化系统

```yaml
axioms:
  - name: "匹配唯一性"
    rule: "for any request, select highest priority matching route"
    description: "请求匹配的路由具备确定的优先级与唯一决策"
  - name: "安全前置性"
    rule: "authz and authn must be evaluated before upstream forwarding"
    description: "认证鉴权先于转发，防止未授权访问"
  - name: "限流守恒"
    rule: "effective_qps <= configured_limit"
    description: "有效请求速率不得超过配置阈值"
  - name: "可观测性可追溯"
    rule: "every request must emit standardized access log and metrics"
    description: "所有请求需输出标准化日志与指标"
```

### 类型安全理论

```yaml
# Kong 声明式配置示例（部分）
_format_version: "3.0"
_transform: true
services:
  - name: user-service
    url: http://user-service.default.svc.cluster.local:8080
    routes:
      - name: user-api
        hosts: ["api.example.com"]
        paths: ["/users"]
        methods: ["GET", "POST"]
        plugins:
          - name: jwt
          - name: rate-limiting
            config:
              minute: 120
              policy: local
plugins:
  - name: cors
    config:
      origins: ["https://console.example.com"]
      methods: ["GET", "POST"]
      headers: ["Authorization", "Content-Type"]
```

## 应用案例

### 案例1：零信任API访问控制

```yaml
zero_trust_api:
  gateway: kong
  policies:
    - type: oidc
      issuer: "https://auth.example.com"
      client_id: "api-gateway"
      scopes: ["openid", "profile"]
    - type: rbac
      rules:
        - allow: ["GET /users"]
          roles: ["reader", "admin"]
        - allow: ["POST /users"]
          roles: ["admin"]
  rate_limit:
    per_minute: 300
    burst: 50
```

### 案例2：灰度发布与金丝雀流量

```yaml
canary_release:
  gateway: envoy
  routes:
    - match: { prefix: "/orders" }
      route:
        weighted_clusters:
          - name: orders-v1
            weight: 80
          - name: orders-v2
            weight: 20
      filters:
        - type: header_modifier
          add:
            x-canary: v2
```

## 最佳实践

```yaml
best_practices:
  - name: "最小权限原则"
    description: "对路由与管理面应用最小权限RBAC"
  - name: "分层限流"
    description: "全局+路由+用户级多层限流，配合熔断重试"
  - name: "零信任认证"
    description: "优先OIDC/JWT，尽量避免共享密钥"
  - name: "统一可观测性"
    description: "标准化访问日志、指标与追踪上下文（W3C TraceContext）"
  - name: "配置即代码"
    description: "网关配置使用GitOps管理，分环境版本化"
```

## 开源项目映射

- Kong: 插件生态丰富，适合快速扩展
- Envoy: L7代理内核，性能优异，生态广
- Traefik: 云原生友好，自动发现

## 相关链接

- 内部: `docs/industry-model/cloud-native-architecture/theory.md`
- 内部: `docs/formal-model/interaction-model/api/theory.md`
- 外部: `https://konghq.com/`, `https://www.envoyproxy.io/`, `https://doc.traefik.io/`

## 总结

通过形式化建模、公理化约束与类型安全的配置治理，API网关可以实现统一入口、可靠安全与高可运维性的目标，支撑大规模微服务对外/对内的稳定暴露。
