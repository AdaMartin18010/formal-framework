# 网络建模DSL草案

## 1. 设计目标

- 用统一DSL描述服务发现、网络策略、拓扑、流量管理、安全等网络要素。
- 支持自动生成K8s NetworkPolicy、Service、Ingress、Istio等配置。

## 2. 基本语法结构

```dsl
network frontend_net {
  type: flat
  services: [web, api]
  policy: allow_all
}

network backend_net {
  type: segment
  services: [db, cache]
  policy: deny_external
}

service_discovery mydns {
  type: dns
  domain: "example.com"
}

traffic_policy api_policy {
  route: {
    path: "/api/v1/*"
    to: api
  }
  rate_limit: 1000
  circuit_breaker: true
}
```

## 3. 关键元素

- network：网络声明
- type/services/policy：类型、服务、策略
- service_discovery：服务发现
- traffic_policy：流量管理

## 4. 常用网络声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| network frontend_net { ... }                  | 网络定义       |
| type: flat/segment/mesh                       | 拓扑类型       |
| services: [web, api]                          | 服务分组       |
| policy: allow_all/deny_external               | 策略声明       |
| service_discovery mydns { ... }               | 服务发现       |
| traffic_policy api_policy { ... }             | 流量管理       |

## 5. 与主流标准的映射

- 可自动转换为K8s NetworkPolicy、Service、Ingress、Istio等配置
- 支持与主流网络与服务网格工具集成

## 6. 递归扩展建议

- 支持多网络拓扑、动态策略、零信任安全
- 支持流量镜像、灰度发布、异常检测
