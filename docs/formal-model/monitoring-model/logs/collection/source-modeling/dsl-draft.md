# 日志采集-源建模DSL草案

## 1. 设计目标

- 用声明式语法描述采集源类型、属性、发现、适配、生命周期等流程
- 支持多源异构日志统一源建模
- 便于自动生成采集源与适配配置

## 2. 基本语法结构

```dsl
log_source "app_log" {
  type = "file"
  path = "/var/log/app.log"
  format = "json"
  label = ["app", "prod"]
}

log_discovery "auto_file" {
  method = "auto"
  interval = "5m"
}

log_adaptation "json_adapter" {
  strategy = "format"
  rule = "json->kv"
}

log_lifecycle "app_log_life" {
  state = "active"
  event = "rotate"
  action = "reload"
}
```

## 3. 关键元素

- log_source：采集源定义
- log_discovery：源发现配置
- log_adaptation：源适配配置
- log_lifecycle：生命周期管理

---

## 4. 示例

```dsl
log_source "db_log" {
  type = "database"
  dsn = "mysql://user:pass@host/db"
  table = "logs"
  label = ["db", "prod"]
}

log_discovery "manual_db" {
  method = "manual"
}

log_adaptation "db_adapter" {
  strategy = "protocol"
  rule = "mysql->json"
}

log_lifecycle "db_log_life" {
  state = "inactive"
  event = "drop"
  action = "archive"
}
```

---

## 5. 与主流标准的映射

| DSL元素        | Fluentd | Filebeat | OTel Receiver | Logstash |
|----------------|---------|----------|---------------|----------|
| log_source     | source  | input    | receiver      | input    |
| log_discovery  | n/a     | autodiscover| n/a         | n/a      |
| log_adaptation | filter  | processor| processor     | filter   |
| log_lifecycle  | n/a     | n/a      | n/a           | n/a      |

---

## 6. 递归扩展建议

- 支持多级源建模与动态适配
- 源建模与采集、解析的统一DSL
- 源建模与AI智能识别的集成

---

## 7. 采集源建模DSL关键元素表格

| 元素            | 说明           | 典型属性           |
|-----------------|----------------|--------------------|
| log_source      | 采集源定义     | type, path, format, label |
| log_discovery   | 源发现配置     | method, interval   |
| log_adaptation  | 源适配配置     | strategy, rule     |
| log_lifecycle   | 生命周期管理   | state, event, action |

---

## 8. 采集源建模DSL语法思维导图（Mermaid）

```mermaid
mindmap
  root((采集源建模DSL))
    log_source
      type
      path
      format
      label
    log_discovery
      method
      interval
    log_adaptation
      strategy
      rule
    log_lifecycle
      state
      event
      action
```

---

## 9. 形式化DSL推理片段

**推论：**  
若 log_source、log_discovery、log_adaptation、log_lifecycle 语法均具备完备性，则任意采集源建模流程均可通过DSL自动生成配置与推理链路。

**证明思路：**  

- 每个环节均可形式化为DSL声明；
- DSL可自动转化为采集源/适配/生命周期配置；
- 组合DSL可推导出完整的采集源建模链路。
