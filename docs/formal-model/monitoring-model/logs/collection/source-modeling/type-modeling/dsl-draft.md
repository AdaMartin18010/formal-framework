# 日志采集-源类型建模DSL草案

## 1. 设计目标

- 用声明式语法描述采集源类型分类、属性、扩展、映射等流程
- 支持多类型日志源统一类型建模
- 便于自动生成类型识别与适配配置

## 2. 基本语法结构

```dsl
type_model "file" {
  category = "local"
  path = "/var/log/*.log"
  format = "json"
}

type_model "database" {
  category = "structured"
  dsn = "mysql://user:pass@host/db"
  table = "logs"
}

type_extension "mq" {
  plugin = "kafka"
  topic = "logs"
}

type_mapping "api_to_file" {
  from = "api"
  to = "file"
  rule = "json->kv"
}
```

## 3. 关键元素

- type_model：类型建模定义
- type_extension：类型扩展配置
- type_mapping：类型映射配置

---

## 4. 示例

```dsl
type_model "syslog" {
  category = "system"
  facility = "auth"
  level = "info"
}

type_extension "custom_plugin" {
  plugin = "custom"
  config = "custom.yaml"
}

type_mapping "db_to_api" {
  from = "database"
  to = "api"
  rule = "row->json"
}
```

---

## 5. 与主流标准的映射

| DSL元素        | Fluentd | Filebeat | OTel Receiver | Logstash |
|----------------|---------|----------|---------------|----------|
| type_model     | source  | input    | receiver      | input    |
| type_extension | plugin  | module   | extension     | plugin   |
| type_mapping   | filter  | processor| processor     | filter   |

---

## 6. 递归扩展建议

- 支持多级类型建模与动态扩展
- 类型建模与采集、解析的统一DSL
- 类型建模与AI智能识别的集成

---

## 7. 源类型建模DSL关键元素表格

| 元素            | 说明           | 典型属性           |
|-----------------|----------------|--------------------|
| type_model      | 类型建模定义   | category, path, format, dsn, table |
| type_extension  | 类型扩展配置   | plugin, topic, config |
| type_mapping    | 类型映射配置   | from, to, rule     |

---

## 8. 源类型建模DSL语法思维导图（Mermaid）

```mermaid
mindmap
  root((源类型建模DSL))
    type_model
      category
      path
      format
      dsn
      table
    type_extension
      plugin
      topic
      config
    type_mapping
      from
      to
      rule
```

---

## 9. 形式化DSL推理片段

**推论：**  
若 type_model、type_extension、type_mapping 语法均具备完备性，则任意采集源类型建模流程均可通过DSL自动生成配置与推理链路。

**证明思路：**  

- 每个环节均可形式化为DSL声明；
- DSL可自动转化为类型/扩展/映射配置；
- 组合DSL可推导出完整的类型建模链路。
