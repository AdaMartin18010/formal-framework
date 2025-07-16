# 工作流建模DSL草案

## 1. 设计目标

- 用统一DSL描述顺序、分支、并发、子流程、动态任务、补偿等工作流要素。
- 支持自动生成BPMN、Airflow DAG、Argo Workflow等配置。

## 2. 基本语法结构

```dsl
workflow DataPipeline {
  task Extract {
    action: extract_data
  }
  task Transform {
    action: transform_data
    depends_on: [Extract]
  }
  task Load {
    action: load_data
    depends_on: [Transform]
  }
  branch {
    if error => HandleError
    else => End
  }
  task HandleError {
    action: send_alert
    compensation: rollback
  }
}
```

## 3. 关键元素

- workflow/task：工作流与任务定义
- action/depends_on：任务动作与依赖
- branch/compensation：分支与补偿
- 并发/子流程/动态任务：可扩展结构

## 4. 常用工作流结构声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| workflow DataPipeline { ... }                 | 工作流定义     |
| task Extract { ... }                          | 任务定义       |
| depends_on: [TaskA]                           | 依赖声明       |
| branch { if cond => A; else => B }            | 条件分支       |
| parallel { TaskA, TaskB }                     | 并发结构       |
| subflow { ... }                               | 子流程         |
| compensation: rollback                        | 补偿动作       |
| dynamic_task { ... }                          | 动态任务       |

## 5. 与主流标准的映射

- 可自动转换为BPMN、Airflow DAG、Argo Workflow等配置
- 支持与主流工作流引擎集成

## 6. 递归扩展建议

- 支持复杂嵌套、动态依赖、异常处理
- 支持流程监控与自动化测试
