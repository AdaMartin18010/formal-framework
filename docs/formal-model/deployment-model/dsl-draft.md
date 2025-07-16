# 部署模型DSL草案

## 1. 设计目标

- 用统一DSL描述基础设施、配置、版本、回滚等部署要素。
- 支持自动生成Terraform、Helm、Kustomize等主流IaC和部署配置。

## 2. 基本语法结构

```dsl
infrastructure cloud {
  provider: "aws"
  region: "us-east-1"
  resources: [
    ec2 { type: "t3.medium" count: 2 },
    rds { engine: "postgres", size: "20Gi" }
  ]
}

config app {
  env: {
    APP_ENV: "production"
    LOG_LEVEL: "info"
  }
  secrets: ["DB_PASSWORD"]
}

version release {
  image: "myapp:v1.2.3"
  changelog: "修复若干bug"
}

rollback policy {
  trigger: "deployment_failed"
  action: "revert_to_previous_version"
}
```

## 3. 关键元素

- infrastructure：基础设施定义
- config：环境与密钥配置
- version：版本与变更
- rollback：回滚策略

## 4. 示例

```dsl
infrastructure k8s {
  provider: "gke"
  node_pool: {
    type: "n1-standard-2"
    count: 3
  }
}

config webapp {
  env: {
    API_URL: "https://api.example.com"
  }
}

version canary {
  image: "webapp:v2.0.0-beta"
}

rollback auto {
  trigger: "health_check_failed"
  action: "rollback"
}
```

## 5. 与主流标准的映射

- 可自动转换为Terraform、Pulumi、Helm、Kustomize等配置
- 支持与GitOps工具链集成

## 6. 递归扩展建议

- 支持多云与混合云资源建模
- 支持配置分层与动态加载
- 支持多版本灰度发布与自动回滚
