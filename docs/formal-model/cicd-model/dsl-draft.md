# CI/CD模型DSL草案

## 1. 设计目标

- 用统一DSL描述流水线、阶段、触发、质量门禁等CI/CD要素。
- 支持自动生成Jenkinsfile、.gitlab-ci.yml、GitHub Actions等主流配置。

## 2. 基本语法结构

```dsl
pipeline BuildAndDeploy {
  trigger: push
  stages: [
    build {
      script: "make build"
      artifacts: ["dist/"]
    },
    test {
      script: "pytest tests/"
      coverage: 0.8
    },
    deploy {
      script: "kubectl apply -f k8s.yaml"
      only: branch == "main"
    }
  ]
  quality_gate: {
    code_review: required
    coverage: 0.8
  }
}
```

## 3. 关键元素

- pipeline：流水线定义
- trigger：触发方式
- stages：阶段序列
- script/artifacts/coverage/only：阶段常用字段
- quality_gate：质量门禁

## 4. 示例

```dsl
pipeline Release {
  trigger: tag
  stages: [
    build {
      script: "npm run build"
    },
    test {
      script: "npm test"
      coverage: 0.9
    },
    publish {
      script: "npm publish"
      only: branch == "main"
    }
  ]
  quality_gate: {
    approval: 2
    coverage: 0.9
  }
}
```

## 5. 与主流标准的映射

- 可自动转换为Jenkinsfile、.gitlab-ci.yml、GitHub Actions等配置
- 支持与主流CI/CD平台集成

## 6. 递归扩展建议

- 支持多流水线、并发与依赖
- 支持多种触发器、动态阶段
- 支持质量门禁自定义与异常处理
