# 测试模型DSL草案

## 1. 设计目标

- 用统一DSL描述测试用例、断言、覆盖率、性能等测试要素。
- 支持自动生成pytest、JUnit、Cucumber、JMeter等主流测试脚本和配置。

## 2. 基本语法结构

```dsl
testcase LoginSuccess {
  description: "用户登录成功"
  steps: [
    { action: "输入用户名", input: "user1" },
    { action: "输入密码", input: "pass123" },
    { action: "点击登录" }
  ]
  expect: {
    status: 200
    message: "登录成功"
  }
}

assert StatusCodeOK {
  actual: response.status
  expect: 200
}

coverage target: "src/", threshold: 0.8

performance LoginLoad {
  users: 1000
  duration: "5m"
  expect: {
    avg_response_time < 200
    error_rate < 0.01
  }
}
```

## 3. 关键元素

- testcase：测试用例定义
- steps：步骤序列
- expect/assert：期望与断言
- coverage：覆盖率目标
- performance：性能测试配置

## 4. 示例

```dsl
testcase RegisterFail {
  description: "注册失败-用户名已存在"
  steps: [
    { action: "输入用户名", input: "user1" },
    { action: "输入密码", input: "pass123" },
    { action: "点击注册" }
  ]
  expect: {
    status: 400
    message: "用户名已存在"
  }
}

assert ErrorMessage {
  actual: response.message
  expect: "用户名已存在"
}

coverage target: "src/service/", threshold: 0.9

performance RegisterLoad {
  users: 500
  duration: "2m"
  expect: {
    avg_response_time < 300
    error_rate < 0.02
  }
}
```

## 5. 与主流标准的映射

- 可自动转换为pytest、JUnit、Cucumber、JMeter等脚本
- 支持与CI/CD集成自动化测试

## 6. 递归扩展建议

- 支持数据驱动测试、边界条件自动生成
- 支持断言表达式扩展、性能场景多样化
- 支持测试报告与覆盖率可视化
