# 自动化脚手架/一键生成工具设计

## 设计目标

- 一键生成项目骨架、模型、代码、配置、CI/CD等全套工程文件
- 支持多语言、多框架、多场景（微服务、Web、API网关等）
- 支持交互式命令行与可视化界面

## 关键功能

- 项目初始化（init）：选择语言、框架、模板、目录结构
- 模型驱动生成（generate）：根据模型定义自动生成代码/配置/文档
- 插件扩展（plugin）：支持自定义生成器/模板/AI集成
- 预览与回滚：生成前预览diff，支持回滚

## 技术选型建议

- CLI：Rust（clap）、Golang（cobra）、Node.js（commander）
- 可视化：Web前端+WASM后端
- 模板引擎：handlebars、tera、text/template等

## 目录结构建议

```text
tools/
  └── cli/
        ├── main.rs / main.go / index.js
        ├── commands/
        ├── templates/
        └── plugins/
```

## 交互流程示例

```text
$ formal init
? 选择项目类型：微服务 / Web / API网关
? 选择主语言：Rust / Golang / ...
? 选择前端：React / Vue / WASM
? 是否集成AI辅助：是 / 否
? 是否生成CI/CD：是 / 否
...
$ formal generate --model examples/webapp/webapp-demo.yaml
```

## 未来展望

- 支持在线可视化建模与一键导出
- 支持AI自动补全与智能推荐
- 支持云端脚手架与团队协作
