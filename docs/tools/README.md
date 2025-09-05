# 工具链

## 📋 概述

正式验证框架提供了完整的工具链，包括验证脚本、测试框架、监控工具和部署工具。

## 🛠️ 工具分类

### 1. 验证脚本

- [Kubernetes验证](verification-scripts/kubernetes/)
- [Docker验证](verification-scripts/docker/)
- [Terraform验证](verification-scripts/terraform/)
- [Ansible验证](verification-scripts/ansible/)

### 2. 测试框架

- [k6性能测试](testing-frameworks/k6/)
- [JMeter负载测试](testing-frameworks/jmeter/)
- [自定义测试框架](testing-frameworks/custom/)

### 3. 监控工具

- [Prometheus指标收集](monitoring/prometheus/)
- [Grafana可视化](monitoring/grafana/)
- [Jaeger链路追踪](monitoring/jaeger/)

### 4. 部署工具

- [Docker容器化](deployment/docker/)
- [Kubernetes编排](deployment/kubernetes/)
- [Helm包管理](deployment/helm/)

## 🚀 快速开始

### 安装工具链

```bash
# 安装所有工具
npm run install-tools

# 验证工具安装
npm run verify-tools
```

### 运行验证

```bash
# 运行完整验证
npm run verify:all

# 运行特定验证
npm run verify:kubernetes
```

## 🔗 相关文档

- [验证矩阵](../VERIFICATION_MATRIX.md)
- [实践案例](../examples/README.md)
- [社区资源](../community/README.md)

---

*最后更新：2024-12-19*-
