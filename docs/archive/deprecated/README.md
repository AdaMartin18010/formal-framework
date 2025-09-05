# 废弃内容

## 📋 概述

本目录包含正式验证框架中已废弃的功能和文档，用于历史追溯和迁移指导。

## 🚫 废弃功能列表

### 已废弃的API接口

- **v1.0 API** (废弃于 v2.0.0)
  - 原因：架构重构，新的API设计更清晰
  - 替代方案：使用v2.0+ API
  - 迁移指南：[API迁移指南](../getting-started/migration.md#api-migration)

### 已废弃的配置选项

- **legacy-config** (废弃于 v2.1.0)
  - 原因：配置系统重新设计
  - 替代方案：使用新的配置格式
  - 迁移指南：[配置迁移指南](../getting-started/migration.md#config-migration)

### 已废弃的工具和脚本

- **old-verification-script** (废弃于 v2.2.0)
  - 原因：功能整合到新的工具链中
  - 替代方案：使用新的验证工具
  - 迁移指南：[工具迁移指南](../getting-started/migration.md#tool-migration)

## 🔄 废弃策略

### 废弃流程

1. **废弃通知**：提前3个月通知废弃计划
2. **迁移支持**：提供迁移指南和工具
3. **兼容性维护**：维护6个月的兼容性
4. **正式废弃**：移除废弃功能

### 废弃原则

- **渐进式废弃**：逐步废弃，避免突然中断
- **充分通知**：提前充分通知用户
- **迁移支持**：提供完整的迁移支持
- **文档维护**：维护废弃功能的文档

## 📚 迁移资源

### 迁移指南

- [API迁移指南](../getting-started/migration.md#api-migration)
- [配置迁移指南](../getting-started/migration.md#config-migration)
- [工具迁移指南](../getting-started/migration.md#tool-migration)

### 迁移工具

- [配置转换工具](../tools/migration-tools/)
- [API适配器](../tools/migration-tools/)
- [数据迁移脚本](../tools/migration-tools/)

### 技术支持

- [迁移支持论坛](https://github.com/formal-framework/formal-framework/discussions)
- [技术支持邮箱](mailto:support@formal-framework.org)
- [迁移咨询服务](mailto:migration@formal-framework.org)

## ⚠️ 重要提醒

### 废弃时间表

- **v1.0 API**: 2024-12-31 正式废弃
- **legacy-config**: 2025-03-31 正式废弃
- **old-verification-script**: 2025-06-30 正式废弃

### 影响评估

- **功能影响**：部分功能可能不可用
- **性能影响**：可能影响系统性能
- **安全影响**：可能存在安全风险

## 🔗 相关文档

- [版本发布说明](../community/releases.md)
- [变更日志](../community/changelog.md)
- [迁移指南](../getting-started/migration.md)

---

*最后更新：2024-12-19*-
