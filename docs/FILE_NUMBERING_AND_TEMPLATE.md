# 文档编号规范与通用模板

## 1. 编号规范

```text
FileNumbering = {
  LevelNumber: L{1-4},      // L1:理论基础, L2:元模型, L3:标准模型, L4:行业应用
  DomainNumber: D{01-99},   // 01:交互, 02:数据, 03:功能, 04:运行时, 05:部署, 06:监控, 07:控制调度, 08:测试, 09:CI/CD, 10:分布式模式, 90+:行业
  ModelNumber: M{001-999},  // 具体模型编号
  VersionNumber: V{1.0-9.9} // 版本
}

FileName = "L{Level}_D{Domain}_M{Model}_V{Version}_{Description}.md"
```

示例：

- L1_D01_M001_V1.0_集合论基础.md
- L2_D02_M005_V1.0_数据元模型.md
- L3_D03_M010_V1.0_功能标准模型.md
- L4_D90_M020_V1.0_金融_支付网关_对标报告.md

## 2. 文档通用模板

复制如下模板作为新文档起始：

```markdown
---
id: L{Level}_D{Domain}_M{Model}_V{Version}
title: {Title}
level: {LevelName}
domain: {DomainName}
model: {ModelName}
version: {Version}
status: draft
author: {Author}
date: {YYYY-MM-DD}
tags: [theory, model, proof, application]
---

## 目录
- [1. 概述](#1-概述)
- [2. 理论基础](#2-理论基础)
- [3. 元模型/模型定义](#3-元模型模型定义)
- [4. 形式化证明](#4-形式化证明)
- [5. 国际对标与术语对齐](#5-国际对标与术语对齐)
- [6. 成熟案例与实践](#6-成熟案例与实践)
- [7. 结论与后续工作](#7-结论与后续工作)
- [附录 A. 参考文献](#附录-a-参考文献)

## 1. 概述

## 2. 理论基础

## 3. 元模型/模型定义

## 4. 形式化证明

## 5. 国际对标与术语对齐

## 6. 成熟案例与实践

## 7. 结论与后续工作

## 附录 A. 参考文献
```

## 3. 质量与评审清单

- 元数据完整：编号、标题、版本、作者、日期
- 目录齐全：7 个主节 + 参考文献
- 引用可追溯：符合 `docs/CITATION_STANDARDS.md`
- 形式化片段：至少包含一种证明策略（集合/图/范畴/类型/逻辑）
- 对标矩阵：至少包含 1 个标准或开源案例对比
- 评审状态：记录在文末 ReviewStatus
