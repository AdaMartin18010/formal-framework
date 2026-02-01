# 概念索引系统 (Concept Index System)

## 概述

概念索引系统是形式化框架项目的核心知识组织系统，旨在为所有核心概念提供统一的索引、导航和学习路径。

## 系统结构

```
concept-index/
├── README.md                    # 本文件
├── CONCEPT_INDEX.md            # 主索引文件（按字母顺序）
├── concepts/                   # 各概念的详细索引页
│   ├── abstract-syntax-tree.md
│   ├── automated-reasoning.md
│   ├── code-generation.md
│   └── ...
└── learning-paths/             # 学习路径相关
    └── concept-dependencies.md  # 概念依赖关系图
```

## 使用指南

### 查找概念

1. **按字母顺序查找**：查看 [CONCEPT_INDEX.md](./CONCEPT_INDEX.md)
2. **按分类查找**：查看各分类索引
3. **按学习路径查找**：查看 [学习路径文档](../../LEARNING_PATHS.md)

### 概念索引页结构

每个概念索引页包含：

- **定义位置**：概念首次定义和详细讲解的位置
- **学习路径**：从基础到高级的学习顺序
- **相关概念**：紧密相关的概念链接
- **应用场景**：概念的实际应用领域
- **难度等级**：学习难度标识（⭐-⭐⭐⭐⭐⭐）
- **前置知识**：学习前需要掌握的概念

## 维护指南

### 添加新概念

1. 在 `CONCEPT_INDEX.md` 中添加条目
2. 在 `concepts/` 目录创建详细索引页
3. 更新相关概念的交叉引用
4. 更新概念依赖关系图

### 更新概念

1. 更新概念索引页内容
2. 检查相关概念的链接
3. 更新学习路径文档

## 相关文档

- [学习路径文档](../../LEARNING_PATHS.md)
- [术语表](../glossary/GLOSSARY.md)
- [概念关系图谱](../concept-maps/CONCEPT_MAPS.md)
