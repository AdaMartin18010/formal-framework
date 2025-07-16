# 存储建模DSL草案

## 1. 设计目标

- 用统一DSL描述存储类型、挂载、容量、访问策略、备份等要素。
- 支持自动生成K8s PersistentVolume、StorageClass、Ceph、NFS等配置。

## 2. 基本语法结构

```dsl
storage data_volume {
  type: nfs
  server: "nfs.example.com"
  path: "/data"
  capacity: "100Gi"
  access: "ReadWriteMany"
  mount: "/mnt/data"
  backup: {
    schedule: "0 2 * * *"
    retention: 7
  }
}

storage db_volume {
  type: block
  capacity: "500Gi"
  mount: "/var/lib/db"
  access: "ReadWriteOnce"
  class: "fast-ssd"
}
```

## 3. 关键元素

- storage：存储声明
- type/server/path/capacity/access/mount：类型、服务器、路径、容量、权限、挂载
- backup/class：备份策略、存储类

## 4. 常用存储声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| storage data_volume { ... }                   | 存储定义       |
| type: nfs/block/object/local/distributed      | 存储类型       |
| server/path/capacity                          | 服务器、路径、容量 |
| access: ReadWriteOnce/Many                    | 访问权限       |
| mount: "/mnt/data"                            | 挂载路径       |
| backup: { schedule: ... }                     | 备份策略       |
| class: "fast-ssd"                             | 存储类         |

## 5. 与主流标准的映射

- 可自动转换为K8s PersistentVolume、StorageClass、Ceph、NFS等配置
- 支持与主流存储与备份工具集成

## 6. 递归扩展建议

- 支持快照、动态扩容、自动恢复
- 支持多存储类型混合与策略切换
