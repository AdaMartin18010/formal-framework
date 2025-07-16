# 基础设施建模DSL草案

## 1. 设计目标

- 用统一DSL描述计算、网络、存储、安全等基础设施要素。
- 支持自动生成Terraform、Pulumi、CloudFormation等IaC脚本。

## 2. 基本语法结构

```dsl
infrastructure cloud {
  provider: "aws"
  region: "us-east-1"
  resources: [
    vm { type: "t3.medium" count: 2 },
    vpc { cidr: "10.0.0.0/16" },
    subnet { cidr: "10.0.1.0/24" },
    lb { type: "application" },
    ebs { size: "100Gi" }
  ]
}

infrastructure onprem {
  provider: "openstack"
  resources: [
    vm { type: "highmem" count: 4 },
    network { vlan: 100 },
    storage { type: "nfs" size: "1Ti" }
  ]
}
```

## 3. 关键元素

- infrastructure：基础设施声明
- provider/region/resources：云厂商、区域、资源
- vm/vpc/subnet/lb/ebs/network/storage：资源类型

## 4. 常用基础设施声明方式一览（表格）

| 语法示例                                      | 说明           |
|-----------------------------------------------|----------------|
| infrastructure cloud { ... }                  | 云基础设施定义  |
| provider: "aws"/"azure"/"gcp"                | 云厂商         |
| vm { type: "t3.medium" count: 2 }             | 虚拟机资源     |
| vpc/subnet/lb/ebs                             | 网络与存储资源 |
| infrastructure onprem { ... }                 | 本地/私有云定义 |
| network { vlan: 100 }                         | VLAN网络       |
| storage { type: "nfs" size: "1Ti" }           | 存储资源       |

## 5. 与主流标准的映射

- 可自动转换为Terraform、Pulumi、CloudFormation等IaC脚本
- 支持与主流云平台、私有云工具集成

## 6. 递归扩展建议

- 支持多云、混合云、弹性伸缩、自动备份
- 支持资源依赖与安全策略建模
