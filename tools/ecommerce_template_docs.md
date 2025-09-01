# ECommerceSystem 模型文档

**模型类型**: business_model

## 实体定义

### User

用户实体

#### 属性

| 属性名 | 类型 | 描述 |
|--------|------|------|
| id | string | 用户ID |
| name | string | 用户姓名 |
| email | string | 邮箱地址 |
| phone | string | 电话号码 |

### Product

商品实体

#### 属性1

| 属性名 | 类型 | 描述 |
|--------|------|------|
| id | string | 商品ID |
| name | string | 商品名称 |
| price | number | 商品价格 |
| category | string | 商品分类 |

### Order

订单实体

#### 属性2

| 属性名 | 类型 | 描述 |
|--------|------|------|
| id | string | 订单ID |
| user_id | string | 用户ID |
| total_amount | number | 订单总金额 |
| status | string | 订单状态 |

## 操作定义

### createUser

创建用户

#### 参数

| 参数名 | 类型 | 描述 |
|--------|------|------|
| name | string | 用户姓名 |
| email | string | 邮箱地址 |

#### 返回值

类型: `User`

### createProduct

创建商品

#### 参数1

| 参数名 | 类型 | 描述 |
|--------|------|------|
| name | string | 商品名称 |
| price | number | 商品价格 |

#### 返回值1

类型: `Product`
