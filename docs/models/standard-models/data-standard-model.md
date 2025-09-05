# 数据标准模型

## 概述

数据标准模型定义了系统数据结构和关系的标准化实现，基于数据元模型构建，提供统一的数据格式、存储方案和访问接口。

## 标准数据结构

### 1. 基础数据类型

#### 标准字段类型

```yaml
StandardFieldTypes:
  primitive:
    string:
      max_length: 255
      encoding: utf-8
      validation: regex_pattern
    integer:
      min_value: -2147483648
      max_value: 2147483647
      format: int32
    float:
      precision: 15
      scale: 2
      format: double
    boolean:
      values: [true, false]
      default: false
    datetime:
      format: ISO8601
      timezone: UTC
      precision: milliseconds
  
  complex:
    json:
      schema: JSONSchema
      validation: strict
    array:
      element_type: FieldType
      max_length: 1000
    object:
      properties: Property[]
      required: string[]
```

#### 实现示例

```python
from pydantic import BaseModel, Field, validator
from typing import Optional, List, Dict, Any
from datetime import datetime
import json

class StandardField(BaseModel):
    """标准字段定义"""
    name: str = Field(..., max_length=255)
    type: str = Field(..., regex="^(string|integer|float|boolean|datetime|json|array|object)$")
    required: bool = False
    default: Optional[Any] = None
    validation: Optional[Dict[str, Any]] = None
    
    @validator('name')
    def validate_name(cls, v):
        if not v.isidentifier():
            raise ValueError('字段名必须是有效的标识符')
        return v

class StandardDataModel(BaseModel):
    """标准数据模型"""
    id: str = Field(..., description="唯一标识符")
    created_at: datetime = Field(default_factory=datetime.utcnow)
    updated_at: datetime = Field(default_factory=datetime.utcnow)
    version: int = Field(default=1, ge=1)
    metadata: Dict[str, Any] = Field(default_factory=dict)
    
    class Config:
        json_encoders = {
            datetime: lambda v: v.isoformat()
        }
```

### 2. 关系数据模型

#### 标准关系类型

```yaml
StandardRelationships:
  one_to_one:
    type: "1:1"
    constraints:
      - unique
      - not_null
    example: "User -> Profile"
  
  one_to_many:
    type: "1:N"
    constraints:
      - foreign_key
    example: "User -> Orders"
  
  many_to_many:
    type: "N:N"
    constraints:
      - junction_table
    example: "Users <-> Roles"
  
  hierarchical:
    type: "tree"
    constraints:
      - parent_id
      - level
    example: "Categories"
```

#### 实现示例1

```python
from sqlalchemy import Column, Integer, String, DateTime, ForeignKey, Table
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import relationship
from datetime import datetime

Base = declarative_base()

# 多对多关系表
user_roles = Table(
    'user_roles',
    Base.metadata,
    Column('user_id', Integer, ForeignKey('users.id'), primary_key=True),
    Column('role_id', Integer, ForeignKey('roles.id'), primary_key=True)
)

class User(Base):
    """用户模型 - 一对多关系示例"""
    __tablename__ = 'users'
    
    id = Column(Integer, primary_key=True)
    username = Column(String(50), unique=True, nullable=False)
    email = Column(String(100), unique=True, nullable=False)
    created_at = Column(DateTime, default=datetime.utcnow)
    
    # 一对多关系
    orders = relationship("Order", back_populates="user")
    # 多对多关系
    roles = relationship("Role", secondary=user_roles, back_populates="users")

class Order(Base):
    """订单模型"""
    __tablename__ = 'orders'
    
    id = Column(Integer, primary_key=True)
    user_id = Column(Integer, ForeignKey('users.id'), nullable=False)
    total_amount = Column(Integer, nullable=False)
    status = Column(String(20), default='pending')
    created_at = Column(DateTime, default=datetime.utcnow)
    
    # 多对一关系
    user = relationship("User", back_populates="orders")

class Role(Base):
    """角色模型"""
    __tablename__ = 'roles'
    
    id = Column(Integer, primary_key=True)
    name = Column(String(50), unique=True, nullable=False)
    description = Column(String(200))
    
    # 多对多关系
    users = relationship("User", secondary=user_roles, back_populates="roles")
```

### 3. 时序数据模型

#### 时序数据结构

```yaml
TimeSeriesModel:
  timestamp:
    type: datetime
    precision: milliseconds
    timezone: UTC
  
  value:
    type: numeric|string|boolean
    encoding: binary|text
  
  tags:
    type: map<string, string>
    cardinality: high
  
  metadata:
    type: map<string, any>
    cardinality: low
```

#### 实现示例2

```python
import pandas as pd
from datetime import datetime, timedelta
from typing import Dict, List, Any
import numpy as np

class TimeSeriesData:
    """时序数据模型"""
    
    def __init__(self, name: str, tags: Dict[str, str] = None):
        self.name = name
        self.tags = tags or {}
        self.data = []
        self.metadata = {}
    
    def add_point(self, timestamp: datetime, value: Any, metadata: Dict[str, Any] = None):
        """添加数据点"""
        point = {
            'timestamp': timestamp,
            'value': value,
            'metadata': metadata or {}
        }
        self.data.append(point)
    
    def to_dataframe(self) -> pd.DataFrame:
        """转换为DataFrame"""
        if not self.data:
            return pd.DataFrame()
        
        df = pd.DataFrame(self.data)
        df.set_index('timestamp', inplace=True)
        return df
    
    def resample(self, frequency: str) -> pd.DataFrame:
        """重采样"""
        df = self.to_dataframe()
        if df.empty:
            return df
        
        return df['value'].resample(frequency).agg(['mean', 'min', 'max', 'count'])

class TimeSeriesDatabase:
    """时序数据库接口"""
    
    def __init__(self, connection_string: str):
        self.connection_string = connection_string
        self.series = {}
    
    def create_series(self, name: str, tags: Dict[str, str] = None) -> TimeSeriesData:
        """创建时序数据"""
        series = TimeSeriesData(name, tags)
        self.series[name] = series
        return series
    
    def query_series(self, name: str, start_time: datetime, end_time: datetime) -> pd.DataFrame:
        """查询时序数据"""
        if name not in self.series:
            raise ValueError(f"时序数据不存在: {name}")
        
        series = self.series[name]
        df = series.to_dataframe()
        
        if df.empty:
            return df
        
        return df.loc[start_time:end_time]
```

## 标准存储方案

### 1. 关系型数据库

#### 标准表结构

```sql
-- 标准表结构模板
CREATE TABLE standard_entities (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    version INTEGER DEFAULT 1,
    status VARCHAR(20) DEFAULT 'active',
    metadata JSONB,
    
    -- 审计字段
    created_by VARCHAR(100),
    updated_by VARCHAR(100),
    
    -- 软删除
    deleted_at TIMESTAMP WITH TIME ZONE,
    
    -- 索引
    CONSTRAINT chk_status CHECK (status IN ('active', 'inactive', 'archived'))
);

-- 创建索引
CREATE INDEX idx_standard_entities_created_at ON standard_entities(created_at);
CREATE INDEX idx_standard_entities_status ON standard_entities(status);
CREATE INDEX idx_standard_entities_metadata ON standard_entities USING GIN(metadata);

-- 创建触发器
CREATE OR REPLACE FUNCTION update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = CURRENT_TIMESTAMP;
    NEW.version = OLD.version + 1;
    RETURN NEW;
END;
$$ language 'plpgsql';

CREATE TRIGGER update_standard_entities_updated_at
    BEFORE UPDATE ON standard_entities
    FOR EACH ROW
    EXECUTE FUNCTION update_updated_at_column();
```

### 2. 文档数据库

#### 标准文档结构

```json
{
  "_id": "uuid",
  "_type": "entity_type",
  "_version": 1,
  "_created_at": "2024-01-01T00:00:00Z",
  "_updated_at": "2024-01-01T00:00:00Z",
  "_status": "active",
  "_metadata": {
    "source": "system",
    "tags": ["tag1", "tag2"],
    "permissions": {
      "read": ["user1", "user2"],
      "write": ["user1"]
    }
  },
  "data": {
    "field1": "value1",
    "field2": "value2",
    "nested": {
      "field3": "value3"
    }
  }
}
```

#### 实现示例3

```python
from pymongo import MongoClient
from datetime import datetime
from typing import Dict, Any, List
import uuid

class DocumentDatabase:
    """文档数据库标准实现"""
    
    def __init__(self, connection_string: str, database_name: str):
        self.client = MongoClient(connection_string)
        self.db = self.client[database_name]
    
    def create_document(self, collection: str, data: Dict[str, Any]) -> str:
        """创建文档"""
        document_id = str(uuid.uuid4())
        document = {
            "_id": document_id,
            "_type": collection,
            "_version": 1,
            "_created_at": datetime.utcnow(),
            "_updated_at": datetime.utcnow(),
            "_status": "active",
            "_metadata": {
                "source": "system",
                "tags": [],
                "permissions": {
                    "read": [],
                    "write": []
                }
            },
            "data": data
        }
        
        self.db[collection].insert_one(document)
        return document_id
    
    def update_document(self, collection: str, document_id: str, data: Dict[str, Any]) -> bool:
        """更新文档"""
        result = self.db[collection].update_one(
            {"_id": document_id},
            {
                "$set": {
                    "data": data,
                    "_updated_at": datetime.utcnow()
                },
                "$inc": {"_version": 1}
            }
        )
        return result.modified_count > 0
    
    def query_documents(self, collection: str, query: Dict[str, Any]) -> List[Dict[str, Any]]:
        """查询文档"""
        return list(self.db[collection].find(query))
```

### 3. 键值存储

#### 标准键值结构

```yaml
KeyValueStructure:
  key:
    format: "namespace:type:id"
    example: "user:profile:12345"
    encoding: string
  
  value:
    format: json|binary|string
    compression: gzip|lz4
    encryption: aes256
  
  metadata:
    ttl: seconds
    version: integer
    created_at: timestamp
    updated_at: timestamp
```

#### 实现示例4

```python
import redis
import json
import pickle
from datetime import datetime, timedelta
from typing import Any, Optional, Union

class KeyValueStore:
    """键值存储标准实现"""
    
    def __init__(self, connection_string: str):
        self.redis = redis.from_url(connection_string)
    
    def set(self, key: str, value: Any, ttl: Optional[int] = None) -> bool:
        """设置键值"""
        serialized_value = self._serialize(value)
        return self.redis.set(key, serialized_value, ex=ttl)
    
    def get(self, key: str) -> Optional[Any]:
        """获取值"""
        serialized_value = self.redis.get(key)
        if serialized_value is None:
            return None
        return self._deserialize(serialized_value)
    
    def delete(self, key: str) -> bool:
        """删除键"""
        return self.redis.delete(key) > 0
    
    def exists(self, key: str) -> bool:
        """检查键是否存在"""
        return self.redis.exists(key) > 0
    
    def _serialize(self, value: Any) -> bytes:
        """序列化值"""
        if isinstance(value, (dict, list)):
            return json.dumps(value).encode('utf-8')
        else:
            return pickle.dumps(value)
    
    def _deserialize(self, data: bytes) -> Any:
        """反序列化值"""
        try:
            return json.loads(data.decode('utf-8'))
        except (json.JSONDecodeError, UnicodeDecodeError):
            return pickle.loads(data)
```

## 标准数据访问接口

### 1. CRUD操作接口

#### 标准CRUD接口

```python
from abc import ABC, abstractmethod
from typing import List, Optional, Dict, Any
from pydantic import BaseModel

class CRUDInterface(ABC):
    """标准CRUD接口"""
    
    @abstractmethod
    def create(self, data: BaseModel) -> str:
        """创建记录"""
        pass
    
    @abstractmethod
    def read(self, id: str) -> Optional[BaseModel]:
        """读取记录"""
        pass
    
    @abstractmethod
    def update(self, id: str, data: BaseModel) -> bool:
        """更新记录"""
        pass
    
    @abstractmethod
    def delete(self, id: str) -> bool:
        """删除记录"""
        pass
    
    @abstractmethod
    def list(self, filters: Dict[str, Any] = None, limit: int = 100, offset: int = 0) -> List[BaseModel]:
        """列出记录"""
        pass

class StandardCRUDRepository(CRUDInterface):
    """标准CRUD实现"""
    
    def __init__(self, model_class: type, db_session):
        self.model_class = model_class
        self.db_session = db_session
    
    def create(self, data: BaseModel) -> str:
        """创建记录"""
        instance = self.model_class(**data.dict())
        self.db_session.add(instance)
        self.db_session.commit()
        return str(instance.id)
    
    def read(self, id: str) -> Optional[BaseModel]:
        """读取记录"""
        instance = self.db_session.query(self.model_class).filter_by(id=id).first()
        if instance:
            return self.model_class.from_orm(instance)
        return None
    
    def update(self, id: str, data: BaseModel) -> bool:
        """更新记录"""
        instance = self.db_session.query(self.model_class).filter_by(id=id).first()
        if instance:
            for key, value in data.dict().items():
                setattr(instance, key, value)
            self.db_session.commit()
            return True
        return False
    
    def delete(self, id: str) -> bool:
        """删除记录"""
        instance = self.db_session.query(self.model_class).filter_by(id=id).first()
        if instance:
            self.db_session.delete(instance)
            self.db_session.commit()
            return True
        return False
    
    def list(self, filters: Dict[str, Any] = None, limit: int = 100, offset: int = 0) -> List[BaseModel]:
        """列出记录"""
        query = self.db_session.query(self.model_class)
        
        if filters:
            for key, value in filters.items():
                if hasattr(self.model_class, key):
                    query = query.filter(getattr(self.model_class, key) == value)
        
        instances = query.offset(offset).limit(limit).all()
        return [self.model_class.from_orm(instance) for instance in instances]
```

### 2. 查询接口

#### 标准查询接口

```python
from typing import List, Dict, Any, Optional
from enum import Enum

class QueryOperator(Enum):
    """查询操作符"""
    EQ = "eq"          # 等于
    NE = "ne"          # 不等于
    GT = "gt"          # 大于
    GTE = "gte"        # 大于等于
    LT = "lt"          # 小于
    LTE = "lte"        # 小于等于
    IN = "in"          # 包含
    NIN = "nin"        # 不包含
    LIKE = "like"      # 模糊匹配
    REGEX = "regex"    # 正则匹配

class QueryCondition:
    """查询条件"""
    
    def __init__(self, field: str, operator: QueryOperator, value: Any):
        self.field = field
        self.operator = operator
        self.value = value

class StandardQueryBuilder:
    """标准查询构建器"""
    
    def __init__(self):
        self.conditions = []
        self.sort_fields = []
        self.limit_value = None
        self.offset_value = 0
    
    def where(self, field: str, operator: QueryOperator, value: Any) -> 'StandardQueryBuilder':
        """添加查询条件"""
        self.conditions.append(QueryCondition(field, operator, value))
        return self
    
    def order_by(self, field: str, ascending: bool = True) -> 'StandardQueryBuilder':
        """添加排序"""
        self.sort_fields.append((field, ascending))
        return self
    
    def limit(self, count: int) -> 'StandardQueryBuilder':
        """设置限制"""
        self.limit_value = count
        return self
    
    def offset(self, count: int) -> 'StandardQueryBuilder':
        """设置偏移"""
        self.offset_value = count
        return self
    
    def build(self) -> Dict[str, Any]:
        """构建查询"""
        query = {
            "conditions": [
                {
                    "field": c.field,
                    "operator": c.operator.value,
                    "value": c.value
                }
                for c in self.conditions
            ],
            "sort": self.sort_fields,
            "limit": self.limit_value,
            "offset": self.offset_value
        }
        return query
```

## 标准数据验证

### 1. 数据完整性验证

#### 完整性约束

```python
from pydantic import BaseModel, validator, Field
from typing import List, Dict, Any
import re

class DataIntegrityValidator:
    """数据完整性验证器"""
    
    @staticmethod
    def validate_email(email: str) -> bool:
        """验证邮箱格式"""
        pattern = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        return re.match(pattern, email) is not None
    
    @staticmethod
    def validate_phone(phone: str) -> bool:
        """验证手机号格式"""
        pattern = r'^\+?1?\d{9,15}$'
        return re.match(pattern, phone) is not None
    
    @staticmethod
    def validate_uuid(uuid_str: str) -> bool:
        """验证UUID格式"""
        pattern = r'^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$'
        return re.match(pattern, uuid_str, re.IGNORECASE) is not None

class StandardDataModel(BaseModel):
    """标准数据模型"""
    id: str = Field(..., description="唯一标识符")
    email: str = Field(..., description="邮箱地址")
    phone: str = Field(..., description="手机号")
    created_at: datetime = Field(default_factory=datetime.utcnow)
    
    @validator('id')
    def validate_id(cls, v):
        if not DataIntegrityValidator.validate_uuid(v):
            raise ValueError('ID必须是有效的UUID格式')
        return v
    
    @validator('email')
    def validate_email(cls, v):
        if not DataIntegrityValidator.validate_email(v):
            raise ValueError('邮箱格式不正确')
        return v
    
    @validator('phone')
    def validate_phone(cls, v):
        if not DataIntegrityValidator.validate_phone(v):
            raise ValueError('手机号格式不正确')
        return v
```

### 2. 数据一致性验证

#### 一致性检查

```python
from typing import List, Dict, Any, Tuple
import hashlib

class DataConsistencyChecker:
    """数据一致性检查器"""
    
    def __init__(self):
        self.checks = []
    
    def add_check(self, name: str, check_func: callable):
        """添加一致性检查"""
        self.checks.append((name, check_func))
    
    def run_checks(self, data: Dict[str, Any]) -> List[Tuple[str, bool, str]]:
        """运行所有检查"""
        results = []
        for name, check_func in self.checks:
            try:
                is_consistent, message = check_func(data)
                results.append((name, is_consistent, message))
            except Exception as e:
                results.append((name, False, f"检查失败: {str(e)}"))
        return results
    
    def check_referential_integrity(self, data: Dict[str, Any]) -> Tuple[bool, str]:
        """检查引用完整性"""
        # 实现引用完整性检查逻辑
        return True, "引用完整性检查通过"
    
    def check_data_hash(self, data: Dict[str, Any]) -> Tuple[bool, str]:
        """检查数据哈希"""
        data_str = str(sorted(data.items()))
        calculated_hash = hashlib.md5(data_str.encode()).hexdigest()
        stored_hash = data.get('_hash')
        
        if stored_hash and calculated_hash != stored_hash:
            return False, "数据哈希不匹配"
        
        return True, "数据哈希检查通过"

# 使用示例
checker = DataConsistencyChecker()
checker.add_check("referential_integrity", checker.check_referential_integrity)
checker.add_check("data_hash", checker.check_data_hash)

results = checker.run_checks(sample_data)
for name, is_consistent, message in results:
    print(f"{name}: {'通过' if is_consistent else '失败'} - {message}")
```

## 标准数据迁移

### 1. 数据迁移策略

#### 迁移类型

```yaml
MigrationTypes:
  schema_migration:
    description: "数据库结构变更"
    examples:
      - "添加新字段"
      - "修改字段类型"
      - "创建新表"
  
  data_migration:
    description: "数据格式转换"
    examples:
      - "数据格式升级"
      - "编码转换"
      - "数据清理"
  
  platform_migration:
    description: "平台迁移"
    examples:
      - "数据库迁移"
      - "云平台迁移"
      - "版本升级"
```

#### 实现示例5

```python
from abc import ABC, abstractmethod
from typing import List, Dict, Any
from datetime import datetime
import logging

class Migration(ABC):
    """数据迁移基类"""
    
    def __init__(self, version: str, description: str):
        self.version = version
        self.description = description
        self.logger = logging.getLogger(self.__class__.__name__)
    
    @abstractmethod
    def up(self) -> bool:
        """执行迁移"""
        pass
    
    @abstractmethod
    def down(self) -> bool:
        """回滚迁移"""
        pass
    
    def execute(self) -> bool:
        """执行迁移"""
        try:
            self.logger.info(f"开始执行迁移: {self.version} - {self.description}")
            result = self.up()
            if result:
                self.logger.info(f"迁移成功: {self.version}")
            else:
                self.logger.error(f"迁移失败: {self.version}")
            return result
        except Exception as e:
            self.logger.error(f"迁移异常: {self.version} - {str(e)}")
            return False

class SchemaMigration(Migration):
    """结构迁移"""
    
    def __init__(self, version: str, description: str, sql_up: str, sql_down: str):
        super().__init__(version, description)
        self.sql_up = sql_up
        self.sql_down = sql_down
    
    def up(self) -> bool:
        """执行结构迁移"""
        # 执行SQL语句
        return self._execute_sql(self.sql_up)
    
    def down(self) -> bool:
        """回滚结构迁移"""
        # 执行回滚SQL语句
        return self._execute_sql(self.sql_down)
    
    def _execute_sql(self, sql: str) -> bool:
        """执行SQL语句"""
        try:
            # 这里应该连接到数据库执行SQL
            self.logger.info(f"执行SQL: {sql}")
            return True
        except Exception as e:
            self.logger.error(f"SQL执行失败: {str(e)}")
            return False

class DataMigration(Migration):
    """数据迁移"""
    
    def __init__(self, version: str, description: str, transform_func: callable):
        super().__init__(version, description)
        self.transform_func = transform_func
    
    def up(self) -> bool:
        """执行数据迁移"""
        try:
            return self.transform_func()
        except Exception as e:
            self.logger.error(f"数据转换失败: {str(e)}")
            return False
    
    def down(self) -> bool:
        """回滚数据迁移"""
        # 数据迁移通常难以回滚
        self.logger.warning("数据迁移无法回滚")
        return False
```

## 最佳实践

1. **数据建模**: 遵循标准的数据建模原则
2. **类型安全**: 使用强类型定义数据结构
3. **验证机制**: 实现完整的数据验证
4. **一致性保证**: 确保数据一致性
5. **性能优化**: 优化数据访问性能
6. **安全考虑**: 实现数据安全保护
7. **文档维护**: 保持数据模型文档的更新

## 相关文档

- [数据元模型](../meta-models/data-model/README.md)
- [验证脚本](../../tools/verification-scripts/README.md)
- [监控工具](../../tools/monitoring/README.md)
