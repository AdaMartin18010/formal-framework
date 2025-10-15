# 代码示例增强指南 (Code Examples Enhancement Guide)

## 📋 概述

本文档提供了形式化框架项目中代码示例的标准格式和最佳实践，确保代码示例的一致性、可读性和实用性。

## 🎯 代码示例分类

### 1. 基础概念示例

#### AST构建示例

```python
# 抽象语法树构建示例
class ASTNode:
    def __init__(self, node_type, value=None, children=None):
        self.node_type = node_type
        self.value = value
        self.children = children or []
        
    def add_child(self, child):
        self.children.append(child)
        
    def traverse(self, visitor):
        """访问者模式遍历AST"""
        visitor.visit(self)
        for child in self.children:
            child.traverse(visitor)

class BinaryExpression(ASTNode):
    def __init__(self, operator, left, right):
        super().__init__('binary_expression', operator)
        self.add_child(left)
        self.add_child(right)

# 使用示例
left = ASTNode('literal', 5)
right = ASTNode('literal', 3)
expr = BinaryExpression('+', left, right)

class PrintVisitor:
    def visit(self, node):
        print(f"Node: {node.node_type}, Value: {node.value}")

visitor = PrintVisitor()
expr.traverse(visitor)
```

#### DSL解析示例

```python
# 简单DSL解析器示例
import re
from dataclasses import dataclass
from typing import List, Dict, Any

@dataclass
class DSLToken:
    type: str
    value: str
    line: int
    column: int

class DSLParser:
    def __init__(self):
        self.tokens = []
        self.current = 0
        
    def tokenize(self, source: str) -> List[DSLToken]:
        """词法分析"""
        token_specs = [
            ('NUMBER', r'\d+'),
            ('IDENTIFIER', r'[a-zA-Z_][a-zA-Z0-9_]*'),
            ('ASSIGN', r'='),
            ('PLUS', r'\+'),
            ('MINUS', r'-'),
            ('MULTIPLY', r'\*'),
            ('DIVIDE', r'/'),
            ('LPAREN', r'\('),
            ('RPAREN', r'\)'),
            ('NEWLINE', r'\n'),
            ('SKIP', r'[ \t]+'),
        ]
        
        tokens = []
        line_num = 1
        line_start = 0
        
        for mo in re.finditer('|'.join(f'(?P<{name}>{pattern})' 
                                      for name, pattern in token_specs), source):
            kind = mo.lastgroup
            value = mo.group()
            column = mo.start() - line_start
            
            if kind == 'NEWLINE':
                line_start = mo.end()
                line_num += 1
            elif kind != 'SKIP':
                tokens.append(DSLToken(kind, value, line_num, column))
                
        return tokens
    
    def parse(self, source: str) -> Dict[str, Any]:
        """语法分析"""
        self.tokens = self.tokenize(source)
        self.current = 0
        return self.parse_expression()
    
    def parse_expression(self) -> Dict[str, Any]:
        """解析表达式"""
        left = self.parse_term()
        
        while self.current < len(self.tokens) and self.tokens[self.current].type in ['PLUS', 'MINUS']:
            op = self.tokens[self.current].type
            self.current += 1
            right = self.parse_term()
            left = {'type': 'binary_op', 'operator': op, 'left': left, 'right': right}
            
        return left
    
    def parse_term(self) -> Dict[str, Any]:
        """解析项"""
        left = self.parse_factor()
        
        while self.current < len(self.tokens) and self.tokens[self.current].type in ['MULTIPLY', 'DIVIDE']:
            op = self.tokens[self.current].type
            self.current += 1
            right = self.parse_factor()
            left = {'type': 'binary_op', 'operator': op, 'left': left, 'right': right}
            
        return left
    
    def parse_factor(self) -> Dict[str, Any]:
        """解析因子"""
        if self.current >= len(self.tokens):
            raise SyntaxError("Unexpected end of input")
            
        token = self.tokens[self.current]
        
        if token.type == 'NUMBER':
            self.current += 1
            return {'type': 'number', 'value': int(token.value)}
        elif token.type == 'IDENTIFIER':
            self.current += 1
            return {'type': 'identifier', 'name': token.value}
        elif token.type == 'LPAREN':
            self.current += 1
            expr = self.parse_expression()
            if self.current >= len(self.tokens) or self.tokens[self.current].type != 'RPAREN':
                raise SyntaxError("Expected ')'")
            self.current += 1
            return expr
        else:
            raise SyntaxError(f"Unexpected token: {token.value}")

# 使用示例
parser = DSLParser()
result = parser.parse("2 + 3 * 4")
print(result)
# 输出: {'type': 'binary_op', 'operator': 'PLUS', 'left': {'type': 'number', 'value': 2}, 'right': {'type': 'binary_op', 'operator': 'MULTIPLY', 'left': {'type': 'number', 'value': 3}, 'right': {'type': 'number', 'value': 4}}}
```

### 2. 模型转换示例

#### 数据模型转换

```python
# 数据模型转换示例
from typing import Dict, List, Any
from dataclasses import dataclass

@dataclass
class Field:
    name: str
    type: str
    nullable: bool = False
    default: Any = None
    constraints: List[str] = None

@dataclass
class Entity:
    name: str
    fields: List[Field]
    primary_key: List[str] = None
    indexes: List[Dict[str, Any]] = None

class ModelTransformer:
    def __init__(self):
        self.transformers = {
            'sql': self.to_sql,
            'json': self.to_json,
            'yaml': self.to_yaml,
            'prisma': self.to_prisma,
        }
    
    def transform(self, entity: Entity, target_format: str) -> str:
        """转换实体到目标格式"""
        if target_format not in self.transformers:
            raise ValueError(f"Unsupported format: {target_format}")
        
        return self.transformers[target_format](entity)
    
    def to_sql(self, entity: Entity) -> str:
        """转换为SQL DDL"""
        fields = []
        for field in entity.fields:
            field_def = f"    {field.name} {field.type.upper()}"
            if not field.nullable:
                field_def += " NOT NULL"
            if field.default is not None:
                field_def += f" DEFAULT {field.default}"
            fields.append(field_def)
        
        sql = f"CREATE TABLE {entity.name} (\n"
        sql += ",\n".join(fields)
        
        if entity.primary_key:
            sql += f",\n    PRIMARY KEY ({', '.join(entity.primary_key)})"
        
        sql += "\n);"
        return sql
    
    def to_json(self, entity: Entity) -> Dict[str, Any]:
        """转换为JSON Schema"""
        properties = {}
        required = []
        
        for field in entity.fields:
            properties[field.name] = {
                "type": field.type,
                "description": f"{field.name} field"
            }
            if not field.nullable:
                required.append(field.name)
        
        schema = {
            "type": "object",
            "properties": properties,
            "required": required
        }
        
        return schema
    
    def to_yaml(self, entity: Entity) -> str:
        """转换为YAML配置"""
        yaml = f"entity: {entity.name}\n"
        yaml += "fields:\n"
        
        for field in entity.fields:
            yaml += f"  - name: {field.name}\n"
            yaml += f"    type: {field.type}\n"
            yaml += f"    nullable: {field.nullable}\n"
            if field.default is not None:
                yaml += f"    default: {field.default}\n"
        
        return yaml
    
    def to_prisma(self, entity: Entity) -> str:
        """转换为Prisma Schema"""
        prisma = f"model {entity.name} {{\n"
        
        for field in entity.fields:
            field_def = f"  {field.name} {field.type}"
            if not field.nullable:
                field_def += "?"
            prisma += field_def + "\n"
        
        prisma += "}\n"
        return prisma

# 使用示例
user_entity = Entity(
    name="User",
    fields=[
        Field("id", "int", nullable=False),
        Field("name", "string", nullable=False),
        Field("email", "string", nullable=False),
        Field("age", "int", nullable=True, default=0),
    ],
    primary_key=["id"]
)

transformer = ModelTransformer()

# 转换为SQL
sql = transformer.transform(user_entity, "sql")
print("SQL DDL:")
print(sql)

# 转换为JSON Schema
json_schema = transformer.transform(user_entity, "json")
print("\nJSON Schema:")
print(json_schema)

# 转换为YAML
yaml = transformer.transform(user_entity, "yaml")
print("\nYAML:")
print(yaml)

# 转换为Prisma Schema
prisma = transformer.transform(user_entity, "prisma")
print("\nPrisma Schema:")
print(prisma)
```

### 3. 行业应用示例

#### 金融交易处理

```python
# 金融交易处理示例
from enum import Enum
from dataclasses import dataclass
from typing import Dict, List, Optional
from decimal import Decimal
from datetime import datetime

class TransactionType(Enum):
    DEPOSIT = "deposit"
    WITHDRAWAL = "withdrawal"
    TRANSFER = "transfer"
    PAYMENT = "payment"

class TransactionStatus(Enum):
    PENDING = "pending"
    PROCESSING = "processing"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"

@dataclass
class Account:
    account_id: str
    customer_id: str
    balance: Decimal
    currency: str
    status: str = "active"
    
    def can_transact(self, amount: Decimal) -> bool:
        return self.balance >= amount and self.status == "active"

@dataclass
class Transaction:
    transaction_id: str
    account_id: str
    transaction_type: TransactionType
    amount: Decimal
    currency: str
    status: TransactionStatus
    created_at: datetime
    completed_at: Optional[datetime] = None
    description: Optional[str] = None
    
    def is_completed(self) -> bool:
        return self.status == TransactionStatus.COMPLETED

class TransactionProcessor:
    def __init__(self):
        self.accounts: Dict[str, Account] = {}
        self.transactions: Dict[str, Transaction] = {}
        self.rules = TransactionRules()
    
    def create_account(self, account_id: str, customer_id: str, 
                      initial_balance: Decimal, currency: str) -> Account:
        """创建账户"""
        account = Account(account_id, customer_id, initial_balance, currency)
        self.accounts[account_id] = account
        return account
    
    def process_transaction(self, transaction: Transaction) -> bool:
        """处理交易"""
        try:
            # 验证交易
            if not self.rules.validate_transaction(transaction):
                transaction.status = TransactionStatus.FAILED
                return False
            
            # 获取账户
            account = self.accounts.get(transaction.account_id)
            if not account:
                transaction.status = TransactionStatus.FAILED
                return False
            
            # 处理不同类型的交易
            if transaction.transaction_type == TransactionType.DEPOSIT:
                return self._process_deposit(account, transaction)
            elif transaction.transaction_type == TransactionType.WITHDRAWAL:
                return self._process_withdrawal(account, transaction)
            elif transaction.transaction_type == TransactionType.TRANSFER:
                return self._process_transfer(account, transaction)
            else:
                transaction.status = TransactionStatus.FAILED
                return False
                
        except Exception as e:
            transaction.status = TransactionStatus.FAILED
            print(f"Transaction processing failed: {e}")
            return False
    
    def _process_deposit(self, account: Account, transaction: Transaction) -> bool:
        """处理存款"""
        account.balance += transaction.amount
        transaction.status = TransactionStatus.COMPLETED
        transaction.completed_at = datetime.now()
        self.transactions[transaction.transaction_id] = transaction
        return True
    
    def _process_withdrawal(self, account: Account, transaction: Transaction) -> bool:
        """处理取款"""
        if not account.can_transact(transaction.amount):
            transaction.status = TransactionStatus.FAILED
            return False
        
        account.balance -= transaction.amount
        transaction.status = TransactionStatus.COMPLETED
        transaction.completed_at = datetime.now()
        self.transactions[transaction.transaction_id] = transaction
        return True
    
    def _process_transfer(self, account: Account, transaction: Transaction) -> bool:
        """处理转账"""
        # 这里需要目标账户信息，简化处理
        if not account.can_transact(transaction.amount):
            transaction.status = TransactionStatus.FAILED
            return False
        
        account.balance -= transaction.amount
        transaction.status = TransactionStatus.COMPLETED
        transaction.completed_at = datetime.now()
        self.transactions[transaction.transaction_id] = transaction
        return True

class TransactionRules:
    def __init__(self):
        self.min_amount = Decimal('0.01')
        self.max_amount = Decimal('1000000.00')
        self.daily_limit = Decimal('50000.00')
    
    def validate_transaction(self, transaction: Transaction) -> bool:
        """验证交易规则"""
        # 检查金额范围
        if transaction.amount < self.min_amount or transaction.amount > self.max_amount:
            return False
        
        # 检查货币
        if transaction.currency not in ['USD', 'EUR', 'GBP', 'CNY']:
            return False
        
        # 检查交易类型
        if transaction.transaction_type not in TransactionType:
            return False
        
        return True

# 使用示例
processor = TransactionProcessor()

# 创建账户
account = processor.create_account(
    account_id="ACC001",
    customer_id="CUST001",
    initial_balance=Decimal('1000.00'),
    currency="USD"
)

# 创建交易
transaction = Transaction(
    transaction_id="TXN001",
    account_id="ACC001",
    transaction_type=TransactionType.DEPOSIT,
    amount=Decimal('500.00'),
    currency="USD",
    status=TransactionStatus.PENDING,
    created_at=datetime.now(),
    description="Salary deposit"
)

# 处理交易
success = processor.process_transaction(transaction)
print(f"Transaction processed: {success}")
print(f"Account balance: {account.balance}")
print(f"Transaction status: {transaction.status}")
```

#### AI模型服务

```python
# AI模型服务示例
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from enum import Enum
import asyncio
import json
from datetime import datetime

class ModelType(Enum):
    CLASSIFICATION = "classification"
    REGRESSION = "regression"
    CLUSTERING = "clustering"
    NLP = "nlp"
    COMPUTER_VISION = "computer_vision"

class ModelStatus(Enum):
    LOADING = "loading"
    READY = "ready"
    SERVING = "serving"
    ERROR = "error"
    OFFLINE = "offline"

@dataclass
class ModelMetadata:
    model_id: str
    name: str
    version: str
    model_type: ModelType
    input_schema: Dict[str, Any]
    output_schema: Dict[str, Any]
    created_at: datetime
    updated_at: datetime
    performance_metrics: Dict[str, float] = None

@dataclass
class PredictionRequest:
    request_id: str
    model_id: str
    input_data: Dict[str, Any]
    timestamp: datetime
    client_id: Optional[str] = None

@dataclass
class PredictionResponse:
    request_id: str
    model_id: str
    prediction: Any
    confidence: Optional[float] = None
    processing_time: Optional[float] = None
    timestamp: datetime = None
    error: Optional[str] = None

class ModelService:
    def __init__(self):
        self.models: Dict[str, Any] = {}
        self.metadata: Dict[str, ModelMetadata] = {}
        self.status: Dict[str, ModelStatus] = {}
        self.request_history: List[PredictionRequest] = []
    
    async def load_model(self, model_id: str, model_path: str, 
                        metadata: ModelMetadata) -> bool:
        """加载模型"""
        try:
            self.status[model_id] = ModelStatus.LOADING
            
            # 模拟模型加载
            await asyncio.sleep(2)  # 模拟加载时间
            
            # 这里应该是实际的模型加载逻辑
            # model = load_model_from_path(model_path)
            # self.models[model_id] = model
            
            self.models[model_id] = f"Mock model for {model_id}"
            self.metadata[model_id] = metadata
            self.status[model_id] = ModelStatus.READY
            
            return True
            
        except Exception as e:
            self.status[model_id] = ModelStatus.ERROR
            print(f"Failed to load model {model_id}: {e}")
            return False
    
    async def predict(self, request: PredictionRequest) -> PredictionResponse:
        """执行预测"""
        start_time = datetime.now()
        
        try:
            # 检查模型状态
            if self.status.get(request.model_id) != ModelStatus.READY:
                return PredictionResponse(
                    request_id=request.request_id,
                    model_id=request.model_id,
                    prediction=None,
                    timestamp=datetime.now(),
                    error="Model not ready"
                )
            
            # 验证输入数据
            if not self._validate_input(request.model_id, request.input_data):
                return PredictionResponse(
                    request_id=request.request_id,
                    model_id=request.model_id,
                    prediction=None,
                    timestamp=datetime.now(),
                    error="Invalid input data"
                )
            
            # 执行预测
            prediction = await self._execute_prediction(request.model_id, request.input_data)
            
            # 计算处理时间
            processing_time = (datetime.now() - start_time).total_seconds()
            
            # 记录请求历史
            self.request_history.append(request)
            
            return PredictionResponse(
                request_id=request.request_id,
                model_id=request.model_id,
                prediction=prediction,
                confidence=0.95,  # 模拟置信度
                processing_time=processing_time,
                timestamp=datetime.now()
            )
            
        except Exception as e:
            return PredictionResponse(
                request_id=request.request_id,
                model_id=request.model_id,
                prediction=None,
                timestamp=datetime.now(),
                error=str(e)
            )
    
    def _validate_input(self, model_id: str, input_data: Dict[str, Any]) -> bool:
        """验证输入数据"""
        metadata = self.metadata.get(model_id)
        if not metadata:
            return False
        
        # 检查必需字段
        required_fields = metadata.input_schema.get('required', [])
        for field in required_fields:
            if field not in input_data:
                return False
        
        # 检查数据类型
        properties = metadata.input_schema.get('properties', {})
        for field, value in input_data.items():
            if field in properties:
                expected_type = properties[field].get('type')
                if expected_type and not isinstance(value, self._get_python_type(expected_type)):
                    return False
        
        return True
    
    def _get_python_type(self, json_type: str):
        """将JSON类型转换为Python类型"""
        type_mapping = {
            'string': str,
            'integer': int,
            'number': float,
            'boolean': bool,
            'array': list,
            'object': dict
        }
        return type_mapping.get(json_type, object)
    
    async def _execute_prediction(self, model_id: str, input_data: Dict[str, Any]) -> Any:
        """执行预测（模拟）"""
        # 模拟预测处理时间
        await asyncio.sleep(0.1)
        
        # 模拟预测结果
        if self.metadata[model_id].model_type == ModelType.CLASSIFICATION:
            return {"class": "positive", "probability": 0.85}
        elif self.metadata[model_id].model_type == ModelType.REGRESSION:
            return {"value": 42.5, "range": [40.0, 45.0]}
        else:
            return {"result": "mock_prediction"}
    
    def get_model_status(self, model_id: str) -> ModelStatus:
        """获取模型状态"""
        return self.status.get(model_id, ModelStatus.OFFLINE)
    
    def get_model_metrics(self, model_id: str) -> Dict[str, Any]:
        """获取模型指标"""
        metadata = self.metadata.get(model_id)
        if not metadata:
            return {}
        
        return {
            "model_id": model_id,
            "status": self.status.get(model_id).value,
            "total_requests": len([r for r in self.request_history if r.model_id == model_id]),
            "performance_metrics": metadata.performance_metrics or {}
        }

# 使用示例
async def main():
    service = ModelService()
    
    # 创建模型元数据
    metadata = ModelMetadata(
        model_id="model_001",
        name="Sentiment Analysis Model",
        version="1.0.0",
        model_type=ModelType.CLASSIFICATION,
        input_schema={
            "type": "object",
            "properties": {
                "text": {"type": "string"},
                "language": {"type": "string"}
            },
            "required": ["text"]
        },
        output_schema={
            "type": "object",
            "properties": {
                "class": {"type": "string"},
                "probability": {"type": "number"}
            }
        },
        created_at=datetime.now(),
        updated_at=datetime.now(),
        performance_metrics={"accuracy": 0.92, "f1_score": 0.89}
    )
    
    # 加载模型
    success = await service.load_model("model_001", "/path/to/model", metadata)
    print(f"Model loaded: {success}")
    
    # 创建预测请求
    request = PredictionRequest(
        request_id="req_001",
        model_id="model_001",
        input_data={"text": "I love this product!", "language": "en"},
        timestamp=datetime.now()
    )
    
    # 执行预测
    response = await service.predict(request)
    print(f"Prediction: {response.prediction}")
    print(f"Confidence: {response.confidence}")
    print(f"Processing time: {response.processing_time}s")
    
    # 获取模型指标
    metrics = service.get_model_metrics("model_001")
    print(f"Model metrics: {metrics}")

# 运行示例
# asyncio.run(main())
```

### 4. 工具集成示例

#### 文档生成工具

```python
# 文档生成工具示例
import os
import json
from typing import Dict, List, Any
from dataclasses import dataclass, asdict
from pathlib import Path
import yaml

@dataclass
class DocumentSection:
    title: str
    content: str
    subsections: List['DocumentSection'] = None
    code_examples: List[str] = None
    references: List[str] = None

@dataclass
class DocumentMetadata:
    title: str
    description: str
    author: str
    version: str
    last_updated: str
    tags: List[str] = None
    related_documents: List[str] = None

class DocumentGenerator:
    def __init__(self, output_dir: str = "generated_docs"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.templates = self._load_templates()
    
    def _load_templates(self) -> Dict[str, str]:
        """加载文档模板"""
        return {
            "markdown": self._get_markdown_template(),
            "html": self._get_html_template(),
            "pdf": self._get_pdf_template()
        }
    
    def _get_markdown_template(self) -> str:
        """获取Markdown模板"""
        return """# {title}

## 概述

{description}

## 目录

{toc}

## 内容

{content}

## 参考文献

{references}

---

*最后更新: {last_updated}*
*作者: {author}*
*版本: {version}*
"""
    
    def _get_html_template(self) -> str:
        """获取HTML模板"""
        return """<!DOCTYPE html>
<html>
<head>
    <title>{title}</title>
    <meta charset="utf-8">
    <style>
        body {{ font-family: Arial, sans-serif; margin: 40px; }}
        h1 {{ color: #333; }}
        h2 {{ color: #666; }}
        code {{ background-color: #f4f4f4; padding: 2px 4px; }}
        pre {{ background-color: #f4f4f4; padding: 10px; overflow-x: auto; }}
    </style>
</head>
<body>
    <h1>{title}</h1>
    <p><strong>概述:</strong> {description}</p>
    
    <h2>目录</h2>
    {toc}
    
    <h2>内容</h2>
    {content}
    
    <h2>参考文献</h2>
    {references}
    
    <hr>
    <p><em>最后更新: {last_updated}</em><br>
    <em>作者: {author}</em><br>
    <em>版本: {version}</em></p>
</body>
</html>"""
    
    def generate_document(self, metadata: DocumentMetadata, 
                         sections: List[DocumentSection], 
                         format_type: str = "markdown") -> str:
        """生成文档"""
        if format_type not in self.templates:
            raise ValueError(f"Unsupported format: {format_type}")
        
        template = self.templates[format_type]
        
        # 生成目录
        toc = self._generate_toc(sections)
        
        # 生成内容
        content = self._generate_content(sections)
        
        # 生成参考文献
        references = self._generate_references(sections)
        
        # 填充模板
        document = template.format(
            title=metadata.title,
            description=metadata.description,
            toc=toc,
            content=content,
            references=references,
            last_updated=metadata.last_updated,
            author=metadata.author,
            version=metadata.version
        )
        
        return document
    
    def _generate_toc(self, sections: List[DocumentSection]) -> str:
        """生成目录"""
        toc = ""
        for i, section in enumerate(sections, 1):
            toc += f"{i}. [{section.title}](#{section.title.lower().replace(' ', '-')})\n"
            if section.subsections:
                for j, subsection in enumerate(section.subsections, 1):
                    toc += f"   {i}.{j}. [{subsection.title}](#{subsection.title.lower().replace(' ', '-')})\n"
        return toc
    
    def _generate_content(self, sections: List[DocumentSection]) -> str:
        """生成内容"""
        content = ""
        for section in sections:
            content += f"## {section.title}\n\n"
            content += f"{section.content}\n\n"
            
            if section.code_examples:
                content += "### 代码示例\n\n"
                for example in section.code_examples:
                    content += f"```python\n{example}\n```\n\n"
            
            if section.subsections:
                for subsection in section.subsections:
                    content += f"### {subsection.title}\n\n"
                    content += f"{subsection.content}\n\n"
        
        return content
    
    def _generate_references(self, sections: List[DocumentSection]) -> str:
        """生成参考文献"""
        references = []
        for section in sections:
            if section.references:
                references.extend(section.references)
        
        # 去重
        unique_references = list(set(references))
        
        ref_text = ""
        for i, ref in enumerate(unique_references, 1):
            ref_text += f"{i}. {ref}\n"
        
        return ref_text
    
    def save_document(self, document: str, filename: str, format_type: str = "markdown"):
        """保存文档"""
        if format_type == "markdown":
            filepath = self.output_dir / f"{filename}.md"
        elif format_type == "html":
            filepath = self.output_dir / f"{filename}.html"
        else:
            filepath = self.output_dir / f"{filename}.txt"
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(document)
        
        return filepath
    
    def generate_multiple_formats(self, metadata: DocumentMetadata, 
                                 sections: List[DocumentSection], 
                                 filename: str) -> Dict[str, Path]:
        """生成多种格式的文档"""
        results = {}
        
        for format_type in self.templates.keys():
            document = self.generate_document(metadata, sections, format_type)
            filepath = self.save_document(document, filename, format_type)
            results[format_type] = filepath
        
        return results

# 使用示例
def create_sample_document():
    # 创建文档元数据
    metadata = DocumentMetadata(
        title="形式化框架使用指南",
        description="本文档介绍了形式化框架的基本概念和使用方法",
        author="Formal Framework Team",
        version="1.0.0",
        last_updated="2024-12-19",
        tags=["formal-methods", "dsl", "modeling"],
        related_documents=["README.md", "API_DOCUMENTATION.md"]
    )
    
    # 创建文档章节
    sections = [
        DocumentSection(
            title="概述",
            content="形式化框架是一个基于数学基础和形式化方法的软件工程知识规范与模型设计平台。",
            code_examples=[
                "from formal_framework import Model\nmodel = Model('example')"
            ]
        ),
        DocumentSection(
            title="核心概念",
            content="框架包含多个核心概念，包括抽象语法树、领域特定语言等。",
            subsections=[
                DocumentSection(
                    title="抽象语法树",
                    content="AST是源代码的树状表示，用于程序分析和转换。"
                ),
                DocumentSection(
                    title="领域特定语言",
                    content="DSL是专门为特定问题域设计的编程语言。"
                )
            ]
        ),
        DocumentSection(
            title="使用示例",
            content="以下是一些基本的使用示例。",
            code_examples=[
                """# 创建数据模型
from formal_framework import DataModel

model = DataModel("User")
model.add_field("id", "int", primary_key=True)
model.add_field("name", "string", nullable=False)
model.add_field("email", "string", unique=True)

# 生成SQL
sql = model.to_sql()
print(sql)"""
            ],
            references=[
                "Aho, A. V., et al. (2006). 'Compilers: Principles, Techniques, and Tools'",
                "Fowler, M. (2010). 'Domain-Specific Languages'"
            ]
        )
    ]
    
    # 生成文档
    generator = DocumentGenerator()
    results = generator.generate_multiple_formats(metadata, sections, "formal_framework_guide")
    
    print("Generated documents:")
    for format_type, filepath in results.items():
        print(f"  {format_type}: {filepath}")
    
    return results

# 运行示例
# create_sample_document()
```

## 📋 代码示例规范

### 1. 格式规范

- **语言标识**: 所有代码块必须指定语言
- **注释完整**: 关键代码必须有详细注释
- **变量命名**: 使用有意义的变量名
- **错误处理**: 包含适当的错误处理逻辑

### 2. 内容规范

- **实用性**: 示例必须能够实际运行
- **完整性**: 包含完整的导入和依赖
- **可读性**: 代码结构清晰，易于理解
- **扩展性**: 提供扩展和定制的可能性

### 3. 文档规范

- **说明文字**: 每个示例前有详细说明
- **使用场景**: 说明适用的使用场景
- **注意事项**: 提供重要的注意事项
- **相关链接**: 链接到相关文档和资源

## 🎯 最佳实践

### 1. 示例选择

- 选择具有代表性的示例
- 覆盖不同的使用场景
- 从简单到复杂的渐进式示例
- 包含实际项目中的应用案例

### 2. 代码质量

- 遵循PEP 8编码规范
- 使用类型提示
- 包含单元测试
- 提供性能优化建议

### 3. 文档维护

- 定期更新示例代码
- 验证代码的可运行性
- 收集用户反馈
- 持续改进示例质量

---

*最后更新: 2024-12-19*
*维护者: Formal Framework Team*
