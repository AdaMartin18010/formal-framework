#!/usr/bin/env python3
"""
实体DSL编译器
支持将实体DSL转换为SQL DDL、ORM模型等
"""

import re
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from enum import Enum

class FieldType(Enum):
    INT = "int"
    STRING = "string"
    FLOAT = "float"
    DATETIME = "datetime"
    TEXT = "text"
    BOOLEAN = "boolean"

@dataclass
class Field:
    name: str
    type: FieldType
    constraints: List[str]
    default_value: Optional[str] = None
    reference: Optional[str] = None

@dataclass
class Entity:
    name: str
    fields: List[Field]
    relationships: List[Dict[str, Any]] = None

class EntityDSLCompiler:
    """实体DSL编译器"""
    
    def __init__(self):
        self.entities: Dict[str, Entity] = {}
        
    def parse_dsl(self, dsl_content: str) -> Dict[str, Entity]:
        """解析DSL内容"""
        lines = dsl_content.strip().split('\n')
        current_entity = None
        
        for line in lines:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
                
            # 解析实体定义
            if line.startswith('entity '):
                entity_match = re.match(r'entity\s+(\w+)\s*{', line)
                if entity_match:
                    entity_name = entity_match.group(1)
                    current_entity = Entity(
                        name=entity_name,
                        fields=[],
                        relationships=[]
                    )
                    self.entities[entity_name] = current_entity
                    
            # 解析字段定义
            elif current_entity and ':' in line and not line.startswith('}'):
                field = self._parse_field(line)
                if field:
                    current_entity.fields.append(field)
                    
        return self.entities
    
    def _parse_field(self, line: str) -> Optional[Field]:
        """解析字段定义"""
        line = re.sub(r'[,}]$', '', line.strip())
        
        field_match = re.match(r'(\w+):\s*(\w+)', line)
        if not field_match:
            return None
            
        field_name = field_match.group(1)
        field_type_str = field_match.group(2)
        
        try:
            field_type = FieldType(field_type_str)
        except ValueError:
            field_type = FieldType.STRING
            
        constraints = []
        default_value = None
        reference = None
        
        if 'primary key' in line:
            constraints.append('PRIMARY KEY')
        if 'unique' in line:
            constraints.append('UNIQUE')
        if 'not null' in line:
            constraints.append('NOT NULL')
        if 'auto_increment' in line:
            constraints.append('AUTO_INCREMENT')
            
        default_match = re.search(r'default\s+(\w+)', line)
        if default_match:
            default_value = default_match.group(1)
            
        ref_match = re.search(r'references\s+(\w+)\((\w+)\)', line)
        if ref_match:
            reference = f"{ref_match.group(1)}.{ref_match.group(2)}"
            
        return Field(
            name=field_name,
            type=field_type,
            constraints=constraints,
            default_value=default_value,
            reference=reference
        )
    
    def generate_sql_ddl(self) -> str:
        """生成SQL DDL"""
        ddl_lines = []
        
        for entity_name, entity in self.entities.items():
            ddl_lines.append(f"CREATE TABLE {entity_name} (")
            
            field_definitions = []
            for field in entity.fields:
                field_def = self._generate_field_definition(field)
                field_definitions.append(f"  {field_def}")
                
            ddl_lines.append(',\n'.join(field_definitions))
            ddl_lines.append(");\n")
            
        return '\n'.join(ddl_lines)
    
    def _generate_field_definition(self, field: Field) -> str:
        """生成字段定义"""
        type_mapping = {
            FieldType.INT: 'INT',
            FieldType.STRING: 'VARCHAR(255)',
            FieldType.FLOAT: 'FLOAT',
            FieldType.DATETIME: 'DATETIME',
            FieldType.TEXT: 'TEXT',
            FieldType.BOOLEAN: 'BOOLEAN'
        }
        
        sql_type = type_mapping.get(field.type, 'VARCHAR(255)')
        parts = [f"{field.name} {sql_type}"]
        
        for constraint in field.constraints:
            parts.append(constraint)
                
        if field.default_value:
            if field.default_value == 'now':
                parts.append("DEFAULT CURRENT_TIMESTAMP")
            else:
                parts.append(f"DEFAULT {field.default_value}")
                
        return ' '.join(parts)

def main():
    """主函数"""
    sample_dsl = """
    entity User {
      id: int primary key auto_increment
      name: string not null
      email: string unique
      age: int
      created_at: datetime default now
    }

    entity Post {
      id: int primary key auto_increment
      title: string not null
      content: text
      author_id: int references User(id)
    }
    """
    
    compiler = EntityDSLCompiler()
    entities = compiler.parse_dsl(sample_dsl)
    
    print("=== 解析的实体 ===")
    for name, entity in entities.items():
        print(f"Entity: {name}")
        for field in entity.fields:
            print(f"  - {field.name}: {field.type.value}")
    
    print("\n=== 生成的SQL DDL ===")
    print(compiler.generate_sql_ddl())

if __name__ == "__main__":
    main()
