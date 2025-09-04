"""
Data Model Test Suite
Tests for the Data Meta-model including tables, fields, indexes, constraints, and relationships.
"""

import pytest
from dataclasses import dataclass
from typing import Set, Optional, List
from datetime import datetime


@dataclass
class Table:
    """Mock Table entity for testing."""
    id: int
    name: str
    schema: str
    description: str
    is_active: bool
    created_at: str
    updated_at: str


@dataclass
class Field:
    """Mock Field entity for testing."""
    id: int
    table_id: int
    name: str
    data_type: str
    is_nullable: bool
    is_primary_key: bool
    is_unique: bool
    default_value: Optional[str]
    description: str


@dataclass
class Index:
    """Mock Index entity for testing."""
    id: int
    table_id: int
    name: str
    field_ids: Set[int]
    is_unique: bool
    is_active: bool
    description: str


@dataclass
class Constraint:
    """Mock Constraint entity for testing."""
    id: int
    table_id: int
    name: str
    type: str
    field_ids: Set[int]
    expression: str
    is_active: bool


@dataclass
class Relationship:
    """Mock Relationship entity for testing."""
    id: int
    source_table_id: int
    target_table_id: int
    type: str
    source_field_ids: Set[int]
    target_field_ids: Set[int]
    is_active: bool
    description: str


class DataModel:
    """Mock DataModel class for testing."""
    
    def __init__(self):
        self.tables: Set[Table] = set()
        self.fields: Set[Field] = set()
        self.indexes: Set[Index] = set()
        self.constraints: Set[Constraint] = set()
        self.relationships: Set[Relationship] = set()
        self._next_table_id = 1
        self._next_field_id = 1
        self._next_index_id = 1
        self._next_constraint_id = 1
        self._next_relationship_id = 1
    
    def add_table(self, name: str, schema: str, description: str = "") -> Table:
        """Add a new table to the model."""
        table = Table(
            id=self._next_table_id,
            name=name,
            schema=schema,
            description=description,
            is_active=True,
            created_at=datetime.now().isoformat(),
            updated_at=datetime.now().isoformat()
        )
        self.tables.add(table)
        self._next_table_id += 1
        return table
    
    def add_field(self, table_id: int, name: str, data_type: str, 
                  is_nullable: bool = True, is_primary_key: bool = False,
                  is_unique: bool = False, default_value: Optional[str] = None,
                  description: str = "") -> Field:
        """Add a new field to a table."""
        field = Field(
            id=self._next_field_id,
            table_id=table_id,
            name=name,
            data_type=data_type,
            is_nullable=is_nullable,
            is_primary_key=is_primary_key,
            is_unique=is_unique,
            default_value=default_value,
            description=description
        )
        self.fields.add(field)
        self._next_field_id += 1
        return field
    
    def add_index(self, table_id: int, name: str, field_ids: Set[int],
                  is_unique: bool = False, description: str = "") -> Index:
        """Add a new index to a table."""
        index = Index(
            id=self._next_index_id,
            table_id=table_id,
            name=name,
            field_ids=field_ids,
            is_unique=is_unique,
            is_active=True,
            description=description
        )
        self.indexes.add(index)
        self._next_index_id += 1
        return index
    
    def add_constraint(self, table_id: int, name: str, constraint_type: str,
                       field_ids: Set[int], expression: str) -> Constraint:
        """Add a new constraint to a table."""
        constraint = Constraint(
            id=self._next_constraint_id,
            table_id=table_id,
            name=name,
            type=constraint_type,
            field_ids=field_ids,
            expression=expression,
            is_active=True
        )
        self.constraints.add(constraint)
        self._next_constraint_id += 1
        return constraint
    
    def add_relationship(self, source_table_id: int, target_table_id: int,
                         relationship_type: str, source_field_ids: Set[int],
                         target_field_ids: Set[int], description: str = "") -> Relationship:
        """Add a new relationship between tables."""
        relationship = Relationship(
            id=self._next_relationship_id,
            source_table_id=source_table_id,
            target_table_id=target_table_id,
            type=relationship_type,
            source_field_ids=source_field_ids,
            target_field_ids=target_field_ids,
            is_active=True,
            description=description
        )
        self.relationships.add(relationship)
        self._next_relationship_id += 1
        return relationship
    
    def get_table_by_id(self, table_id: int) -> Optional[Table]:
        """Get a table by its ID."""
        for table in self.tables:
            if table.id == table_id:
                return table
        return None
    
    def get_fields_by_table_id(self, table_id: int) -> List[Field]:
        """Get all fields for a specific table."""
        return [field for field in self.fields if field.table_id == table_id]
    
    def get_indexes_by_table_id(self, table_id: int) -> List[Index]:
        """Get all indexes for a specific table."""
        return [index for index in self.indexes if index.table_id == table_id]
    
    def get_constraints_by_table_id(self, table_id: int) -> List[Constraint]:
        """Get all constraints for a specific table."""
        return [constraint for constraint in self.constraints if constraint.table_id == table_id]
    
    def validate_table(self, table: Table) -> bool:
        """Validate a table entity."""
        if not table.name or not table.schema:
            return False
        if table.id <= 0:
            return False
        return True
    
    def validate_field(self, field: Field) -> bool:
        """Validate a field entity."""
        if not field.name or not field.data_type:
            return False
        if field.id <= 0 or field.table_id <= 0:
            return False
        if field.data_type not in ["INTEGER", "VARCHAR", "TEXT", "BOOLEAN", "DATE", "TIMESTAMP", "DECIMAL", "BLOB"]:
            return False
        return True


# Pytest fixtures
@pytest.fixture
def data_model():
    """Fixture providing a fresh DataModel instance."""
    return DataModel()


@pytest.fixture
def sample_table(data_model):
    """Fixture providing a sample table."""
    return data_model.add_table("users", "public", "User table for authentication")


@pytest.fixture
def sample_field(data_model, sample_table):
    """Fixture providing a sample field."""
    return data_model.add_field(
        sample_table.id, "id", "INTEGER", 
        is_nullable=False, is_primary_key=True, 
        description="Primary key"
    )


@pytest.fixture
def sample_index(data_model, sample_table, sample_field):
    """Fixture providing a sample index."""
    return data_model.add_index(
        sample_table.id, "idx_users_id", {sample_field.id},
        is_unique=True, description="Unique index on id"
    )


@pytest.fixture
def sample_constraint(data_model, sample_table, sample_field):
    """Fixture providing a sample constraint."""
    return data_model.add_constraint(
        sample_table.id, "pk_users", "PRIMARY_KEY",
        {sample_field.id}, "id > 0"
    )


@pytest.fixture
def sample_relationship(data_model, sample_table):
    """Fixture providing a sample relationship."""
    target_table = data_model.add_table("profiles", "public", "User profile table")
    source_field = data_model.add_field(sample_table.id, "profile_id", "INTEGER")
    target_field = data_model.add_field(target_table.id, "id", "INTEGER", is_primary_key=True)
    
    return data_model.add_relationship(
        sample_table.id, target_table.id, "ONE_TO_ONE",
        {source_field.id}, {target_field.id},
        "User to profile relationship"
    )


# Test classes
class TestDataModel:
    """Test class for DataModel basic operations."""
    
    def test_add_table(self, data_model):
        """Test adding a table to the model."""
        table = data_model.add_table("test_table", "test_schema", "Test description")
        
        assert table.id == 1
        assert table.name == "test_table"
        assert table.schema == "test_schema"
        assert table.description == "Test description"
        assert table.is_active is True
        assert table in data_model.tables
    
    def test_add_field(self, data_model, sample_table):
        """Test adding a field to a table."""
        field = data_model.add_field(
            sample_table.id, "test_field", "VARCHAR",
            is_nullable=True, is_primary_key=False
        )
        
        assert field.id == 1
        assert field.table_id == sample_table.id
        assert field.name == "test_field"
        assert field.data_type == "VARCHAR"
        assert field.is_nullable is True
        assert field.is_primary_key is False
        assert field in data_model.fields
    
    def test_add_index(self, data_model, sample_table, sample_field):
        """Test adding an index to a table."""
        index = data_model.add_index(
            sample_table.id, "test_index", {sample_field.id},
            is_unique=False
        )
        
        assert index.id == 1
        assert index.table_id == sample_table.id
        assert index.name == "test_index"
        assert sample_field.id in index.field_ids
        assert index.is_unique is False
        assert index in data_model.indexes
    
    def test_add_constraint(self, data_model, sample_table, sample_field):
        """Test adding a constraint to a table."""
        constraint = data_model.add_constraint(
            sample_table.id, "test_constraint", "CHECK",
            {sample_field.id}, "id > 0"
        )
        
        assert constraint.id == 1
        assert constraint.table_id == sample_table.id
        assert constraint.name == "test_constraint"
        assert constraint.type == "CHECK"
        assert sample_field.id in constraint.field_ids
        assert constraint.expression == "id > 0"
        assert constraint in data_model.constraints
    
    def test_add_relationship(self, data_model, sample_table):
        """Test adding a relationship between tables."""
        target_table = data_model.add_table("target_table", "test_schema")
        source_field = data_model.add_field(sample_table.id, "source_field", "INTEGER")
        target_field = data_model.add_field(target_table.id, "target_field", "INTEGER")
        
        relationship = data_model.add_relationship(
            sample_table.id, target_table.id, "MANY_TO_ONE",
            {source_field.id}, {target_field.id},
            "Test relationship"
        )
        
        assert relationship.id == 1
        assert relationship.source_table_id == sample_table.id
        assert relationship.target_table_id == target_table.id
        assert relationship.type == "MANY_TO_ONE"
        assert source_field.id in relationship.source_field_ids
        assert target_field.id in relationship.target_field_ids
        assert relationship in data_model.relationships


class TestDataValidation:
    """Test class for data validation rules."""
    
    def test_table_validation_success(self, data_model):
        """Test successful table validation."""
        table = Table(1, "valid_table", "valid_schema", "Valid description", True, "2023-01-01", "2023-01-01")
        assert data_model.validate_table(table) is True
    
    def test_table_validation_failure_no_name(self, data_model):
        """Test table validation failure due to missing name."""
        table = Table(1, "", "valid_schema", "Valid description", True, "2023-01-01", "2023-01-01")
        assert data_model.validate_table(table) is False
    
    def test_table_validation_failure_no_schema(self, data_model):
        """Test table validation failure due to missing schema."""
        table = Table(1, "valid_table", "", "Valid description", True, "2023-01-01", "2023-01-01")
        assert data_model.validate_table(table) is False
    
    def test_table_validation_failure_invalid_id(self, data_model):
        """Test table validation failure due to invalid ID."""
        table = Table(0, "valid_table", "valid_schema", "Valid description", True, "2023-01-01", "2023-01-01")
        assert data_model.validate_table(table) is False
    
    def test_field_validation_success(self, data_model):
        """Test successful field validation."""
        field = Field(1, 1, "valid_field", "VARCHAR", True, False, False, None, "Valid field")
        assert data_model.validate_field(field) is True
    
    def test_field_validation_failure_no_name(self, data_model):
        """Test field validation failure due to missing name."""
        field = Field(1, 1, "", "VARCHAR", True, False, False, None, "Valid field")
        assert data_model.validate_field(field) is False
    
    def test_field_validation_failure_invalid_data_type(self, data_model):
        """Test field validation failure due to invalid data type."""
        field = Field(1, 1, "valid_field", "INVALID_TYPE", True, False, False, None, "Valid field")
        assert data_model.validate_field(field) is False
    
    def test_field_validation_failure_invalid_id(self, data_model):
        """Test field validation failure due to invalid ID."""
        field = Field(0, 1, "valid_field", "VARCHAR", True, False, False, None, "Valid field")
        assert data_model.validate_field(field) is False


class TestModelConstraints:
    """Test class for model constraints and invariants."""
    
    def test_table_uniqueness(self, data_model):
        """Test that table IDs are unique."""
        table1 = data_model.add_table("table1", "schema1")
        table2 = data_model.add_table("table2", "schema2")
        
        assert table1.id != table2.id
        assert len(data_model.tables) == 2
    
    def test_field_uniqueness(self, data_model, sample_table):
        """Test that field IDs are unique."""
        field1 = data_model.add_field(sample_table.id, "field1", "VARCHAR")
        field2 = data_model.add_field(sample_table.id, "field2", "INTEGER")
        
        assert field1.id != field2.id
        assert len(data_model.fields) == 2
    
    def test_field_table_association(self, data_model, sample_table):
        """Test that fields are properly associated with tables."""
        field = data_model.add_field(sample_table.id, "test_field", "VARCHAR")
        
        table_fields = data_model.get_fields_by_table_id(sample_table.id)
        assert field in table_fields
        assert len(table_fields) == 1
    
    def test_index_table_association(self, data_model, sample_table, sample_field):
        """Test that indexes are properly associated with tables."""
        index = data_model.add_index(sample_table.id, "test_index", {sample_field.id})
        
        table_indexes = data_model.get_indexes_by_table_id(sample_table.id)
        assert index in table_indexes
        assert len(table_indexes) == 1
    
    def test_constraint_table_association(self, data_model, sample_table, sample_field):
        """Test that constraints are properly associated with tables."""
        constraint = data_model.add_constraint(sample_table.id, "test_constraint", "CHECK", {sample_field.id}, "id > 0")
        
        table_constraints = data_model.get_constraints_by_table_id(sample_table.id)
        assert constraint in table_constraints
        assert len(table_constraints) == 1
    
    def test_primary_key_constraint(self, data_model, sample_table):
        """Test that each table has at least one primary key field."""
        # Add a primary key field
        primary_key_field = data_model.add_field(
            sample_table.id, "id", "INTEGER",
            is_nullable=False, is_primary_key=True
        )
        
        table_fields = data_model.get_fields_by_table_id(sample_table.id)
        primary_key_fields = [f for f in table_fields if f.is_primary_key]
        
        assert len(primary_key_fields) >= 1
        assert primary_key_field in primary_key_fields
    
    def test_unique_constraint(self, data_model, sample_table):
        """Test unique constraint validation."""
        # Add a unique field
        unique_field = data_model.add_field(
            sample_table.id, "email", "VARCHAR",
            is_unique=True
        )
        
        # Try to add another field with the same name (should not affect uniqueness)
        another_field = data_model.add_field(
            sample_table.id, "email", "VARCHAR",
            is_unique=False
        )
        
        # The first field should remain unique
        assert unique_field.is_unique is True
        assert another_field.is_unique is False


class TestPerformance:
    """Test class for performance benchmarks."""
    
    def test_add_multiple_tables(self, data_model):
        """Test adding multiple tables performance."""
        start_time = datetime.now()
        
        for i in range(100):
            data_model.add_table(f"table_{i}", f"schema_{i}", f"Description {i}")
        
        end_time = datetime.now()
        duration = (end_time - start_time).total_seconds()
        
        assert len(data_model.tables) == 100
        assert duration < 1.0  # Should complete within 1 second
    
    def test_add_multiple_fields(self, data_model, sample_table):
        """Test adding multiple fields performance."""
        start_time = datetime.now()
        
        for i in range(100):
            data_model.add_field(
                sample_table.id, f"field_{i}", "VARCHAR",
                description=f"Field {i}"
            )
        
        end_time = datetime.now()
        duration = (end_time - start_time).total_seconds()
        
        assert len(data_model.fields) == 100
        assert duration < 1.0  # Should complete within 1 second
    
    def test_search_by_table_id(self, data_model):
        """Test searching for tables by ID performance."""
        # Add many tables
        for i in range(100):
            data_model.add_table(f"table_{i}", f"schema_{i}")
        
        start_time = datetime.now()
        
        # Search for a specific table
        target_table = data_model.get_table_by_id(50)
        
        end_time = datetime.now()
        duration = (end_time - start_time).total_seconds()
        
        assert target_table is not None
        assert target_table.id == 50
        assert duration < 0.1  # Should complete within 0.1 seconds


# Parameterized tests
@pytest.mark.parametrize("data_type", ["INTEGER", "VARCHAR", "TEXT", "BOOLEAN", "DATE", "TIMESTAMP", "DECIMAL", "BLOB"])
def test_valid_data_types(data_model, sample_table, data_type):
    """Test that all valid data types are accepted."""
    field = data_model.add_field(sample_table.id, f"field_{data_type}", data_type)
    assert field.data_type == data_type
    assert data_model.validate_field(field) is True


@pytest.mark.parametrize("invalid_data_type", ["INVALID", "CUSTOM_TYPE", "123", ""])
def test_invalid_data_types(data_model, sample_table, invalid_data_type):
    """Test that invalid data types are rejected."""
    field = Field(1, sample_table.id, "test_field", invalid_data_type, True, False, False, None, "Test")
    assert data_model.validate_field(field) is False


@pytest.mark.parametrize("relationship_type", ["ONE_TO_ONE", "ONE_TO_MANY", "MANY_TO_ONE", "MANY_TO_MANY"])
def test_relationship_types(data_model, sample_table, relationship_type):
    """Test different relationship types."""
    target_table = data_model.add_table("target_table", "test_schema")
    source_field = data_model.add_field(sample_table.id, "source_field", "INTEGER")
    target_field = data_model.add_field(target_table.id, "target_field", "INTEGER")
    
    relationship = data_model.add_relationship(
        sample_table.id, target_table.id, relationship_type,
        {source_field.id}, {target_field.id}
    )
    
    assert relationship.type == relationship_type
    assert relationship in data_model.relationships


# Marked tests for different execution categories
@pytest.mark.slow
def test_large_scale_operations(data_model):
    """Test large-scale operations (marked as slow)."""
    # Add 1000 tables with 10 fields each
    for i in range(1000):
        table = data_model.add_table(f"large_table_{i}", f"schema_{i}")
        for j in range(10):
            data_model.add_field(table.id, f"field_{j}", "VARCHAR")
    
    assert len(data_model.tables) == 1000
    assert len(data_model.fields) == 10000


@pytest.mark.integration
def test_full_model_integration(data_model):
    """Test full model integration (marked as integration)."""
    # Create a complete data model with all entity types
    users_table = data_model.add_table("users", "public", "Users table")
    profiles_table = data_model.add_table("profiles", "public", "Profiles table")
    
    # Add fields
    user_id = data_model.add_field(users_table.id, "id", "INTEGER", is_primary_key=True)
    user_email = data_model.add_field(users_table.id, "email", "VARCHAR", is_unique=True)
    profile_id = data_model.add_field(profiles_table.id, "id", "INTEGER", is_primary_key=True)
    profile_user_id = data_model.add_field(profiles_table.id, "user_id", "INTEGER")
    
    # Add indexes
    data_model.add_index(users_table.id, "idx_users_email", {user_email.id}, is_unique=True)
    data_model.add_index(profiles_table.id, "idx_profiles_user_id", {profile_user_id.id})
    
    # Add constraints
    data_model.add_constraint(users_table.id, "pk_users", "PRIMARY_KEY", {user_id.id}, "")
    data_model.add_constraint(profiles_table.id, "pk_profiles", "PRIMARY_KEY", {profile_id.id}, "")
    
    # Add relationship
    data_model.add_relationship(
        users_table.id, profiles_table.id, "ONE_TO_ONE",
        {user_id.id}, {profile_id.id},
        "User profile relationship"
    )
    
    # Verify the complete model
    assert len(data_model.tables) == 2
    assert len(data_model.fields) == 4
    assert len(data_model.indexes) == 2
    assert len(data_model.constraints) == 2
    assert len(data_model.relationships) == 1
    
    # Verify relationships
    user_fields = data_model.get_fields_by_table_id(users_table.id)
    profile_fields = data_model.get_fields_by_table_id(profiles_table.id)
    
    assert len(user_fields) == 2
    assert len(profile_fields) == 2
