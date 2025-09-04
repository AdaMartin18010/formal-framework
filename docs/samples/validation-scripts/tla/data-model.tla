---------------------------- MODULE DataModel ----------------------------
(*
  Data Model TLA+ Specification
  Defines formal specification for the Data Meta-model including:
  - Data entities (Table, Field, Index, Constraint, etc.)
  - Relationships and constraints
  - Data integrity invariants
  - CRUD operations
*)

EXTENDS Naturals, Sequences, FiniteSets

(* Constants *)
CONSTANTS MaxTables, MaxFields, MaxIndexes, MaxConstraints, MaxRelationships

(* Types *)
VARIABLES tables, fields, indexes, constraints, relationships, dataTypes

(* State variables *)
VARIABLES tableIds, fieldIds, indexIds, constraintIds, relationshipIds

(* Type definitions *)
TableId == 1..MaxTables
FieldId == 1..MaxFields
IndexId == 1..MaxIndexes
ConstraintId == 1..MaxConstraints
RelationshipId == 1..MaxRelationships

(* Data type definitions *)
DataType == {"INTEGER", "VARCHAR", "TEXT", "BOOLEAN", "DATE", "TIMESTAMP", "DECIMAL", "BLOB"}

(* Structure definitions *)
Table == [id: TableId, name: STRING, schema: STRING, description: STRING, 
          isActive: BOOLEAN, createdAt: STRING, updatedAt: STRING]

Field == [id: FieldId, tableId: TableId, name: STRING, dataType: DataType, 
          isNullable: BOOLEAN, isPrimaryKey: BOOLEAN, isUnique: BOOLEAN,
          defaultValue: STRING, description: STRING]

Index == [id: IndexId, tableId: TableId, name: STRING, fieldIds: SUBSET FieldId,
          isUnique: BOOLEAN, isActive: BOOLEAN, description: STRING]

Constraint == [id: ConstraintId, tableId: TableId, name: STRING, type: STRING,
               fieldIds: SUBSET FieldId, expression: STRING, isActive: BOOLEAN]

Relationship == [id: RelationshipId, sourceTableId: TableId, targetTableId: TableId,
                 type: STRING, sourceFieldIds: SUBSET FieldId, targetFieldIds: SUBSET FieldId,
                 isActive: BOOLEAN, description: STRING]

(* Initial state *)
Init == 
    /\ tables = {}
    /\ fields = {}
    /\ indexes = {}
    /\ constraints = {}
    /\ relationships = {}
    /\ tableIds = {}
    /\ fieldIds = {}
    /\ indexIds = {}
    /\ constraintIds = {}
    /\ relationshipIds = {}

(* Actions *)

(* Add a new table *)
AddTable(table) ==
    /\ table.id \notin tableIds
    /\ tableIds' = tableIds \union {table.id}
    /\ tables' = tables \union {table}
    /\ UNCHANGED <<fields, indexes, constraints, relationships, fieldIds, indexIds, constraintIds, relationshipIds>>

(* Add a new field *)
AddField(field) ==
    /\ field.id \notin fieldIds
    /\ field.tableId \in tableIds
    /\ fieldIds' = fieldIds \union {field.id}
    /\ fields' = fields \union {field}
    /\ UNCHANGED <<tables, indexes, constraints, relationships, tableIds, indexIds, constraintIds, relationshipIds>>

(* Add a new index *)
AddIndex(index) ==
    /\ index.id \notin indexIds
    /\ index.tableId \in tableIds
    /\ \A fieldId \in index.fieldIds: fieldId \in fieldIds
    /\ indexIds' = indexIds \union {index.id}
    /\ indexes' = indexes \union {index}
    /\ UNCHANGED <<tables, fields, constraints, relationships, tableIds, fieldIds, indexIds, relationshipIds>>

(* Add a new constraint *)
AddConstraint(constraint) ==
    /\ constraint.id \notin constraintIds
    /\ constraint.tableId \in tableIds
    /\ \A fieldId \in constraint.fieldIds: fieldId \in fieldIds
    /\ constraintIds' = constraintIds \union {constraint.id}
    /\ constraints' = constraints \union {constraint}
    /\ UNCHANGED <<tables, fields, indexes, relationships, tableIds, fieldIds, indexIds, relationshipIds>>

(* Add a new relationship *)
AddRelationship(relationship) ==
    /\ relationship.id \notin relationshipIds
    /\ relationship.sourceTableId \in tableIds
    /\ relationship.targetTableId \in tableIds
    /\ \A fieldId \in relationship.sourceFieldIds: fieldId \in fieldIds
    /\ \A fieldId \in relationship.targetFieldIds: fieldId \in fieldIds
    /\ relationshipIds' = relationshipIds \union {relationship.id}
    /\ relationships' = relationships \union {relationship}
    /\ UNCHANGED <<tables, fields, indexes, constraints, tableIds, fieldIds, indexIds, constraintIds>>

(* Update table *)
UpdateTable(tableId, updates) ==
    /\ tableId \in tableIds
    /\ tables' = {t \in tables: IF t.id = tableId THEN [t EXCEPT !.name = updates.name, !.description = updates.description, !.updatedAt = updates.updatedAt] ELSE t}
    /\ UNCHANGED <<fields, indexes, constraints, relationships, tableIds, fieldIds, indexIds, constraintIds, relationshipIds>>

(* Update field *)
UpdateField(fieldId, updates) ==
    /\ fieldId \in fieldIds
    /\ fields' = {f \in fields: IF f.id = fieldId THEN [f EXCEPT !.name = updates.name, !.isNullable = updates.isNullable, !.isUnique = updates.isUnique, !.description = updates.description] ELSE f}
    /\ UNCHANGED <<tables, indexes, constraints, relationships, tableIds, fieldIds, indexIds, constraintIds, relationshipIds>>

(* Next state relation *)
Next == 
    \/ \E table \in Table: AddTable(table)
    \/ \E field \in Field: AddField(field)
    \/ \E index \in Index: AddIndex(index)
    \/ \E constraint \in Constraint: AddConstraint(constraint)
    \/ \E relationship \in Relationship: AddRelationship(relationship)
    \/ \E tableId \in tableIds, updates \in [name: STRING, description: STRING, updatedAt: STRING]: UpdateTable(tableId, updates)
    \/ \E fieldId \in fieldIds, updates \in [name: STRING, isNullable: BOOLEAN, isUnique: BOOLEAN, description: STRING]: UpdateField(fieldId, updates)

(* Invariants *)

(* Table uniqueness *)
TableUniqueness == 
    \A t1, t2 \in tables: t1.id = t2.id => t1 = t2

(* Field uniqueness *)
FieldUniqueness == 
    \A f1, f2 \in fields: f1.id = f2.id => f1 = f2

(* Index uniqueness *)
IndexUniqueness == 
    \A i1, i2 \in indexes: i1.id = i2.id => i1 = i2

(* Constraint uniqueness *)
ConstraintUniqueness == 
    \A c1, c2 \in constraints: c1.id = c2.id => c1 = c2

(* Relationship uniqueness *)
RelationshipUniqueness == 
    \A r1, r2 \in relationships: r1.id = r2.id => r1 = r2

(* Table integrity *)
TableIntegrity == 
    \A t \in tables: t.id \in tableIds

(* Field integrity *)
FieldIntegrity == 
    \A f \in fields: f.id \in fieldIds /\ f.tableId \in tableIds

(* Index integrity *)
IndexIntegrity == 
    \A i \in indexes: i.id \in indexIds /\ i.tableId \in tableIds /\ \A fieldId \in i.fieldIds: fieldId \in fieldIds

(* Constraint integrity *)
ConstraintIntegrity == 
    \A c \in constraints: c.id \in constraintIds /\ c.tableId \in tableIds /\ \A fieldId \in c.fieldIds: fieldId \in fieldIds

(* Relationship integrity *)
RelationshipIntegrity == 
    \A r \in relationships: r.id \in relationshipIds /\ r.sourceTableId \in tableIds /\ r.targetTableId \in tableIds /\ 
    \A fieldId \in r.sourceFieldIds: fieldId \in fieldIds /\ \A fieldId \in r.targetFieldIds: fieldId \in fieldIds

(* Field table association *)
FieldTableAssociation == 
    \A f \in fields: \E t \in tables: f.tableId = t.id

(* Index table association *)
IndexTableAssociation == 
    \A i \in indexes: \E t \in tables: i.tableId = t.id

(* Constraint table association *)
ConstraintTableAssociation == 
    \A c \in constraints: \E t \in tables: c.tableId = t.id

(* Primary key constraint *)
PrimaryKeyConstraint == 
    \A t \in tables: \E f \in fields: f.tableId = t.id /\ f.isPrimaryKey = TRUE

(* Unique constraint *)
UniqueConstraint == 
    \A f \in fields: f.isUnique = TRUE => \A f2 \in fields: (f2.id /= f.id /\ f2.tableId = f.tableId /\ f2.name = f.name) => f2.isUnique = FALSE

(* Data type validity *)
DataTypeValidity == 
    \A f \in fields: f.dataType \in DataType

(* Relationship consistency *)
RelationshipConsistency == 
    \A r \in relationships: r.sourceTableId /= r.targetTableId

(* All invariants *)
Invariant == 
    TableUniqueness /\ FieldUniqueness /\ IndexUniqueness /\ ConstraintUniqueness /\ RelationshipUniqueness /\
    TableIntegrity /\ FieldIntegrity /\ IndexIntegrity /\ ConstraintIntegrity /\ RelationshipIntegrity /\
    FieldTableAssociation /\ IndexTableAssociation /\ ConstraintTableAssociation /\
    PrimaryKeyConstraint /\ UniqueConstraint /\ DataTypeValidity /\ RelationshipConsistency

(* Main specification *)
Spec == Init /\ [][Next]_<<tables, fields, indexes, constraints, relationships, tableIds, fieldIds, indexIds, constraintIds, relationshipIds>>

(* Theorem to prove *)
THEOREM Spec => []Invariant
