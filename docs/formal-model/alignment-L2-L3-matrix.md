---
id: ALIGN_L2_L3_V1.0
title: L2↔L3 映射总表
version: V1.0
status: stable
---

## 1. 目的

汇总 L2 元模型与 L3 标准模型的对象/属性/不变式对齐关系，便于横向审阅与后续维护。

## 2. 映射视图

### 2.1 交互（D01） {#21-交互d01}

- 对象映射
  - L2.Endpoint ↔ L3.APIEndpointStandard.REST/GraphQL/gRPC
  - L2.Message ↔ L3.MessageFormatStandard.JSON/Protobuf/Avro
  - L2.Protocol ↔ L3.ProtocolStandard.HTTP/WebSocket/MQTT
- 属性映射
  - security/authentication/authorization ↔ OAuth2/OIDC 配置
  - version/deprecation ↔ VersioningConfig 与兼容策略
- 不变式映射
  - ContractCompleteness ↔ C1
  - VersionCompatibility ↔ C2
  - AuthEnforcement ↔ C3
  - MessageTypeSafety ↔ C4
  - ProtocolStateConsistency ↔ C5

### 2.2 数据（D02） {#22-数据d02}

- 对象映射
  - L2.Entity/Field/Relation/Index ↔ L3.EntityDesign/FieldDefinition/RelationshipModeling
  - L2.Migration ↔ L3.DataMigration
- 属性映射
  - constraints/check/triggers/views ↔ L3 constraints/triggers/views
  - types/json/uuid/format/range ↔ L3 字段类型与约束
- 不变式映射
  - PrimaryKeyUniqueness ↔ D1
  - ForeignKeyIntegrity ↔ D2
  - MigrationReversibility ↔ D3

### 2.3 运行时（D04） {#23-运行时d04}

- 对象映射
  - L2.Workload/Service/Network/Storage ↔ L3.Orchestration/Service/Network/Storage
  - L2.Policy ↔ L3.NetworkPolicy/ServiceMesh.security_policies
- 属性映射
  - deployment_strategy/health_checks ↔ L3 Workload.deployment_strategy/health_checks
  - service_mesh.virtual_service/destination_rule/gateway/sidecar ↔ L3 ServiceMesh 对应对象
- 不变式映射
  - ReplicaBounds ↔ WS1–WS3
  - EndpointHealth ↔ SD3
  - NetworkPolicyCompleteness ↔ NS1–NS3
  - LBHealthy ↔ SS3
  - ResourceLimitsSLA ↔ QoS1

### 2.4 部署（D05） {#24-部署d05}

- 对象映射
  - L2.Environment/Configuration/DeploymentStrategy/VersionControl/Rollback ↔ L3 Release/DeploymentStrategy/Configuration/Infrastructure/Environment/Rollback
  - L2.DeploymentPipeline/Stage ↔ L3 Pipeline/Stage
- 属性映射
  - drift_policy/schema/value/dependency/security ↔ L3 Configuration.validation/drift_management
  - iac/provider/region ↔ L3 Infrastructure.infrastructure_as_code/cloud_providers
- 不变式映射
  - ImmutableArtifact ↔ DEP1/CI3
  - QualityGateEnforcement ↔ DEP2/CI1
  - RollbackSafety ↔ DEP3
  - EnvironmentReady ↔ DEP4

### 2.5 监控（D06） {#25-监控d06}

- 对象映射
  - L2.Metric/Alert/Trace/Dashboard ↔ L3 ObservabilityStandard
- 属性映射
  - metric.name/kind/labels/unit/retention ↔ L3 Metric 定义
  - alert.expr/severity/for/annotations/runbook ↔ L3 Alert 定义
- 不变式映射
  - SLOCoverage ↔ MON1
  - LabelCardinalityBound ↔ MON2
  - RunbookPresence ↔ MON3
  - MetricNaming ↔ MON4

### 2.6 控制调度（D07） {#26-控制调度d07}

- 对象映射
  - L2.Scheduler/Task/StateMachine/Transition/Queue ↔ L3 TaskScheduling/StateMachine
- 不变式映射
  - EDFSchedulability ↔ EDF1/EC 合集
  - RMBound ↔ RMS 利用率上界
  - MutualExclusion ↔ CS2
  - DeterministicStateMachine ↔ StateConsistency
  - EventLatencyBound ↔ 性能与实时约束

### 2.7 测试（D08） {#27-测试d08}

- 对象映射
  - L2.TestCase/TestSuite/Coverage/PerformanceProfile ↔ L3 TestingCore
  - L2.Defect/Environment/TestData ↔ L3 DefectWorkflow/Env/Data
- 不变式映射
  - Determinism ↔ T1
  - CoverageGate ↔ T2
  - FlakyBound ↔ T3
  - LatencySLA ↔ T4
  - RegressionSafety ↔ T5

### 2.8 CI/CD（D09） {#28-cicdd09}

- 对象映射
  - L2.DeploymentPipeline/Stage ↔ L3 Pipeline/Stage
  - L2.Artifact（在部署域） ↔ L3 Artifact（供应链）
- 不变式映射
  - GateBlocking ↔ CI1
  - ReproducibleBuild ↔ CI2
  - ArtifactTraceability ↔ CI3
  - SupplyChainIntegrity ↔ CI4

## 3. 维护建议

- 变更控制：L2/L3 任一侧更新需同步更新本映射表
- 质量门禁：PR 中新增/修改不变式需更新映射项
- 版本化：对齐表版本与 L2/L3 文档版本关联

## 4. 参见

- [项目总览 (docs/README)](../README.md#-快速导航) - 快速导航中含本映射表入口
- [快速导航系统 (QUICK_NAVIGATION)](../QUICK_NAVIGATION.md#l2l3-映射总表) - L2/L3 文档列表与映射总表
- 各 L2/L3 文档末尾均含「参见：L2↔L3 映射总表」链接，便于从单篇文档返回本表
