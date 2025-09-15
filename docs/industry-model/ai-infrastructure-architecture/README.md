# AI 基础设施行业模型 - 案例库（骨架占位）

## 案例一：模型服务与多版本灰度（TF Serving）

- 对齐：`L3_D04_运行时标准模型.md` 服务/部署 · `L4_D93_AI_行业索引与对标.md`
- 不变式：VersionCompatibility/CanarySafety
- 交叉链接：`docs/formal-model/runtime-model/theory.md`
- evidence:AI-SERVING-VERSIONS

## 案例二：特征库一致性与回放（Feast）

- 对齐：`L2_D02_数据元模型.md` 一致性 · `L4_D93_AI_行业索引与对标.md`
- 不变式：FeatureEntityConsistency
- 交叉链接：`docs/formal-model/data-model/theory.md`
- evidence:AI-FEAST-CONSISTENCY

## 案例三：训练流水线与编排（Kubeflow/Airflow）

- 对齐：`L3_D09_CICD标准模型.md` 流水线/Stage
- 不变式：GateBlocking/ReproducibleBuild
- 交叉链接：`docs/formal-model/cicd-model/theory.md`
- evidence:AI-PIPELINE-KF
