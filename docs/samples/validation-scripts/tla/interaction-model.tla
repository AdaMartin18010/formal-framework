---------------------------- MODULE InteractionModel ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

(* 交互模型的形式化规格定义 *)

(* 常量定义 *)
CONSTANTS 
    MaxEndpoints,    (* 最大端点数量 *)
    MaxResources,    (* 最大资源数量 *)
    MaxOperations,   (* 最大操作数量 *)
    MaxVersions,     (* 最大版本数量 *)
    MaxMethods       (* 最大HTTP方法数量 *)

(* 假设条件 *)
ASSUME MaxEndpoints > 0 /\ MaxResources > 0 /\ MaxOperations > 0 /\ MaxVersions > 0 /\ MaxMethods > 0

(* 类型定义 *)
EndpointId == 1..MaxEndpoints
ResourceId == 1..MaxResources
OperationId == 1..MaxOperations
VersionId == 1..MaxVersions
MethodId == 1..MaxMethods

(* 状态变量 *)
VARIABLES
    endpoints,      (* 端点集合 *)
    resources,      (* 资源集合 *)
    operations,     (* 操作集合 *)
    endpointPaths,  (* 端点路径映射 *)
    endpointMethods, (* 端点方法映射 *)
    resourceOperations, (* 资源操作映射 *)
    operationResources,  (* 操作资源映射 *)
    versions,       (* 版本集合 *)
    authRequired,   (* 认证要求映射 *)
    rateLimits,     (* 限流配置映射 *)
    timeouts,       (* 超时配置映射 *)

(* 初始状态 *)
Init ==
    /\ endpoints = {}
    /\ resources = {}
    /\ operations = {}
    /\ endpointPaths = [e \in EndpointId |-> ""]
    /\ endpointMethods = [e \in EndpointId |-> {}]
    /\ resourceOperations = [r \in ResourceId |-> {}]
    /\ operationResources = [o \in OperationId |-> {}]
    /\ versions = {}
    /\ authRequired = [e \in EndpointId |-> FALSE]
    /\ rateLimits = [e \in EndpointId |-> 0]
    /\ timeouts = [e \in EndpointId |-> 0]

(* 动作定义 *)

(* 添加端点 *)
AddEndpoint(endpoint, path, method) ==
    /\ endpoint \notin endpoints
    /\ path \in STRING
    /\ method \in MethodId
    /\ endpointPaths' = [endpointPaths EXCEPT ![endpoint] = path]
    /\ endpointMethods' = [endpointMethods EXCEPT ![endpoint] = endpointMethods[endpoint] \cup {method}]
    /\ endpoints' = endpoints \cup {endpoint}
    /\ UNCHANGED <<resources, operations, resourceOperations, operationResources, versions, authRequired, rateLimits, timeouts>>

(* 添加资源 *)
AddResource(resource) ==
    /\ resource \notin resources
    /\ resources' = resources \cup {resource}
    /\ UNCHANGED <<endpoints, operations, endpointPaths, endpointMethods, resourceOperations, operationResources, versions, authRequired, rateLimits, timeouts>>

(* 添加操作 *)
AddOperation(operation, resource) ==
    /\ operation \notin operations
    /\ resource \in resources
    /\ operations' = operations \cup {operation}
    /\ resourceOperations' = [resourceOperations EXCEPT ![resource] = resourceOperations[resource] \cup {operation}]
    /\ operationResources' = [operationResources EXCEPT ![operation] = resource]
    /\ UNCHANGED <<endpoints, endpointPaths, endpointMethods, versions, authRequired, rateLimits, timeouts>>

(* 设置认证要求 *)
SetAuthRequired(endpoint, required) ==
    /\ endpoint \in endpoints
    /\ authRequired' = [authRequired EXCEPT ![endpoint] = required]
    /\ UNCHANGED <<resources, operations, endpointPaths, endpointMethods, resourceOperations, operationResources, versions, rateLimits, timeouts>>

(* 设置限流配置 *)
SetRateLimit(endpoint, limit) ==
    /\ endpoint \in endpoints
    /\ limit >= 0
    /\ rateLimits' = [rateLimits EXCEPT ![endpoint] = limit]
    /\ UNCHANGED <<resources, operations, endpointPaths, endpointMethods, resourceOperations, operationResources, versions, authRequired, timeouts>>

(* 设置超时配置 *)
SetTimeout(endpoint, timeout) ==
    /\ endpoint \in endpoints
    /\ timeout >= 0
    /\ timeouts' = [timeouts EXCEPT ![endpoint] = timeout]
    /\ UNCHANGED <<resources, operations, endpointPaths, endpointMethods, resourceOperations, operationResources, versions, authRequired, rateLimits>>

(* 下一个状态关系 *)
Next ==
    \/ \E endpoint \in EndpointId, path \in STRING, method \in MethodId : AddEndpoint(endpoint, path, method)
    \/ \E resource \in ResourceId : AddResource(resource)
    \/ \E operation \in OperationId, resource \in ResourceId : AddOperation(operation, resource)
    \/ \E endpoint \in EndpointId, required \in BOOLEAN : SetAuthRequired(endpoint, required)
    \/ \E endpoint \in EndpointId, limit \in Nat : SetRateLimit(endpoint, limit)
    \/ \E endpoint \in EndpointId, timeout \in Nat : SetTimeout(endpoint, timeout)

(* 不变式定义 *)

(* 1. 端点唯一性约束 *)
EndpointUniqueness ==
    \A e1, e2 \in endpoints :
        e1 # e2 => 
            endpointPaths[e1] # endpointPaths[e2] \/
            endpointMethods[e1] \cap endpointMethods[e2] = {}

(* 2. 资源完整性约束 *)
ResourceIntegrity ==
    \A r \in resources :
        \E o \in operations : o \in resourceOperations[r]

(* 3. 操作完整性约束 *)
OperationIntegrity ==
    \A o \in operations :
        \E r \in resources : operationResources[o] = r

(* 4. 端点资源关联约束 *)
EndpointResourceAssociation ==
    \A e \in endpoints :
        \E r \in resources :
            \E o \in operations :
                o \in resourceOperations[r] /\ e \in endpoints

(* 5. 认证配置约束 *)
AuthConfigurationConstraint ==
    \A e \in endpoints :
        authRequired[e] => 
            rateLimits[e] > 0 /\ timeouts[e] > 0

(* 6. 限流配置约束 *)
RateLimitConstraint ==
    \A e \in endpoints :
        rateLimits[e] > 0 => timeouts[e] > 0

(* 7. 超时配置约束 *)
TimeoutConstraint ==
    \A e \in endpoints :
        timeouts[e] > 0 => timeouts[e] <= 30000  (* 最大30秒 *)

(* 8. 版本一致性约束 *)
VersionConsistency ==
    \A e \in endpoints :
        \A v \in versions :
            endpointPaths[e] # "" => 
                \E r \in resources :
                    \E o \in operations :
                        o \in resourceOperations[r]

(* 9. 方法有效性约束 *)
MethodValidity ==
    \A e \in endpoints :
        \A m \in endpointMethods[e] :
            m \in MethodId

(* 10. 路径有效性约束 *)
PathValidity ==
    \A e \in endpoints :
        endpointPaths[e] # "" => 
            endpointPaths[e][1] = "/"

(* 主要不变式 *)
Invariant ==
    /\ EndpointUniqueness
    /\ ResourceIntegrity
    /\ OperationIntegrity
    /\ EndpointResourceAssociation
    /\ AuthConfigurationConstraint
    /\ RateLimitConstraint
    /\ TimeoutConstraint
    /\ VersionConsistency
    /\ MethodValidity
    /\ PathValidity

(* 规格定义 *)
Spec == Init /\ [][Next]_<<endpoints, resources, operations, endpointPaths, endpointMethods, resourceOperations, operationResources, versions, authRequired, rateLimits, timeouts>>

(* 定理：规格满足不变式 *)
THEOREM Spec => []Invariant

(* 辅助不变式 *)

(* 状态机属性 *)
StateMachineProperty ==
    \A e \in endpoints :
        \A m \in endpointMethods[e] :
            \E r \in resources :
                \E o \in operations :
                    o \in resourceOperations[r]

(* 资源管理属性 *)
ResourceManagementProperty ==
    \A r \in resources :
        Cardinality(resourceOperations[r]) <= MaxOperations

(* 操作管理属性 *)
OperationManagementProperty ==
    \A o \in operations :
        \E r \in resources :
            operationResources[o] = r

(* 完整规格 *)
CompleteSpec ==
    Spec /\ []StateMachineProperty /\ []ResourceManagementProperty /\ []OperationManagementProperty

(* 验证配置 *)
CONSTANT
    MaxEndpoints = 10,
    MaxResources = 5,
    MaxOperations = 20,
    MaxVersions = 3,
    MaxMethods = 8

=============================================================================
