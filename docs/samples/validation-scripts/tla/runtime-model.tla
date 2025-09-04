---------------------------- MODULE RuntimeModel ----------------------------
(*
  Runtime Model TLA+ Specification
  Defines formal specification for the Runtime Meta-model including:
  - Runtime entities (Container, Pod, Node, Namespace, etc.)
  - Resource management and scheduling
  - Runtime constraints and invariants
  - Container lifecycle operations
*)

EXTENDS Naturals, Sequences, FiniteSets

(* Constants *)
CONSTANTS MaxContainers, MaxPods, MaxNodes, MaxNamespaces, MaxServices, MaxVolumes

(* Types *)
VARIABLES containers, pods, nodes, namespaces, services, volumes, configMaps, secrets

(* State variables *)
VARIABLES containerIds, podIds, nodeIds, namespaceIds, serviceIds, volumeIds, configMapIds, secretIds

(* Type definitions *)
ContainerId == 1..MaxContainers
PodId == 1..MaxPods
NodeId == 1..MaxNodes
NamespaceId == 1..MaxNamespaces
ServiceId == 1..MaxServices
VolumeId == 1..MaxVolumes
ConfigMapId == 1..MaxContainers
SecretId == 1..MaxContainers

(* Resource definitions *)
Resource == [cpu: Nat, memory: Nat, storage: Nat, network: Nat]
ResourceLimit == [cpu: Nat, memory: Nat, storage: Nat, network: Nat]
ResourceRequest == [cpu: Nat, memory: Nat, storage: Nat, network: Nat]

(* Status definitions *)
ContainerStatus == {"RUNNING", "STOPPED", "ERROR", "CREATING", "TERMINATING"}
PodStatus == {"RUNNING", "PENDING", "SUCCEEDED", "FAILED", "UNKNOWN"}
NodeStatus == {"READY", "NOT_READY", "UNKNOWN"}
ServiceStatus == {"ACTIVE", "INACTIVE", "ERROR"}

(* Structure definitions *)
Container == [id: ContainerId, podId: PodId, name: STRING, image: STRING, 
              resources: Resource, limits: ResourceLimit, requests: ResourceRequest,
              status: ContainerStatus, ports: SUBSET Nat, envVars: SUBSET STRING,
              volumeMounts: SUBSET VolumeId, createdAt: STRING, updatedAt: STRING]

Pod == [id: PodId, namespaceId: NamespaceId, nodeId: NodeId, name: STRING,
        labels: SUBSET STRING, annotations: SUBSET STRING, status: PodStatus,
        containerIds: SUBSET ContainerId, volumes: SUBSET VolumeId,
        restartPolicy: STRING, createdAt: STRING, updatedAt: STRING]

Node == [id: NodeId, name: STRING, status: NodeStatus, capacity: Resource,
         allocatable: Resource, labels: SUBSET STRING, taints: SUBSET STRING,
         podIds: SUBSET PodId, createdAt: STRING, updatedAt: STRING]

Namespace == [id: NamespaceId, name: STRING, status: STRING, labels: SUBSET STRING,
              annotations: SUBSET STRING, resourceQuotas: SUBSET STRING,
              podIds: SUBSET PodId, serviceIds: SUBSET ServiceId, createdAt: STRING]

Service == [id: ServiceId, namespaceId: NamespaceId, name: STRING, type: STRING,
            selector: SUBSET STRING, ports: SUBSET Nat, targetPodIds: SUBSET PodId,
            status: ServiceStatus, createdAt: STRING, updatedAt: STRING]

Volume == [id: VolumeId, name: STRING, type: STRING, size: Nat, mountPath: STRING,
           accessMode: STRING, persistent: BOOLEAN, storageClass: STRING,
           podIds: SUBSET PodId, createdAt: STRING]

ConfigMap == [id: ConfigMapId, namespaceId: NamespaceId, name: STRING,
              data: SUBSET STRING, podIds: SUBSET PodId, createdAt: STRING]

Secret == [id: SecretId, namespaceId: NamespaceId, name: STRING,
           data: SUBSET STRING, type: STRING, podIds: SUBSET PodId, createdAt: STRING]

(* Initial state *)
Init == 
    /\ containers = {}
    /\ pods = {}
    /\ nodes = {}
    /\ namespaces = {}
    /\ services = {}
    /\ volumes = {}
    /\ configMaps = {}
    /\ secrets = {}
    /\ containerIds = {}
    /\ podIds = {}
    /\ nodeIds = {}
    /\ namespaceIds = {}
    /\ serviceIds = {}
    /\ volumeIds = {}
    /\ configMapIds = {}
    /\ secretIds = {}

(* Actions *)

(* Create a new namespace *)
CreateNamespace(namespace) ==
    /\ namespace.id \notin namespaceIds
    /\ namespaceIds' = namespaceIds \union {namespace.id}
    /\ namespaces' = namespaces \union {namespace}
    /\ UNCHANGED <<containers, pods, nodes, services, volumes, configMaps, secrets, containerIds, podIds, nodeIds, serviceIds, volumeIds, configMapIds, secretIds>>

(* Create a new node *)
CreateNode(node) ==
    /\ node.id \notin nodeIds
    /\ nodeIds' = nodeIds \union {node.id}
    /\ nodes' = nodes \union {node}
    /\ UNCHANGED <<containers, pods, namespaces, services, volumes, configMaps, secrets, containerIds, podIds, namespaceIds, serviceIds, volumeIds, configMapIds, secretIds>>

(* Create a new pod *)
CreatePod(pod) ==
    /\ pod.id \notin podIds
    /\ pod.namespaceId \in namespaceIds
    /\ pod.nodeId \in nodeIds
    /\ podIds' = podIds \union {pod.id}
    /\ pods' = pods \union {pod}
    /\ namespaces' = {n \in namespaces: IF n.id = pod.namespaceId THEN [n EXCEPT !.podIds = n.podIds \union {pod.id}] ELSE n}
    /\ nodes' = {n \in nodes: IF n.id = pod.nodeId THEN [n EXCEPT !.podIds = n.podIds \union {pod.id}] ELSE n}
    /\ UNCHANGED <<containers, services, volumes, configMaps, secrets, containerIds, serviceIds, volumeIds, configMapIds, secretIds>>

(* Create a new container *)
CreateContainer(container) ==
    /\ container.id \notin containerIds
    /\ container.podId \in podIds
    /\ containerIds' = containerIds \union {container.id}
    /\ containers' = containers \union {container}
    /\ pods' = {p \in pods: IF p.id = container.podId THEN [p EXCEPT !.containerIds = p.containerIds \union {container.id}] ELSE p}
    /\ UNCHANGED <<nodes, namespaces, services, volumes, configMaps, secrets, nodeIds, namespaceIds, serviceIds, volumeIds, configMapIds, secretIds>>

(* Create a new service *)
CreateService(service) ==
    /\ service.id \notin serviceIds
    /\ service.namespaceId \in namespaceIds
    /\ \A podId \in service.targetPodIds: podId \in podIds
    /\ serviceIds' = serviceIds \union {service.id}
    /\ services' = services \union {service}
    /\ namespaces' = {n \in namespaces: IF n.id = service.namespaceId THEN [n EXCEPT !.serviceIds = n.serviceIds \union {service.id}] ELSE n}
    /\ UNCHANGED <<containers, pods, nodes, volumes, configMaps, secrets, containerIds, podIds, nodeIds, volumeIds, configMapIds, secretIds>>

(* Create a new volume *)
CreateVolume(volume) ==
    /\ volume.id \notin volumeIds
    /\ \A podId \in volume.podIds: podId \in podIds
    /\ volumeIds' = volumeIds \union {volume.id}
    /\ volumes' = volumes \union {volume}
    /\ UNCHANGED <<containers, pods, nodes, namespaces, services, configMaps, secrets, containerIds, podIds, nodeIds, namespaceIds, serviceIds, configMapIds, secretIds>>

(* Schedule pod to node *)
SchedulePod(podId, nodeId) ==
    /\ podId \in podIds
    /\ nodeId \in nodeIds
    /\ pods' = {p \in pods: IF p.id = podId THEN [p EXCEPT !.nodeId = nodeId] ELSE p}
    /\ nodes' = {n \in nodes: IF n.id = nodeId THEN [n EXCEPT !.podIds = n.podIds \union {podId}] ELSE n}
    /\ UNCHANGED <<containers, namespaces, services, volumes, configMaps, secrets, containerIds, namespaceIds, serviceIds, volumeIds, configMapIds, secretIds>>

(* Update pod status *)
UpdatePodStatus(podId, status) ==
    /\ podId \in podIds
    /\ pods' = {p \in pods: IF p.id = podId THEN [p EXCEPT !.status = status, !.updatedAt = "now"] ELSE p}
    /\ UNCHANGED <<containers, nodes, namespaces, services, volumes, configMaps, secrets, containerIds, nodeIds, namespaceIds, serviceIds, volumeIds, configMapIds, secretIds>>

(* Update container status *)
UpdateContainerStatus(containerId, status) ==
    /\ containerId \in containerIds
    /\ containers' = {c \in containers: IF c.id = containerId THEN [c EXCEPT !.status = status, !.updatedAt = "now"] ELSE c}
    /\ UNCHANGED <<pods, nodes, namespaces, services, volumes, configMaps, secrets, podIds, nodeIds, namespaceIds, serviceIds, volumeIds, configMapIds, secretIds>>

(* Next state relation *)
Next == 
    \/ \E namespace \in Namespace: CreateNamespace(namespace)
    \/ \E node \in Node: CreateNode(node)
    \/ \E pod \in Pod: CreatePod(pod)
    \/ \E container \in Container: CreateContainer(container)
    \/ \E service \in Service: CreateService(service)
    \/ \E volume \in Volume: CreateVolume(volume)
    \/ \E podId \in podIds, nodeId \in nodeIds: SchedulePod(podId, nodeId)
    \/ \E podId \in podIds, status \in PodStatus: UpdatePodStatus(podId, status)
    \/ \E containerId \in containerIds, status \in ContainerStatus: UpdateContainerStatus(containerId, status)

(* Invariants *)

(* Container uniqueness *)
ContainerUniqueness == 
    \A c1, c2 \in containers: c1.id = c2.id => c1 = c2

(* Pod uniqueness *)
PodUniqueness == 
    \A p1, p2 \in pods: p1.id = p2.id => p1 = p2

(* Node uniqueness *)
NodeUniqueness == 
    \A n1, n2 \in nodes: n1.id = n2.id => n1 = n2

(* Namespace uniqueness *)
NamespaceUniqueness == 
    \A ns1, ns2 \in namespaces: ns1.id = ns2.id => ns1 = ns2

(* Service uniqueness *)
ServiceUniqueness == 
    \A s1, s2 \in services: s1.id = s2.id => s1 = s2

(* Volume uniqueness *)
VolumeUniqueness == 
    \A v1, v2 \in volumes: v1.id = v2.id => v1 = v2

(* Container integrity *)
ContainerIntegrity == 
    \A c \in containers: c.id \in containerIds /\ c.podId \in podIds

(* Pod integrity *)
PodIntegrity == 
    \A p \in pods: p.id \in podIds /\ p.namespaceId \in namespaceIds /\ p.nodeId \in nodeIds

(* Node integrity *)
NodeIntegrity == 
    \A n \in nodes: n.id \in nodeIds

(* Namespace integrity *)
NamespaceIntegrity == 
    \A ns \in namespaces: ns.id \in namespaceIds

(* Service integrity *)
ServiceIntegrity == 
    \A s \in services: s.id \in serviceIds /\ s.namespaceId \in namespaceIds /\ \A podId \in s.targetPodIds: podId \in podIds

(* Volume integrity *)
VolumeIntegrity == 
    \A v \in volumes: v.id \in volumeIds /\ \A podId \in v.podIds: podId \in podIds

(* Container pod association *)
ContainerPodAssociation == 
    \A c \in containers: \E p \in pods: c.podId = p.id

(* Pod namespace association *)
PodNamespaceAssociation == 
    \A p \in pods: \E ns \in namespaces: p.namespaceId = ns.id

(* Pod node association *)
PodNodeAssociation == 
    \A p \in pods: \E n \in nodes: p.nodeId = n.id

(* Service namespace association *)
ServiceNamespaceAssociation == 
    \A s \in services: \E ns \in namespaces: s.namespaceId = ns.id

(* Resource constraint *)
ResourceConstraint == 
    \A c \in containers: c.requests.cpu <= c.limits.cpu /\ c.requests.memory <= c.limits.memory

(* Node capacity constraint *)
NodeCapacityConstraint == 
    \A n \in nodes: \A resource \in {"cpu", "memory", "storage", "network"}: 
        \A p \in pods: p.nodeId = n.id => 
            \A c \in containers: c.podId = p.id => 
                c.requests[resource] <= n.allocatable[resource]

(* Pod container constraint *)
PodContainerConstraint == 
    \A p \in pods: \A containerId \in p.containerIds: \E c \in containers: c.id = containerId /\ c.podId = p.id

(* Service pod constraint *)
ServicePodConstraint == 
    \A s \in services: \A podId \in s.targetPodIds: \E p \in pods: p.id = podId

(* Volume pod constraint *)
VolumePodConstraint == 
    \A v \in volumes: \A podId \in v.podIds: \E p \in pods: p.id = podId

(* All invariants *)
Invariant == 
    ContainerUniqueness /\ PodUniqueness /\ NodeUniqueness /\ NamespaceUniqueness /\ ServiceUniqueness /\ VolumeUniqueness /\
    ContainerIntegrity /\ PodIntegrity /\ NodeIntegrity /\ NamespaceIntegrity /\ ServiceIntegrity /\ VolumeIntegrity /\
    ContainerPodAssociation /\ PodNamespaceAssociation /\ PodNodeAssociation /\ ServiceNamespaceAssociation /\
    ResourceConstraint /\ NodeCapacityConstraint /\ PodContainerConstraint /\ ServicePodConstraint /\ VolumePodConstraint

(* Main specification *)
Spec == Init /\ [][Next]_<<containers, pods, nodes, namespaces, services, volumes, configMaps, secrets, containerIds, podIds, nodeIds, namespaceIds, serviceIds, volumeIds, configMapIds, secretIds>>

(* Theorem to prove *)
THEOREM Spec => []Invariant
