# 智能家居 隐私与安全 DSL 草案

## 1. 概述

该DSL用于统一配置智能家居的访问控制、数据保护、合规模块与网络安全策略，可与顶层智能家居DSL及设备互联模块共同工作。

## 2. 核心语法定义

### 2.1 访问控制（RBAC/ABAC）

```yaml
access_control:
  roles:
    - name: "owner"; permissions: ["all"]
    - name: "adult"; permissions: ["scene_run", "device_control", "camera_view"]
    - name: "child"; permissions: ["scene_run_limited"]
    - name: "guest"; permissions: ["guest_mode"]
  attributes:
    - name: "time_range"; values: ["day", "night"]
    - name: "location"; values: ["home", "guest_wifi"]
  policies:
    - resource: "lock.*"; effect: "allow"; roles: ["owner", "adult"]
    - resource: "camera.*"; effect: "allow"; roles: ["owner"]
    - resource: "thermostat.*"; effect: "allow"; roles: ["owner", "adult"]
    - resource: "scene.good_night"; effect: "allow"; roles: ["owner", "adult", "child"]
    - resource: "camera.*"; effect: "deny"; roles: ["guest"]
```

### 2.2 数据保护（留存/加密/脱敏）

```yaml
data_protection:
  retention:
    camera_recordings: "7d"
    access_logs: "180d"
    sensor_history: "90d"
  encryption:
    at_rest: "aes-256"
    in_transit: "tls-1.3"
    key_mgmt: "hsm | kms"
  pii_masking:
    rules:
      - field: "user.phone"; method: "mask_tail"; keep: 4
      - field: "user.email"; method: "mask_local"
```

### 2.3 合规与审计

```yaml
compliance_audit:
  frameworks: ["GDPR", "CCPA", "PIPL"]
  consent:
    policies: ["explicit_opt_in", "purpose_limitation"]
    records: {retention: "5y"}
  audit_logging:
    enabled: true
    fields: ["actor", "action", "resource", "result", "timestamp", "ip"]
    export: [{target: "siem"}]
```

### 2.4 网络安全（分段/防火墙/零信任）

```yaml
network_security:
  segmentation: ["iot_vlan", "guest_wifi", "home_lan"]
  firewall:
    rules:
      - name: "deny_iot_to_lan"; action: "deny"; from: "iot_vlan"; to: "home_lan"
      - name: "allow_controller_to_iot"; action: "allow"; from: "home_lan"; to: "iot_vlan"; ports: ["5683/udp", "1883/tcp"]
  zero_trust:
    mfa_for_admin: true
    device_attestation: "matter_pase" 
```

## 3. 自动化与验证

```python
class PrivacySecurityValidator:
  def validate_acl(self, policies):
    assert any(p["effect"] == "deny" for p in policies), "missing deny rules"
```
