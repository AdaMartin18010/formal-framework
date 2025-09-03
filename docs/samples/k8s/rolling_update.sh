#!/usr/bin/env bash
set -euo pipefail

kubectl -n default set image deploy/demo-api api=demo/api:${1:-vNEXT}
kubectl -n default rollout status deploy/demo-api --timeout=120s
