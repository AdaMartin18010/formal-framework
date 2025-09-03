#!/usr/bin/env bash
set -euo pipefail

kubectl -n default port-forward svc/demo-nginx 8080:80
