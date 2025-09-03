#!/usr/bin/env bash
set -euo pipefail

BASE_URL=${BASE_URL:-http://demo-api.default.svc.cluster.local/health}
SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)

k6 run "$SCRIPT_DIR/http_load_test.js" --env BASE_URL="$BASE_URL"
