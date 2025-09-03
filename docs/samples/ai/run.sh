#!/usr/bin/env bash
set -euo pipefail

uvicorn fastapi_infer:app --host 0.0.0.0 --port 8000
