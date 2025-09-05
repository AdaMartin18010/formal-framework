#!/bin/bash

# 正式验证框架部署脚本
# 支持多种部署环境：开发、测试、生产

set -e  # 遇到错误立即退出

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 配置变量
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
ENVIRONMENT="${ENVIRONMENT:-development}"
NAMESPACE="${NAMESPACE:-formal-framework}"
IMAGE_TAG="${IMAGE_TAG:-latest}"
REGISTRY="${REGISTRY:-ghcr.io/formal-framework}"

# 显示帮助信息
show_help() {
    cat << EOF
正式验证框架部署脚本

用法: $0 [选项] [命令]

选项:
    -e, --environment ENV    部署环境 (development|staging|production)
    -n, --namespace NS       命名空间 (默认: formal-framework)
    -t, --tag TAG           镜像标签 (默认: latest)
    -r, --registry REG      镜像仓库 (默认: ghcr.io/formal-framework)
    -h, --help              显示此帮助信息

命令:
    build                   构建镜像
    push                    推送镜像
    deploy                  部署应用
    upgrade                 升级应用
    rollback                回滚应用
    status                  查看状态
    logs                    查看日志
    clean                   清理资源
    full                    完整部署流程

示例:
    $0 -e production deploy
    $0 -e staging full
    $0 -t v1.2.3 build push deploy
EOF
}

# 检查依赖
check_dependencies() {
    log_info "检查部署依赖..."
    
    local missing_deps=()
    
    # 检查Docker
    if ! command -v docker &> /dev/null; then
        missing_deps+=("docker")
    fi
    
    # 检查kubectl
    if ! command -v kubectl &> /dev/null; then
        missing_deps+=("kubectl")
    fi
    
    # 检查helm
    if ! command -v helm &> /dev/null; then
        missing_deps+=("helm")
    fi
    
    if [ ${#missing_deps[@]} -ne 0 ]; then
        log_error "缺少以下依赖: ${missing_deps[*]}"
        log_info "请安装缺少的依赖后重试"
        exit 1
    fi
    
    log_success "所有依赖检查通过"
}

# 验证环境配置
validate_environment() {
    log_info "验证环境配置..."
    
    case $ENVIRONMENT in
        development|staging|production)
            log_success "环境配置有效: $ENVIRONMENT"
            ;;
        *)
            log_error "无效的环境配置: $ENVIRONMENT"
            log_info "支持的环境: development, staging, production"
            exit 1
            ;;
    esac
    
    # 检查Kubernetes连接
    if ! kubectl cluster-info &> /dev/null; then
        log_error "无法连接到Kubernetes集群"
        exit 1
    fi
    
    log_success "Kubernetes集群连接正常"
}

# 构建镜像
build_images() {
    log_info "构建Docker镜像..."
    
    local services=("app" "verification" "monitoring")
    
    for service in "${services[@]}"; do
        log_info "构建 $service 服务镜像..."
        
        local dockerfile="Dockerfile"
        if [ "$service" != "app" ]; then
            dockerfile="Dockerfile.$service"
        fi
        
        if [ ! -f "$PROJECT_ROOT/$dockerfile" ]; then
            log_warning "Dockerfile不存在: $dockerfile，跳过构建"
            continue
        fi
        
        docker build \
            -f "$PROJECT_ROOT/$dockerfile" \
            -t "$REGISTRY/$service:$IMAGE_TAG" \
            -t "$REGISTRY/$service:latest" \
            "$PROJECT_ROOT"
        
        log_success "$service 镜像构建完成"
    done
}

# 推送镜像
push_images() {
    log_info "推送Docker镜像到仓库..."
    
    local services=("app" "verification" "monitoring")
    
    for service in "${services[@]}"; do
        log_info "推送 $service 服务镜像..."
        
        docker push "$REGISTRY/$service:$IMAGE_TAG"
        docker push "$REGISTRY/$service:latest"
        
        log_success "$service 镜像推送完成"
    done
}

# 创建命名空间
create_namespace() {
    log_info "创建Kubernetes命名空间: $NAMESPACE"
    
    if kubectl get namespace "$NAMESPACE" &> /dev/null; then
        log_info "命名空间 $NAMESPACE 已存在"
    else
        kubectl create namespace "$NAMESPACE"
        log_success "命名空间 $NAMESPACE 创建成功"
    fi
}

# 部署配置
deploy_config() {
    log_info "部署配置和密钥..."
    
    # 创建配置映射
    kubectl apply -f - <<EOF
apiVersion: v1
kind: ConfigMap
metadata:
  name: app-config
  namespace: $NAMESPACE
data:
  NODE_ENV: $ENVIRONMENT
  LOG_LEVEL: info
  API_BASE_URL: https://api.formal-framework.com
EOF
    
    # 创建密钥
    kubectl create secret generic app-secrets \
        --namespace="$NAMESPACE" \
        --from-literal=database-url="postgresql://postgres:password@postgres:5432/formal_framework" \
        --from-literal=redis-url="redis://redis:6379" \
        --from-literal=jwt-secret="your-super-secret-key" \
        --dry-run=client -o yaml | kubectl apply -f -
    
    log_success "配置和密钥部署完成"
}

# 部署数据库
deploy_database() {
    log_info "部署数据库服务..."
    
    kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: postgres
  namespace: $NAMESPACE
spec:
  replicas: 1
  selector:
    matchLabels:
      app: postgres
  template:
    metadata:
      labels:
        app: postgres
    spec:
      containers:
      - name: postgres
        image: postgres:15-alpine
        env:
        - name: POSTGRES_DB
          value: formal_framework
        - name: POSTGRES_USER
          value: postgres
        - name: POSTGRES_PASSWORD
          value: password
        ports:
        - containerPort: 5432
        volumeMounts:
        - name: postgres-storage
          mountPath: /var/lib/postgresql/data
      volumes:
      - name: postgres-storage
        emptyDir: {}
---
apiVersion: v1
kind: Service
metadata:
  name: postgres
  namespace: $NAMESPACE
spec:
  selector:
    app: postgres
  ports:
  - port: 5432
    targetPort: 5432
EOF
    
    log_success "数据库服务部署完成"
}

# 部署Redis
deploy_redis() {
    log_info "部署Redis服务..."
    
    kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: redis
  namespace: $NAMESPACE
spec:
  replicas: 1
  selector:
    matchLabels:
      app: redis
  template:
    metadata:
      labels:
        app: redis
    spec:
      containers:
      - name: redis
        image: redis:7-alpine
        ports:
        - containerPort: 6379
        volumeMounts:
        - name: redis-storage
          mountPath: /data
      volumes:
      - name: redis-storage
        emptyDir: {}
---
apiVersion: v1
kind: Service
metadata:
  name: redis
  namespace: $NAMESPACE
spec:
  selector:
    app: redis
  ports:
  - port: 6379
    targetPort: 6379
EOF
    
    log_success "Redis服务部署完成"
}

# 部署应用
deploy_app() {
    log_info "部署应用服务..."
    
    kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: formal-framework-app
  namespace: $NAMESPACE
spec:
  replicas: 3
  selector:
    matchLabels:
      app: formal-framework-app
  template:
    metadata:
      labels:
        app: formal-framework-app
    spec:
      containers:
      - name: app
        image: $REGISTRY/app:$IMAGE_TAG
        ports:
        - containerPort: 8080
        env:
        - name: NODE_ENV
          valueFrom:
            configMapKeyRef:
              name: app-config
              key: NODE_ENV
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: app-secrets
              key: database-url
        - name: REDIS_URL
          valueFrom:
            secretKeyRef:
              name: app-secrets
              key: redis-url
        - name: JWT_SECRET
          valueFrom:
            secretKeyRef:
              name: app-secrets
              key: jwt-secret
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: formal-framework-app-service
  namespace: $NAMESPACE
spec:
  selector:
    app: formal-framework-app
  ports:
  - port: 80
    targetPort: 8080
  type: ClusterIP
---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: formal-framework-app-hpa
  namespace: $NAMESPACE
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: formal-framework-app
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
EOF
    
    log_success "应用服务部署完成"
}

# 部署监控
deploy_monitoring() {
    log_info "部署监控服务..."
    
    # 部署Prometheus
    kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: prometheus
  namespace: $NAMESPACE
spec:
  replicas: 1
  selector:
    matchLabels:
      app: prometheus
  template:
    metadata:
      labels:
        app: prometheus
    spec:
      containers:
      - name: prometheus
        image: prom/prometheus:latest
        ports:
        - containerPort: 9090
        volumeMounts:
        - name: prometheus-config
          mountPath: /etc/prometheus
        - name: prometheus-storage
          mountPath: /prometheus
        args:
          - '--config.file=/etc/prometheus/prometheus.yml'
          - '--storage.tsdb.path=/prometheus'
          - '--web.console.libraries=/etc/prometheus/console_libraries'
          - '--web.console.templates=/etc/prometheus/consoles'
          - '--storage.tsdb.retention.time=200h'
          - '--web.enable-lifecycle'
      volumes:
      - name: prometheus-config
        configMap:
          name: prometheus-config
      - name: prometheus-storage
        emptyDir: {}
---
apiVersion: v1
kind: Service
metadata:
  name: prometheus
  namespace: $NAMESPACE
spec:
  selector:
    app: prometheus
  ports:
  - port: 9090
    targetPort: 9090
  type: ClusterIP
EOF
    
    # 部署Grafana
    kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: grafana
  namespace: $NAMESPACE
spec:
  replicas: 1
  selector:
    matchLabels:
      app: grafana
  template:
    metadata:
      labels:
        app: grafana
    spec:
      containers:
      - name: grafana
        image: grafana/grafana:latest
        ports:
        - containerPort: 3000
        env:
        - name: GF_SECURITY_ADMIN_PASSWORD
          value: admin
        volumeMounts:
        - name: grafana-storage
          mountPath: /var/lib/grafana
      volumes:
      - name: grafana-storage
        emptyDir: {}
---
apiVersion: v1
kind: Service
metadata:
  name: grafana
  namespace: $NAMESPACE
spec:
  selector:
    app: grafana
  ports:
  - port: 3000
    targetPort: 3000
  type: ClusterIP
EOF
    
    log_success "监控服务部署完成"
}

# 等待部署完成
wait_for_deployment() {
    log_info "等待部署完成..."
    
    local deployments=("formal-framework-app" "postgres" "redis" "prometheus" "grafana")
    
    for deployment in "${deployments[@]}"; do
        log_info "等待 $deployment 部署完成..."
        kubectl wait --for=condition=available --timeout=300s deployment/"$deployment" -n "$NAMESPACE"
        log_success "$deployment 部署完成"
    done
}

# 检查部署状态
check_status() {
    log_info "检查部署状态..."
    
    echo "=== 命名空间状态 ==="
    kubectl get namespace "$NAMESPACE"
    
    echo "=== 部署状态 ==="
    kubectl get deployments -n "$NAMESPACE"
    
    echo "=== 服务状态 ==="
    kubectl get services -n "$NAMESPACE"
    
    echo "=== Pod状态 ==="
    kubectl get pods -n "$NAMESPACE"
    
    echo "=== 配置映射 ==="
    kubectl get configmaps -n "$NAMESPACE"
    
    echo "=== 密钥 ==="
    kubectl get secrets -n "$NAMESPACE"
}

# 查看日志
view_logs() {
    local service="${1:-formal-framework-app}"
    
    log_info "查看 $service 服务日志..."
    kubectl logs -f deployment/"$service" -n "$NAMESPACE"
}

# 升级应用
upgrade_app() {
    log_info "升级应用..."
    
    kubectl set image deployment/formal-framework-app \
        app="$REGISTRY/app:$IMAGE_TAG" \
        -n "$NAMESPACE"
    
    kubectl rollout status deployment/formal-framework-app -n "$NAMESPACE"
    
    log_success "应用升级完成"
}

# 回滚应用
rollback_app() {
    log_info "回滚应用..."
    
    kubectl rollout undo deployment/formal-framework-app -n "$NAMESPACE"
    kubectl rollout status deployment/formal-framework-app -n "$NAMESPACE"
    
    log_success "应用回滚完成"
}

# 清理资源
clean_resources() {
    log_warning "清理Kubernetes资源..."
    
    read -p "确定要删除命名空间 $NAMESPACE 中的所有资源吗? (y/N): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        kubectl delete namespace "$NAMESPACE"
        log_success "资源清理完成"
    else
        log_info "取消清理操作"
    fi
}

# 完整部署流程
full_deploy() {
    log_info "开始完整部署流程..."
    
    check_dependencies
    validate_environment
    build_images
    push_images
    create_namespace
    deploy_config
    deploy_database
    deploy_redis
    deploy_app
    deploy_monitoring
    wait_for_deployment
    check_status
    
    log_success "完整部署流程完成！"
}

# 主函数
main() {
    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -e|--environment)
                ENVIRONMENT="$2"
                shift 2
                ;;
            -n|--namespace)
                NAMESPACE="$2"
                shift 2
                ;;
            -t|--tag)
                IMAGE_TAG="$2"
                shift 2
                ;;
            -r|--registry)
                REGISTRY="$2"
                shift 2
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            build)
                check_dependencies
                build_images
                ;;
            push)
                check_dependencies
                push_images
                ;;
            deploy)
                check_dependencies
                validate_environment
                create_namespace
                deploy_config
                deploy_database
                deploy_redis
                deploy_app
                deploy_monitoring
                wait_for_deployment
                ;;
            upgrade)
                check_dependencies
                validate_environment
                upgrade_app
                ;;
            rollback)
                check_dependencies
                validate_environment
                rollback_app
                ;;
            status)
                check_dependencies
                validate_environment
                check_status
                ;;
            logs)
                check_dependencies
                validate_environment
                view_logs "$2"
                ;;
            clean)
                check_dependencies
                clean_resources
                ;;
            full)
                full_deploy
                ;;
            *)
                log_error "未知命令: $1"
                show_help
                exit 1
                ;;
        esac
    done
}

# 执行主函数
main "$@"
