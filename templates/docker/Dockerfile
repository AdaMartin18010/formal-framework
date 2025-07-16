# 多阶段构建的Dockerfile模板
# 适用于Rust微服务项目

# 阶段1: 构建阶段
FROM rust:1.70-alpine AS builder

# 设置工作目录
WORKDIR /app

# 安装构建依赖
RUN apk add --no-cache \
    musl-dev \
    openssl-dev \
    pkgconfig \
    && rm -rf /var/cache/apk/*

# 复制Cargo.toml和Cargo.lock
COPY Cargo.toml Cargo.lock ./

# 创建虚拟的main.rs来缓存依赖
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码
COPY src ./src

# 重新构建应用（依赖已缓存）
RUN cargo build --release --bin {{project_name}}

# 阶段2: 运行时阶段
FROM alpine:latest AS runtime

# 安装运行时依赖
RUN apk add --no-cache \
    ca-certificates \
    tzdata \
    && rm -rf /var/cache/apk/*

# 创建非root用户
RUN addgroup -g 1001 -S appgroup && \
    adduser -u 1001 -S appuser -G appgroup

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/release/{{project_name}} /app/{{project_name}}

# 复制配置文件
COPY configs/ /app/configs/

# 设置权限
RUN chown -R appuser:appgroup /app

# 切换到非root用户
USER appuser

# 暴露端口
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8080/health || exit 1

# 设置环境变量
ENV RUST_LOG=info
ENV RUST_BACKTRACE=1

# 启动应用
CMD ["./{{project_name}}"]

# 标签
LABEL maintainer="{{maintainer}}"
LABEL version="{{version}}"
LABEL description="{{description}}"
LABEL org.opencontainers.image.source="{{repository}}"

# 元数据
ARG BUILD_DATE
ARG VCS_REF
LABEL org.opencontainers.image.created=$BUILD_DATE
LABEL org.opencontainers.image.revision=$VCS_REF
LABEL org.opencontainers.image.version={{version}} 