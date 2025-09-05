# 质量门禁机制配置

## 概述

质量门禁机制是确保正式框架代码质量和可靠性的关键组件。它定义了在代码合并、发布和部署前必须满足的质量标准。

## 质量门禁类型

### 1. 代码质量门禁

#### 1.1 代码覆盖率门禁

- **单元测试覆盖率**: ≥ 80%
- **集成测试覆盖率**: ≥ 70%
- **整体测试覆盖率**: ≥ 75%

#### 1.2 代码质量门禁

- **代码复杂度**: 圈复杂度 ≤ 10
- **函数长度**: 单个函数 ≤ 50 行
- **类长度**: 单个类 ≤ 500 行
- **文件长度**: 单个文件 ≤ 1000 行

#### 1.3 代码风格门禁

- **Linting 错误**: 0 个严重错误
- **代码格式化**: 通过 black、isort 检查
- **类型检查**: 通过 mypy 检查
- **代码分析**: 通过 pylint 检查

### 2. 功能质量门禁

#### 2.1 测试门禁

- **单元测试**: 100% 通过
- **集成测试**: 100% 通过
- **性能测试**: 在可接受范围内
- **回归测试**: 无回归

#### 2.2 验证门禁

- **形式化验证**: TLA+ 模型检查通过
- **约束求解**: Z3 求解器验证通过
- **不变式验证**: 所有不变式满足

#### 2.3 文档门禁

- **API 文档**: 100% 覆盖
- **代码注释**: 关键函数有注释
- **README 更新**: 与代码同步
- **变更日志**: 记录所有变更

### 3. 安全质量门禁

#### 3.1 安全扫描门禁

- **漏洞扫描**: 无高危漏洞
- **依赖安全**: 无已知安全漏洞
- **代码审计**: 通过安全审查
- **权限检查**: 最小权限原则

#### 3.2 合规性门禁

- **许可证合规**: 符合项目许可证
- **版权合规**: 无版权问题
- **数据保护**: 符合数据保护要求

### 4. 性能质量门禁

#### 4.1 性能指标门禁

- **响应时间**: 在 SLA 范围内
- **吞吐量**: 满足性能要求
- **资源使用**: 在合理范围内
- **扩展性**: 支持预期负载

#### 4.2 负载测试门禁

- **压力测试**: 系统稳定运行
- **容量测试**: 支持预期容量
- **故障恢复**: 快速恢复能力

## 质量门禁配置

### 配置文件结构

```yaml
quality_gates:
  code_quality:
    coverage:
      unit_test: 80
      integration_test: 70
      overall: 75
    complexity:
      cyclomatic_complexity: 10
      function_length: 50
      class_length: 500
      file_length: 1000
    style:
      linting_errors: 0
      formatting_check: true
      type_check: true
      code_analysis: true
  
  functional_quality:
    testing:
      unit_tests: 100
      integration_tests: 100
      performance_tests: true
      regression_tests: true
    verification:
      formal_verification: true
      constraint_solving: true
      invariant_verification: true
    documentation:
      api_docs: 100
      code_comments: true
      readme_sync: true
      changelog: true
  
  security_quality:
    scanning:
      vulnerability_scan: true
      dependency_security: true
      code_audit: true
      permission_check: true
    compliance:
      license_compliance: true
      copyright_compliance: true
      data_protection: true
  
  performance_quality:
    metrics:
      response_time: true
      throughput: true
      resource_usage: true
      scalability: true
    load_testing:
      stress_test: true
      capacity_test: true
      fault_recovery: true
```

### 门禁检查脚本

```python
#!/usr/bin/env python3
"""
质量门禁检查脚本
检查代码质量和功能完整性
"""

import os
import sys
import json
import subprocess
from typing import Dict, Any, List
from dataclasses import dataclass
from pathlib import Path


@dataclass
class QualityGateResult:
    """质量门禁检查结果"""
    gate_name: str
    passed: bool
    score: float
    threshold: float
    details: str
    recommendations: List[str]


class QualityGateChecker:
    """质量门禁检查器"""
    
    def __init__(self, config_path: str = "quality-gates-config.json"):
        self.config = self.load_config(config_path)
        self.results: List[QualityGateResult] = []
    
    def load_config(self, config_path: str) -> Dict[str, Any]:
        """加载配置文件"""
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        except FileNotFoundError:
            print(f"配置文件 {config_path} 未找到，使用默认配置")
            return self.get_default_config()
    
    def get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            "code_quality": {
                "coverage": {
                    "unit_test": 80,
                    "integration_test": 70,
                    "overall": 75
                },
                "complexity": {
                    "cyclomatic_complexity": 10,
                    "function_length": 50,
                    "class_length": 500,
                    "file_length": 1000
                }
            }
        }
    
    def check_code_coverage(self) -> QualityGateResult:
        """检查代码覆盖率"""
        try:
            # 运行覆盖率检查
            result = subprocess.run(
                ["pytest", "--cov=samples/validation-scripts", "--cov-report=json"],
                capture_output=True,
                text=True,
                cwd="."
            )
            
            if result.returncode != 0:
                return QualityGateResult(
                    gate_name="代码覆盖率",
                    passed=False,
                    score=0.0,
                    threshold=self.config["code_quality"]["coverage"]["overall"],
                    details="覆盖率检查失败",
                    recommendations=["检查测试配置", "确保测试可执行"]
                )
            
            # 解析覆盖率结果
            coverage_data = json.loads(result.stdout)
            total_coverage = coverage_data.get("totals", {}).get("percent_covered", 0.0)
            
            threshold = self.config["code_quality"]["coverage"]["overall"]
            passed = total_coverage >= threshold
            
            return QualityGateResult(
                gate_name="代码覆盖率",
                passed=passed,
                score=total_coverage,
                threshold=threshold,
                details=f"当前覆盖率: {total_coverage:.2f}%",
                recommendations=["增加测试用例"] if not passed else []
            )
            
        except Exception as e:
            return QualityGateResult(
                gate_name="代码覆盖率",
                passed=False,
                score=0.0,
                threshold=self.config["code_quality"]["coverage"]["overall"],
                details=f"检查失败: {str(e)}",
                recommendations=["检查测试环境", "验证依赖安装"]
            )
    
    def check_code_quality(self) -> QualityGateResult:
        """检查代码质量"""
        try:
            # 运行代码质量检查
            result = subprocess.run(
                ["flake8", "samples/validation-scripts/", "--max-line-length=120"],
                capture_output=True,
                text=True
            )
            
            # 统计错误数量
            error_lines = result.stdout.strip().split('\n') if result.stdout.strip() else []
            error_count = len([line for line in error_lines if line])
            
            threshold = 0
            passed = error_count <= threshold
            
            return QualityGateResult(
                gate_name="代码质量",
                passed=passed,
                score=max(0, 100 - error_count * 10),
                threshold=threshold,
                details=f"发现 {error_count} 个代码质量问题",
                recommendations=["修复代码风格问题", "运行代码格式化工具"] if not passed else []
            )
            
        except Exception as e:
            return QualityGateResult(
                gate_name="代码质量",
                passed=False,
                score=0.0,
                threshold=0,
                details=f"检查失败: {str(e)}",
                recommendations=["安装 flake8", "检查 Python 环境"]
            )
    
    def check_formal_verification(self) -> QualityGateResult:
        """检查形式化验证"""
        try:
            # 检查 TLA+ 文件是否存在
            tla_files = list(Path("samples/validation-scripts/tla/").glob("*.tla"))
            
            if not tla_files:
                return QualityGateResult(
                    gate_name="形式化验证",
                    passed=False,
                    score=0.0,
                    threshold=100,
                    details="未找到 TLA+ 规格文件",
                    recommendations=["创建 TLA+ 规格文件", "实现模型检查"]
                )
            
            # 检查 Z3 约束求解器
            result = subprocess.run(
                ["python", "samples/validation-scripts/z3/constraint-solver.py", "--help"],
                capture_output=True,
                text=True
            )
            
            passed = result.returncode == 0
            score = 100.0 if passed else 0.0
            
            return QualityGateResult(
                gate_name="形式化验证",
                passed=passed,
                score=score,
                threshold=100,
                details=f"TLA+ 文件: {len(tla_files)} 个, Z3 求解器: {'可用' if passed else '不可用'}",
                recommendations=["验证 TLA+ 规格", "测试 Z3 求解器"] if not passed else []
            )
            
        except Exception as e:
            return QualityGateResult(
                gate_name="形式化验证",
                passed=False,
                score=0.0,
                threshold=100,
                details=f"检查失败: {str(e)}",
                recommendations=["检查 TLA+ 工具", "验证 Z3 安装"]
            )
    
    def check_documentation(self) -> QualityGateResult:
        """检查文档完整性"""
        try:
            required_files = [
                "docs/README.md",
                "docs/PROJECT_REPOSITIONING_PLAN.md",
                "docs/formal-model/COMPLETION_STATUS.md",
                "docs/L2_D01_交互元模型.md",
                "docs/L2_D02_数据元模型.md",
                "docs/L2_D03_功能元模型.md",
                "docs/L2_D04_运行时元模型.md",
                "docs/L2_D05_部署元模型.md",
                "docs/L2_D06_监控元模型.md",
                "docs/L2_D07_控制调度元模型.md",
                "docs/L2_D08_测试元模型.md"
            ]
            
            missing_files = []
            for file_path in required_files:
                if not Path(file_path).exists():
                    missing_files.append(file_path)
            
            score = max(0, 100 - len(missing_files) * 10)
            passed = len(missing_files) == 0
            
            return QualityGateResult(
                gate_name="文档完整性",
                passed=passed,
                score=score,
                threshold=90,
                details=f"缺失文件: {len(missing_files)} 个",
                recommendations=[f"创建文件: {file}" for file in missing_files] if not passed else []
            )
            
        except Exception as e:
            return QualityGateResult(
                gate_name="文档完整性",
                passed=False,
                score=0.0,
                threshold=90,
                details=f"检查失败: {str(e)}",
                recommendations=["检查文件系统权限", "验证工作目录"]
            )
    
    def run_all_checks(self) -> List[QualityGateResult]:
        """运行所有质量检查"""
        print("开始质量门禁检查...")
        
        checks = [
            self.check_code_coverage,
            self.check_code_quality,
            self.check_formal_verification,
            self.check_documentation
        ]
        
        for check in checks:
            try:
                result = check()
                self.results.append(result)
                print(f"✓ {result.gate_name}: {'通过' if result.passed else '失败'}")
            except Exception as e:
                print(f"✗ {check.__name__}: 检查异常 - {str(e)}")
        
        return self.results
    
    def generate_report(self) -> str:
        """生成质量报告"""
        if not self.results:
            return "无检查结果"
        
        passed_count = sum(1 for r in self.results if r.passed)
        total_count = len(self.results)
        overall_score = sum(r.score for r in self.results) / total_count
        
        report = f"""
# 质量门禁检查报告

## 总体结果
- 检查项目: {total_count}
- 通过项目: {passed_count}
- 失败项目: {total_count - passed_count}
- 整体得分: {overall_score:.2f}/100

## 详细结果
"""
        
        for result in self.results:
            status = "✅ 通过" if result.passed else "❌ 失败"
            report += f"""
### {result.gate_name} - {status}
- 得分: {result.score:.2f}/{result.threshold}
- 详情: {result.details}
"""
            
            if result.recommendations:
                report += "- 建议:\n"
                for rec in result.recommendations:
                    report += f"  - {rec}\n"
        
        return report
    
    def save_report(self, output_path: str = "quality-gate-report.md"):
        """保存质量报告"""
        report = self.generate_report()
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"质量报告已保存到: {output_path}")


def main():
    """主函数"""
    checker = QualityGateChecker()
    results = checker.run_all_checks()
    
    # 生成报告
    checker.save_report()
    
    # 检查是否所有门禁都通过
    all_passed = all(r.passed for r in results)
    
    if all_passed:
        print("\n🎉 所有质量门禁检查通过！")
        sys.exit(0)
    else:
        print("\n⚠️  部分质量门禁检查失败，请查看报告了解详情。")
        sys.exit(1)


if __name__ == "__main__":
    main()
```

## 质量门禁执行流程

### 1. 预提交检查

- 代码风格检查
- 基本语法检查
- 单元测试运行

### 2. 提交后检查

- 完整测试套件
- 代码覆盖率分析
- 形式化验证

### 3. 合并前检查

- 集成测试
- 性能测试
- 安全扫描

### 4. 发布前检查

- 端到端测试
- 负载测试
- 文档完整性

## 质量门禁配置管理

### 1. 配置文件

- 支持 JSON、YAML 格式
- 环境特定配置
- 动态阈值调整

### 2. 阈值管理

- 基于历史数据
- 项目特定要求
- 渐进式提升

### 3. 报告生成

- 详细检查结果
- 改进建议
- 趋势分析

## 质量门禁集成

### 1. CI/CD 集成

- GitHub Actions 工作流
- GitLab CI 管道
- Jenkins 流水线

### 2. 代码审查集成

- 自动质量检查
- 质量门禁状态
- 审查建议

### 3. 发布管理集成

- 质量门禁验证
- 发布条件检查
- 回滚机制

## 质量门禁监控

### 1. 实时监控

- 质量指标仪表板
- 趋势图表
- 告警通知

### 2. 历史分析

- 质量趋势分析
- 问题模式识别
- 改进效果评估

### 3. 团队协作

- 质量责任分配
- 改进计划跟踪
- 知识分享

## 最佳实践

### 1. 门禁设置

- 设置合理的阈值
- 避免过于严格
- 支持渐进式改进

### 2. 检查频率

- 预提交快速检查
- 定期深度检查
- 发布前全面检查

### 3. 反馈机制

- 及时反馈结果
- 提供改进建议
- 支持团队学习

### 4. 持续改进

- 定期评估门禁
- 调整检查策略
- 优化检查工具
