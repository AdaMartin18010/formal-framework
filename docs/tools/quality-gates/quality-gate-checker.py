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
