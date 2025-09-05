#!/usr/bin/env python3
"""
质量门禁系统
用于自动化质量检查和门禁控制
"""

import os
import sys
import json
import yaml
import subprocess
from typing import Dict, Any, List, Optional, Tuple
from dataclasses import dataclass
from pathlib import Path
import logging
from datetime import datetime
import requests

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

@dataclass
class QualityGate:
    """质量门禁"""
    name: str
    description: str
    threshold: float
    current_value: float
    status: str  # "passed", "failed", "warning"
    details: Dict[str, Any]

@dataclass
class QualityReport:
    """质量报告"""
    timestamp: datetime
    overall_status: str
    gates: List[QualityGate]
    summary: Dict[str, Any]

class QualityGateSystem:
    """质量门禁系统"""
    
    def __init__(self, config_file: str = "docs/tools/automation/quality-gates-config.yaml"):
        self.config_file = Path(config_file)
        self.config = self._load_config()
        self.gates = []
        self.report = None
    
    def _load_config(self) -> Dict[str, Any]:
        """加载配置文件"""
        if self.config_file.exists():
            with open(self.config_file, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        else:
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            "gates": {
                "code_coverage": {
                    "enabled": True,
                    "threshold": 80.0,
                    "description": "代码覆盖率检查"
                },
                "code_quality": {
                    "enabled": True,
                    "threshold": 7.0,
                    "description": "代码质量评分"
                },
                "security_scan": {
                    "enabled": True,
                    "threshold": 0,
                    "description": "安全漏洞扫描"
                },
                "documentation_coverage": {
                    "enabled": True,
                    "threshold": 90.0,
                    "description": "文档覆盖率检查"
                },
                "test_coverage": {
                    "enabled": True,
                    "threshold": 85.0,
                    "description": "测试覆盖率检查"
                },
                "performance_benchmark": {
                    "enabled": True,
                    "threshold": 1000.0,
                    "description": "性能基准测试"
                }
            },
            "notifications": {
                "slack_webhook": None,
                "email_recipients": []
            }
        }
    
    def check_code_coverage(self) -> QualityGate:
        """检查代码覆盖率"""
        logger.info("检查代码覆盖率...")
        
        try:
            # 运行覆盖率测试
            result = subprocess.run(
                ["python", "-m", "pytest", "--cov=.", "--cov-report=json"],
                capture_output=True,
                text=True,
                cwd=Path.cwd()
            )
            
            if result.returncode == 0:
                # 解析覆盖率报告
                coverage_file = Path("coverage.json")
                if coverage_file.exists():
                    with open(coverage_file, 'r') as f:
                        coverage_data = json.load(f)
                    
                    total_coverage = coverage_data.get("totals", {}).get("percent_covered", 0)
                    
                    threshold = self.config["gates"]["code_coverage"]["threshold"]
                    status = "passed" if total_coverage >= threshold else "failed"
                    
                    return QualityGate(
                        name="code_coverage",
                        description="代码覆盖率检查",
                        threshold=threshold,
                        current_value=total_coverage,
                        status=status,
                        details={
                            "coverage_percent": total_coverage,
                            "lines_covered": coverage_data.get("totals", {}).get("covered_lines", 0),
                            "total_lines": coverage_data.get("totals", {}).get("num_statements", 0)
                        }
                    )
                else:
                    return QualityGate(
                        name="code_coverage",
                        description="代码覆盖率检查",
                        threshold=self.config["gates"]["code_coverage"]["threshold"],
                        current_value=0,
                        status="failed",
                        details={"error": "覆盖率报告文件不存在"}
                    )
            else:
                return QualityGate(
                    name="code_coverage",
                    description="代码覆盖率检查",
                    threshold=self.config["gates"]["code_coverage"]["threshold"],
                    current_value=0,
                    status="failed",
                    details={"error": f"测试执行失败: {result.stderr}"}
                )
        except Exception as e:
            logger.error(f"代码覆盖率检查失败: {e}")
            return QualityGate(
                name="code_coverage",
                description="代码覆盖率检查",
                threshold=self.config["gates"]["code_coverage"]["threshold"],
                current_value=0,
                status="failed",
                details={"error": str(e)}
            )
    
    def check_code_quality(self) -> QualityGate:
        """检查代码质量"""
        logger.info("检查代码质量...")
        
        try:
            # 运行代码质量检查（使用pylint）
            result = subprocess.run(
                ["python", "-m", "pylint", ".", "--output-format=json"],
                capture_output=True,
                text=True,
                cwd=Path.cwd()
            )
            
            # 解析pylint结果
            if result.stdout:
                try:
                    pylint_data = json.loads(result.stdout)
                    if isinstance(pylint_data, list) and pylint_data:
                        # 计算平均分数
                        scores = [item.get("score", 0) for item in pylint_data if "score" in item]
                        if scores:
                            avg_score = sum(scores) / len(scores)
                        else:
                            avg_score = 0
                    else:
                        avg_score = 0
                except json.JSONDecodeError:
                    avg_score = 0
            else:
                avg_score = 0
            
            threshold = self.config["gates"]["code_quality"]["threshold"]
            status = "passed" if avg_score >= threshold else "failed"
            
            return QualityGate(
                name="code_quality",
                description="代码质量评分",
                threshold=threshold,
                current_value=avg_score,
                status=status,
                details={
                    "pylint_score": avg_score,
                    "output": result.stdout[:500] if result.stdout else "无输出"
                }
            )
        except Exception as e:
            logger.error(f"代码质量检查失败: {e}")
            return QualityGate(
                name="code_quality",
                description="代码质量评分",
                threshold=self.config["gates"]["code_quality"]["threshold"],
                current_value=0,
                status="failed",
                details={"error": str(e)}
            )
    
    def check_security_scan(self) -> QualityGate:
        """安全检查"""
        logger.info("执行安全检查...")
        
        try:
            # 运行安全扫描（使用bandit）
            result = subprocess.run(
                ["python", "-m", "bandit", "-r", ".", "-f", "json"],
                capture_output=True,
                text=True,
                cwd=Path.cwd()
            )
            
            # 解析bandit结果
            if result.stdout:
                try:
                    bandit_data = json.loads(result.stdout)
                    high_severity = bandit_data.get("results", [])
                    high_count = len([r for r in high_severity if r.get("issue_severity") == "HIGH"])
                    medium_count = len([r for r in high_severity if r.get("issue_severity") == "MEDIUM"])
                    low_count = len([r for r in high_severity if r.get("issue_severity") == "LOW"])
                except json.JSONDecodeError:
                    high_count = medium_count = low_count = 0
            else:
                high_count = medium_count = low_count = 0
            
            threshold = self.config["gates"]["security_scan"]["threshold"]
            total_issues = high_count + medium_count + low_count
            status = "passed" if total_issues <= threshold else "failed"
            
            return QualityGate(
                name="security_scan",
                description="安全漏洞扫描",
                threshold=threshold,
                current_value=total_issues,
                status=status,
                details={
                    "high_severity": high_count,
                    "medium_severity": medium_count,
                    "low_severity": low_count,
                    "total_issues": total_issues
                }
            )
        except Exception as e:
            logger.error(f"安全检查失败: {e}")
            return QualityGate(
                name="security_scan",
                description="安全漏洞扫描",
                threshold=self.config["gates"]["security_scan"]["threshold"],
                current_value=999,
                status="failed",
                details={"error": str(e)}
            )
    
    def check_documentation_coverage(self) -> QualityGate:
        """检查文档覆盖率"""
        logger.info("检查文档覆盖率...")
        
        try:
            docs_dir = Path("docs")
            if not docs_dir.exists():
                return QualityGate(
                    name="documentation_coverage",
                    description="文档覆盖率检查",
                    threshold=self.config["gates"]["documentation_coverage"]["threshold"],
                    current_value=0,
                    status="failed",
                    details={"error": "docs目录不存在"}
                )
            
            # 统计文档文件
            doc_files = list(docs_dir.rglob("*.md"))
            total_docs = len(doc_files)
            
            # 检查关键文档是否存在
            required_docs = [
                "README.md",
                "docs/README.md",
                "docs/USER_GUIDE.md",
                "docs/API_REFERENCE.md",
                "docs/BEST_PRACTICES.md"
            ]
            
            existing_docs = sum(1 for doc in required_docs if Path(doc).exists())
            coverage_percent = (existing_docs / len(required_docs)) * 100
            
            threshold = self.config["gates"]["documentation_coverage"]["threshold"]
            status = "passed" if coverage_percent >= threshold else "failed"
            
            return QualityGate(
                name="documentation_coverage",
                description="文档覆盖率检查",
                threshold=threshold,
                current_value=coverage_percent,
                status=status,
                details={
                    "total_doc_files": total_docs,
                    "required_docs": len(required_docs),
                    "existing_docs": existing_docs,
                    "coverage_percent": coverage_percent
                }
            )
        except Exception as e:
            logger.error(f"文档覆盖率检查失败: {e}")
            return QualityGate(
                name="documentation_coverage",
                description="文档覆盖率检查",
                threshold=self.config["gates"]["documentation_coverage"]["threshold"],
                current_value=0,
                status="failed",
                details={"error": str(e)}
            )
    
    def check_test_coverage(self) -> QualityGate:
        """检查测试覆盖率"""
        logger.info("检查测试覆盖率...")
        
        try:
            # 查找测试文件
            test_files = list(Path.cwd().rglob("test_*.py")) + list(Path.cwd().rglob("*_test.py"))
            total_tests = len(test_files)
            
            # 运行测试并获取覆盖率
            if total_tests > 0:
                result = subprocess.run(
                    ["python", "-m", "pytest", "--cov=.", "--cov-report=term-missing"],
                    capture_output=True,
                    text=True,
                    cwd=Path.cwd()
                )
                
                # 从输出中提取覆盖率
                coverage_percent = 0
                if result.stdout:
                    for line in result.stdout.split('\n'):
                        if 'TOTAL' in line and '%' in line:
                            try:
                                coverage_percent = float(line.split('%')[0].split()[-1])
                                break
                            except (ValueError, IndexError):
                                continue
            else:
                coverage_percent = 0
            
            threshold = self.config["gates"]["test_coverage"]["threshold"]
            status = "passed" if coverage_percent >= threshold else "failed"
            
            return QualityGate(
                name="test_coverage",
                description="测试覆盖率检查",
                threshold=threshold,
                current_value=coverage_percent,
                status=status,
                details={
                    "test_files": total_tests,
                    "coverage_percent": coverage_percent
                }
            )
        except Exception as e:
            logger.error(f"测试覆盖率检查失败: {e}")
            return QualityGate(
                name="test_coverage",
                description="测试覆盖率检查",
                threshold=self.config["gates"]["test_coverage"]["threshold"],
                current_value=0,
                status="failed",
                details={"error": str(e)}
            )
    
    def check_performance_benchmark(self) -> QualityGate:
        """性能基准测试"""
        logger.info("执行性能基准测试...")
        
        try:
            # 运行性能测试
            result = subprocess.run(
                ["python", "-m", "pytest", "tests/performance/", "-v"],
                capture_output=True,
                text=True,
                cwd=Path.cwd()
            )
            
            # 解析性能结果
            response_time = 1000  # 默认值
            if result.stdout:
                for line in result.stdout.split('\n'):
                    if 'response_time' in line.lower():
                        try:
                            response_time = float(line.split(':')[-1].strip())
                            break
                        except (ValueError, IndexError):
                            continue
            
            threshold = self.config["gates"]["performance_benchmark"]["threshold"]
            status = "passed" if response_time <= threshold else "failed"
            
            return QualityGate(
                name="performance_benchmark",
                description="性能基准测试",
                threshold=threshold,
                current_value=response_time,
                status=status,
                details={
                    "response_time_ms": response_time,
                    "test_output": result.stdout[:500] if result.stdout else "无输出"
                }
            )
        except Exception as e:
            logger.error(f"性能基准测试失败: {e}")
            return QualityGate(
                name="performance_benchmark",
                description="性能基准测试",
                threshold=self.config["gates"]["performance_benchmark"]["threshold"],
                current_value=9999,
                status="failed",
                details={"error": str(e)}
            )
    
    def run_all_gates(self) -> QualityReport:
        """运行所有质量门禁"""
        logger.info("开始运行质量门禁检查...")
        
        gates = []
        
        # 运行各个门禁检查
        gate_checks = {
            "code_coverage": self.check_code_coverage,
            "code_quality": self.check_code_quality,
            "security_scan": self.check_security_scan,
            "documentation_coverage": self.check_documentation_coverage,
            "test_coverage": self.check_test_coverage,
            "performance_benchmark": self.check_performance_benchmark
        }
        
        for gate_name, check_func in gate_checks.items():
            if self.config["gates"].get(gate_name, {}).get("enabled", True):
                logger.info(f"运行门禁检查: {gate_name}")
                gate = check_func()
                gates.append(gate)
                logger.info(f"{gate_name}: {gate.status} ({gate.current_value}/{gate.threshold})")
        
        # 计算总体状态
        failed_gates = [g for g in gates if g.status == "failed"]
        warning_gates = [g for g in gates if g.status == "warning"]
        
        if failed_gates:
            overall_status = "failed"
        elif warning_gates:
            overall_status = "warning"
        else:
            overall_status = "passed"
        
        # 生成摘要
        summary = {
            "total_gates": len(gates),
            "passed_gates": len([g for g in gates if g.status == "passed"]),
            "failed_gates": len(failed_gates),
            "warning_gates": len(warning_gates),
            "overall_status": overall_status
        }
        
        self.report = QualityReport(
            timestamp=datetime.now(),
            overall_status=overall_status,
            gates=gates,
            summary=summary
        )
        
        self.gates = gates
        
        logger.info(f"质量门禁检查完成，总体状态: {overall_status}")
        return self.report
    
    def generate_report(self) -> str:
        """生成质量报告"""
        if not self.report:
            self.run_all_gates()
        
        report_lines = [
            "# 质量门禁报告",
            f"生成时间: {self.report.timestamp.strftime('%Y-%m-%d %H:%M:%S')}",
            f"总体状态: {self.report.overall_status}",
            "",
            "## 摘要",
            f"- 总门禁数: {self.report.summary['total_gates']}",
            f"- 通过门禁: {self.report.summary['passed_gates']}",
            f"- 失败门禁: {self.report.summary['failed_gates']}",
            f"- 警告门禁: {self.report.summary['warning_gates']}",
            "",
            "## 详细结果",
            ""
        ]
        
        for gate in self.report.gates:
            status_emoji = "✅" if gate.status == "passed" else "❌" if gate.status == "failed" else "⚠️"
            report_lines.extend([
                f"### {status_emoji} {gate.name}",
                f"**描述**: {gate.description}",
                f"**状态**: {gate.status}",
                f"**当前值**: {gate.current_value}",
                f"**阈值**: {gate.threshold}",
                ""
            ])
            
            if gate.details:
                report_lines.append("**详细信息**:")
                for key, value in gate.details.items():
                    report_lines.append(f"- {key}: {value}")
                report_lines.append("")
        
        return "\n".join(report_lines)
    
    def send_notifications(self):
        """发送通知"""
        if not self.report:
            return
        
        # Slack通知
        slack_webhook = self.config.get("notifications", {}).get("slack_webhook")
        if slack_webhook:
            self._send_slack_notification()
        
        # 邮件通知
        email_recipients = self.config.get("notifications", {}).get("email_recipients", [])
        if email_recipients:
            self._send_email_notification()
    
    def _send_slack_notification(self):
        """发送Slack通知"""
        try:
            slack_webhook = self.config["notifications"]["slack_webhook"]
            
            status_emoji = "✅" if self.report.overall_status == "passed" else "❌"
            message = f"{status_emoji} 质量门禁检查完成\n总体状态: {self.report.overall_status}\n"
            
            if self.report.summary["failed_gates"] > 0:
                message += f"失败门禁: {self.report.summary['failed_gates']}\n"
            
            payload = {"text": message}
            response = requests.post(slack_webhook, json=payload)
            
            if response.status_code == 200:
                logger.info("Slack通知发送成功")
            else:
                logger.error(f"Slack通知发送失败: {response.status_code}")
        except Exception as e:
            logger.error(f"Slack通知发送异常: {e}")
    
    def _send_email_notification(self):
        """发送邮件通知"""
        # 这里应该实现邮件发送逻辑
        logger.info("邮件通知功能待实现")

def main():
    """主函数"""
    quality_system = QualityGateSystem()
    report = quality_system.run_all_gates()
    
    # 生成报告
    report_content = quality_system.generate_report()
    print(report_content)
    
    # 保存报告
    report_file = Path("docs/quality-report.md")
    with open(report_file, 'w', encoding='utf-8') as f:
        f.write(report_content)
    
    # 发送通知
    quality_system.send_notifications()
    
    # 根据结果设置退出码
    if report.overall_status == "failed":
        sys.exit(1)
    else:
        sys.exit(0)

if __name__ == "__main__":
    main()
