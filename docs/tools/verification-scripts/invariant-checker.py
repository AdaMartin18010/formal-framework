#!/usr/bin/env python3
"""
系统不变性检查器
用于验证系统在运行过程中是否保持关键不变性
"""

import requests
import time
import json
import logging
from typing import Dict, List, Any, Callable
from dataclasses import dataclass
from datetime import datetime, timedelta
import argparse
import sys

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('invariant_checker.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

@dataclass
class InvariantResult:
    """不变性检查结果"""
    name: str
    passed: bool
    message: str
    timestamp: datetime
    duration: float
    details: Dict[str, Any] = None

class InvariantChecker:
    """不变性检查器"""
    
    def __init__(self, base_url: str = "http://localhost:8080"):
        self.base_url = base_url
        self.session = requests.Session()
        self.session.timeout = 30
        self.results: List[InvariantResult] = []
        
    def check_http_health(self) -> InvariantResult:
        """检查HTTP服务健康状态"""
        start_time = time.time()
        
        try:
            response = self.session.get(f"{self.base_url}/health")
            duration = time.time() - start_time
            
            if response.status_code == 200:
                health_data = response.json()
                return InvariantResult(
                    name="HTTP健康检查",
                    passed=True,
                    message="服务健康状态正常",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "status_code": response.status_code,
                        "response_time": duration,
                        "health_data": health_data
                    }
                )
            else:
                return InvariantResult(
                    name="HTTP健康检查",
                    passed=False,
                    message=f"服务返回错误状态码: {response.status_code}",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={"status_code": response.status_code}
                )
                
        except Exception as e:
            duration = time.time() - start_time
            return InvariantResult(
                name="HTTP健康检查",
                passed=False,
                message=f"健康检查失败: {str(e)}",
                timestamp=datetime.now(),
                duration=duration,
                details={"error": str(e)}
            )
    
    def check_data_consistency(self) -> InvariantResult:
        """检查数据一致性"""
        start_time = time.time()
        
        try:
            # 获取所有账户
            accounts_response = self.session.get(f"{self.base_url}/api/accounts")
            if accounts_response.status_code != 200:
                return InvariantResult(
                    name="数据一致性检查",
                    passed=False,
                    message="无法获取账户数据",
                    timestamp=datetime.now(),
                    duration=time.time() - start_time
                )
            
            accounts = accounts_response.json().get("data", [])
            total_balance = 0
            active_accounts = 0
            
            for account in accounts:
                if account.get("status") == "ACTIVE":
                    active_accounts += 1
                    total_balance += float(account.get("balance", 0))
            
            # 检查总余额是否为正数
            balance_positive = total_balance >= 0
            
            # 检查活跃账户数量
            has_active_accounts = active_accounts > 0
            
            duration = time.time() - start_time
            
            if balance_positive and has_active_accounts:
                return InvariantResult(
                    name="数据一致性检查",
                    passed=True,
                    message="数据一致性检查通过",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "total_balance": total_balance,
                        "active_accounts": active_accounts,
                        "total_accounts": len(accounts)
                    }
                )
            else:
                return InvariantResult(
                    name="数据一致性检查",
                    passed=False,
                    message=f"数据一致性问题: 余额={total_balance}, 活跃账户={active_accounts}",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "total_balance": total_balance,
                        "active_accounts": active_accounts,
                        "balance_positive": balance_positive,
                        "has_active_accounts": has_active_accounts
                    }
                )
                
        except Exception as e:
            duration = time.time() - start_time
            return InvariantResult(
                name="数据一致性检查",
                passed=False,
                message=f"数据一致性检查失败: {str(e)}",
                timestamp=datetime.now(),
                duration=duration,
                details={"error": str(e)}
            )
    
    def check_transaction_integrity(self) -> InvariantResult:
        """检查交易完整性"""
        start_time = time.time()
        
        try:
            # 获取最近的交易
            transactions_response = self.session.get(
                f"{self.base_url}/api/transactions",
                params={"limit": 100}
            )
            
            if transactions_response.status_code != 200:
                return InvariantResult(
                    name="交易完整性检查",
                    passed=False,
                    message="无法获取交易数据",
                    timestamp=datetime.now(),
                    duration=time.time() - start_time
                )
            
            transactions = transactions_response.json().get("data", [])
            
            # 检查交易完整性
            valid_transactions = 0
            invalid_transactions = 0
            total_amount = 0
            
            for transaction in transactions:
                amount = float(transaction.get("amount", 0))
                transaction_type = transaction.get("type", "")
                status = transaction.get("status", "")
                
                # 检查交易状态
                if status in ["BOOKED", "PENDING"]:
                    valid_transactions += 1
                    total_amount += amount
                else:
                    invalid_transactions += 1
            
            duration = time.time() - start_time
            
            # 检查不变性：有效交易应该占大多数
            if valid_transactions > invalid_transactions:
                return InvariantResult(
                    name="交易完整性检查",
                    passed=True,
                    message="交易完整性检查通过",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "valid_transactions": valid_transactions,
                        "invalid_transactions": invalid_transactions,
                        "total_amount": total_amount,
                        "total_transactions": len(transactions)
                    }
                )
            else:
                return InvariantResult(
                    name="交易完整性检查",
                    passed=False,
                    message=f"交易完整性问题: 有效={valid_transactions}, 无效={invalid_transactions}",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "valid_transactions": valid_transactions,
                        "invalid_transactions": invalid_transactions,
                        "total_amount": total_amount
                    }
                )
                
        except Exception as e:
            duration = time.time() - start_time
            return InvariantResult(
                name="交易完整性检查",
                passed=False,
                message=f"交易完整性检查失败: {str(e)}",
                timestamp=datetime.now(),
                duration=duration,
                details={"error": str(e)}
            )
    
    def check_performance_bounds(self) -> InvariantResult:
        """检查性能边界"""
        start_time = time.time()
        
        try:
            # 执行多个请求来测试性能
            response_times = []
            success_count = 0
            error_count = 0
            
            for i in range(10):
                request_start = time.time()
                response = self.session.get(f"{self.base_url}/api/accounts")
                request_duration = time.time() - request_start
                
                response_times.append(request_duration)
                
                if response.status_code == 200:
                    success_count += 1
                else:
                    error_count += 1
                
                time.sleep(0.1)  # 避免过于频繁的请求
            
            avg_response_time = sum(response_times) / len(response_times)
            max_response_time = max(response_times)
            min_response_time = min(response_times)
            
            duration = time.time() - start_time
            
            # 性能边界检查
            avg_ok = avg_response_time < 1.0  # 平均响应时间小于1秒
            max_ok = max_response_time < 5.0  # 最大响应时间小于5秒
            success_rate_ok = success_count / (success_count + error_count) > 0.95  # 成功率大于95%
            
            if avg_ok and max_ok and success_rate_ok:
                return InvariantResult(
                    name="性能边界检查",
                    passed=True,
                    message="性能边界检查通过",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "avg_response_time": avg_response_time,
                        "max_response_time": max_response_time,
                        "min_response_time": min_response_time,
                        "success_count": success_count,
                        "error_count": error_count,
                        "success_rate": success_count / (success_count + error_count)
                    }
                )
            else:
                return InvariantResult(
                    name="性能边界检查",
                    passed=False,
                    message=f"性能边界问题: 平均={avg_response_time:.3f}s, 最大={max_response_time:.3f}s, 成功率={success_count/(success_count+error_count):.2%}",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "avg_response_time": avg_response_time,
                        "max_response_time": max_response_time,
                        "min_response_time": min_response_time,
                        "success_count": success_count,
                        "error_count": error_count,
                        "success_rate": success_count / (success_count + error_count),
                        "avg_ok": avg_ok,
                        "max_ok": max_ok,
                        "success_rate_ok": success_rate_ok
                    }
                )
                
        except Exception as e:
            duration = time.time() - start_time
            return InvariantResult(
                name="性能边界检查",
                passed=False,
                message=f"性能边界检查失败: {str(e)}",
                timestamp=datetime.now(),
                duration=duration,
                details={"error": str(e)}
            )
    
    def check_resource_usage(self) -> InvariantResult:
        """检查资源使用情况"""
        start_time = time.time()
        
        try:
            # 获取系统状态
            status_response = self.session.get(f"{self.base_url}/api/system/status")
            
            if status_response.status_code != 200:
                return InvariantResult(
                    name="资源使用检查",
                    passed=False,
                    message="无法获取系统状态",
                    timestamp=datetime.now(),
                    duration=time.time() - start_time
                )
            
            status_data = status_response.json()
            
            # 检查资源使用情况
            cpu_usage = status_data.get("cpu_usage", 0)
            memory_usage = status_data.get("memory_usage", 0)
            disk_usage = status_data.get("disk_usage", 0)
            
            duration = time.time() - start_time
            
            # 资源使用边界检查
            cpu_ok = cpu_usage < 80  # CPU使用率小于80%
            memory_ok = memory_usage < 85  # 内存使用率小于85%
            disk_ok = disk_usage < 90  # 磁盘使用率小于90%
            
            if cpu_ok and memory_ok and disk_ok:
                return InvariantResult(
                    name="资源使用检查",
                    passed=True,
                    message="资源使用检查通过",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "cpu_usage": cpu_usage,
                        "memory_usage": memory_usage,
                        "disk_usage": disk_usage
                    }
                )
            else:
                return InvariantResult(
                    name="资源使用检查",
                    passed=False,
                    message=f"资源使用问题: CPU={cpu_usage}%, 内存={memory_usage}%, 磁盘={disk_usage}%",
                    timestamp=datetime.now(),
                    duration=duration,
                    details={
                        "cpu_usage": cpu_usage,
                        "memory_usage": memory_usage,
                        "disk_usage": disk_usage,
                        "cpu_ok": cpu_ok,
                        "memory_ok": memory_ok,
                        "disk_ok": disk_ok
                    }
                )
                
        except Exception as e:
            duration = time.time() - start_time
            return InvariantResult(
                name="资源使用检查",
                passed=False,
                message=f"资源使用检查失败: {str(e)}",
                timestamp=datetime.now(),
                duration=duration,
                details={"error": str(e)}
            )
    
    def run_all_checks(self) -> List[InvariantResult]:
        """运行所有不变性检查"""
        logger.info("开始运行不变性检查...")
        
        checks = [
            self.check_http_health,
            self.check_data_consistency,
            self.check_transaction_integrity,
            self.check_performance_bounds,
            self.check_resource_usage
        ]
        
        results = []
        for check in checks:
            try:
                result = check()
                results.append(result)
                self.results.append(result)
                
                if result.passed:
                    logger.info(f"✅ {result.name}: {result.message}")
                else:
                    logger.error(f"❌ {result.name}: {result.message}")
                    
            except Exception as e:
                error_result = InvariantResult(
                    name=check.__name__,
                    passed=False,
                    message=f"检查执行失败: {str(e)}",
                    timestamp=datetime.now(),
                    duration=0,
                    details={"error": str(e)}
                )
                results.append(error_result)
                self.results.append(error_result)
                logger.error(f"❌ {check.__name__}: {str(e)}")
        
        return results
    
    def generate_report(self) -> Dict[str, Any]:
        """生成检查报告"""
        if not self.results:
            return {"error": "没有检查结果"}
        
        total_checks = len(self.results)
        passed_checks = len([r for r in self.results if r.passed])
        failed_checks = total_checks - passed_checks
        
        avg_duration = sum(r.duration for r in self.results) / total_checks
        
        report = {
            "summary": {
                "total_checks": total_checks,
                "passed_checks": passed_checks,
                "failed_checks": failed_checks,
                "success_rate": passed_checks / total_checks * 100,
                "avg_duration": avg_duration,
                "timestamp": datetime.now().isoformat()
            },
            "results": [
                {
                    "name": r.name,
                    "passed": r.passed,
                    "message": r.message,
                    "timestamp": r.timestamp.isoformat(),
                    "duration": r.duration,
                    "details": r.details
                }
                for r in self.results
            ]
        }
        
        return report
    
    def save_report(self, filename: str = None):
        """保存检查报告"""
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"invariant_check_report_{timestamp}.json"
        
        report = self.generate_report()
        
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        
        logger.info(f"检查报告已保存到: {filename}")
        return filename

def main():
    parser = argparse.ArgumentParser(description='系统不变性检查器')
    parser.add_argument('--url', default='http://localhost:8080',
                       help='目标服务URL')
    parser.add_argument('--output', default=None,
                       help='报告输出文件名')
    parser.add_argument('--continuous', action='store_true',
                       help='持续运行检查')
    parser.add_argument('--interval', type=int, default=60,
                       help='持续检查间隔(秒)')
    
    args = parser.parse_args()
    
    checker = InvariantChecker(args.url)
    
    try:
        if args.continuous:
            logger.info(f"开始持续不变性检查，间隔: {args.interval} 秒")
            while True:
                results = checker.run_all_checks()
                
                # 检查是否有失败的检查
                failed_checks = [r for r in results if not r.passed]
                if failed_checks:
                    logger.warning(f"发现 {len(failed_checks)} 个失败的检查")
                
                # 保存报告
                checker.save_report()
                
                time.sleep(args.interval)
        else:
            # 单次检查
            results = checker.run_all_checks()
            
            # 生成并保存报告
            report_file = checker.save_report(args.output)
            
            # 打印摘要
            report = checker.generate_report()
            summary = report["summary"]
            
            print("\n" + "="*50)
            print("不变性检查报告摘要")
            print("="*50)
            print(f"总检查数: {summary['total_checks']}")
            print(f"通过检查: {summary['passed_checks']}")
            print(f"失败检查: {summary['failed_checks']}")
            print(f"成功率: {summary['success_rate']:.2f}%")
            print(f"平均耗时: {summary['avg_duration']:.3f} 秒")
            print(f"报告文件: {report_file}")
            print("="*50)
            
            # 如果有失败的检查，退出码为1
            if summary['failed_checks'] > 0:
                sys.exit(1)
                
    except KeyboardInterrupt:
        logger.info("收到中断信号，正在退出...")
        sys.exit(0)
    except Exception as e:
        logger.error(f"检查过程中发生错误: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
