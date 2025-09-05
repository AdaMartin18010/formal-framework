#!/usr/bin/env python3
"""
数据一致性检查器
用于验证分布式系统中的数据一致性
"""

import requests
import time
import json
import logging
from typing import Dict, List, Any, Tuple
from dataclasses import dataclass
from datetime import datetime, timedelta
import argparse
import sys
import hashlib
import sqlite3
from concurrent.futures import ThreadPoolExecutor, as_completed

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class ConsistencyCheck:
    """一致性检查结果"""
    check_name: str
    passed: bool
    message: str
    timestamp: datetime
    details: Dict[str, Any] = None

class DataConsistencyChecker:
    """数据一致性检查器"""
    
    def __init__(self, services: List[str], db_config: Dict[str, str] = None):
        self.services = services
        self.db_config = db_config or {}
        self.session = requests.Session()
        self.session.timeout = 30
        self.results: List[ConsistencyCheck] = []
        
    def get_data_from_service(self, service_url: str, endpoint: str) -> Tuple[bool, Any]:
        """从服务获取数据"""
        try:
            response = self.session.get(f"{service_url}{endpoint}")
            if response.status_code == 200:
                return True, response.json()
            else:
                logger.error(f"服务 {service_url} 返回错误状态码: {response.status_code}")
                return False, None
        except Exception as e:
            logger.error(f"从服务 {service_url} 获取数据失败: {e}")
            return False, None
    
    def get_data_from_database(self, query: str, params: Tuple = ()) -> Tuple[bool, List[Dict]]:
        """从数据库获取数据"""
        try:
            if not self.db_config:
                return False, []
            
            conn = sqlite3.connect(self.db_config.get('database', 'test.db'))
            conn.row_factory = sqlite3.Row
            cursor = conn.cursor()
            
            cursor.execute(query, params)
            rows = cursor.fetchall()
            
            # 转换为字典列表
            data = [dict(row) for row in rows]
            
            conn.close()
            return True, data
            
        except Exception as e:
            logger.error(f"从数据库获取数据失败: {e}")
            return False, []
    
    def calculate_data_hash(self, data: Any) -> str:
        """计算数据哈希值"""
        data_str = json.dumps(data, sort_keys=True, ensure_ascii=False)
        return hashlib.md5(data_str.encode('utf-8')).hexdigest()
    
    def check_account_balance_consistency(self) -> ConsistencyCheck:
        """检查账户余额一致性"""
        logger.info("检查账户余额一致性...")
        
        try:
            # 从所有服务获取账户数据
            service_data = {}
            for service_url in self.services:
                success, data = self.get_data_from_service(service_url, "/api/accounts")
                if success:
                    service_data[service_url] = data
                else:
                    return ConsistencyCheck(
                        check_name="账户余额一致性",
                        passed=False,
                        message=f"无法从服务 {service_url} 获取账户数据",
                        timestamp=datetime.now()
                    )
            
            # 检查数据一致性
            if len(service_data) < 2:
                return ConsistencyCheck(
                    check_name="账户余额一致性",
                    passed=False,
                    message="需要至少两个服务进行一致性检查",
                    timestamp=datetime.now()
                )
            
            # 比较数据哈希值
            hashes = {}
            for service_url, data in service_data.items():
                hashes[service_url] = self.calculate_data_hash(data)
            
            # 检查所有哈希值是否相同
            unique_hashes = set(hashes.values())
            if len(unique_hashes) == 1:
                return ConsistencyCheck(
                    check_name="账户余额一致性",
                    passed=True,
                    message="所有服务的账户数据一致",
                    timestamp=datetime.now(),
                    details={
                        "services": list(service_data.keys()),
                        "data_hash": list(unique_hashes)[0],
                        "account_count": len(service_data[list(service_data.keys())[0]].get('data', []))
                    }
                )
            else:
                return ConsistencyCheck(
                    check_name="账户余额一致性",
                    passed=False,
                    message="服务间账户数据不一致",
                    timestamp=datetime.now(),
                    details={
                        "hashes": hashes,
                        "unique_hashes": list(unique_hashes)
                    }
                )
                
        except Exception as e:
            return ConsistencyCheck(
                check_name="账户余额一致性",
                passed=False,
                message=f"检查过程中发生错误: {str(e)}",
                timestamp=datetime.now(),
                details={"error": str(e)}
            )
    
    def check_transaction_consistency(self) -> ConsistencyCheck:
        """检查交易一致性"""
        logger.info("检查交易一致性...")
        
        try:
            # 从所有服务获取交易数据
            service_data = {}
            for service_url in self.services:
                success, data = self.get_data_from_service(service_url, "/api/transactions")
                if success:
                    service_data[service_url] = data
                else:
                    return ConsistencyCheck(
                        check_name="交易一致性",
                        passed=False,
                        message=f"无法从服务 {service_url} 获取交易数据",
                        timestamp=datetime.now()
                    )
            
            # 检查数据一致性
            if len(service_data) < 2:
                return ConsistencyCheck(
                    check_name="交易一致性",
                    passed=False,
                    message="需要至少两个服务进行一致性检查",
                    timestamp=datetime.now()
                )
            
            # 比较交易数据
            all_transactions = {}
            for service_url, data in service_data.items():
                transactions = data.get('data', [])
                for transaction in transactions:
                    tx_id = transaction.get('id')
                    if tx_id:
                        if tx_id not in all_transactions:
                            all_transactions[tx_id] = {}
                        all_transactions[tx_id][service_url] = transaction
            
            # 检查每个交易在所有服务中是否一致
            inconsistent_transactions = []
            for tx_id, service_transactions in all_transactions.items():
                if len(service_transactions) != len(self.services):
                    inconsistent_transactions.append({
                        "transaction_id": tx_id,
                        "reason": "交易在某些服务中缺失",
                        "services": list(service_transactions.keys())
                    })
                    continue
                
                # 比较交易数据
                first_service = list(service_transactions.keys())[0]
                first_transaction = service_transactions[first_service]
                
                for service_url, transaction in service_transactions.items():
                    if transaction != first_transaction:
                        inconsistent_transactions.append({
                            "transaction_id": tx_id,
                            "reason": "交易数据不一致",
                            "services": [first_service, service_url]
                        })
                        break
            
            if not inconsistent_transactions:
                return ConsistencyCheck(
                    check_name="交易一致性",
                    passed=True,
                    message="所有服务的交易数据一致",
                    timestamp=datetime.now(),
                    details={
                        "total_transactions": len(all_transactions),
                        "services": list(service_data.keys())
                    }
                )
            else:
                return ConsistencyCheck(
                    check_name="交易一致性",
                    passed=False,
                    message=f"发现 {len(inconsistent_transactions)} 个不一致的交易",
                    timestamp=datetime.now(),
                    details={
                        "inconsistent_transactions": inconsistent_transactions,
                        "total_transactions": len(all_transactions)
                    }
                )
                
        except Exception as e:
            return ConsistencyCheck(
                check_name="交易一致性",
                passed=False,
                message=f"检查过程中发生错误: {str(e)}",
                timestamp=datetime.now(),
                details={"error": str(e)}
            )
    
    def check_database_consistency(self) -> ConsistencyCheck:
        """检查数据库一致性"""
        logger.info("检查数据库一致性...")
        
        try:
            if not self.db_config:
                return ConsistencyCheck(
                    check_name="数据库一致性",
                    passed=False,
                    message="未配置数据库连接",
                    timestamp=datetime.now()
                )
            
            # 检查账户表一致性
            success, accounts = self.get_data_from_database(
                "SELECT id, account_number, balance, status FROM accounts ORDER BY id"
            )
            
            if not success:
                return ConsistencyCheck(
                    check_name="数据库一致性",
                    passed=False,
                    message="无法从数据库获取账户数据",
                    timestamp=datetime.now()
                )
            
            # 检查交易表一致性
            success, transactions = self.get_data_from_database(
                "SELECT id, account_id, amount, status, created_at FROM transactions ORDER BY id"
            )
            
            if not success:
                return ConsistencyCheck(
                    check_name="数据库一致性",
                    passed=False,
                    message="无法从数据库获取交易数据",
                    timestamp=datetime.now()
                )
            
            # 检查数据完整性
            account_ids = {acc['id'] for acc in accounts}
            transaction_account_ids = {tx['account_id'] for tx in transactions}
            
            # 检查外键约束
            orphaned_transactions = transaction_account_ids - account_ids
            
            # 检查账户余额计算
            balance_errors = []
            for account in accounts:
                account_id = account['id']
                account_balance = account['balance']
                
                # 计算实际余额
                account_transactions = [tx for tx in transactions if tx['account_id'] == account_id]
                calculated_balance = sum(tx['amount'] for tx in account_transactions if tx['status'] == 'BOOKED')
                
                if abs(account_balance - calculated_balance) > 0.01:  # 允许小的浮点误差
                    balance_errors.append({
                        "account_id": account_id,
                        "stored_balance": account_balance,
                        "calculated_balance": calculated_balance,
                        "difference": account_balance - calculated_balance
                    })
            
            if not orphaned_transactions and not balance_errors:
                return ConsistencyCheck(
                    check_name="数据库一致性",
                    passed=True,
                    message="数据库数据一致",
                    timestamp=datetime.now(),
                    details={
                        "account_count": len(accounts),
                        "transaction_count": len(transactions)
                    }
                )
            else:
                return ConsistencyCheck(
                    check_name="数据库一致性",
                    passed=False,
                    message=f"发现数据一致性问题: 孤立交易={len(orphaned_transactions)}, 余额错误={len(balance_errors)}",
                    timestamp=datetime.now(),
                    details={
                        "orphaned_transactions": list(orphaned_transactions),
                        "balance_errors": balance_errors,
                        "account_count": len(accounts),
                        "transaction_count": len(transactions)
                    }
                )
                
        except Exception as e:
            return ConsistencyCheck(
                check_name="数据库一致性",
                passed=False,
                message=f"检查过程中发生错误: {str(e)}",
                timestamp=datetime.now(),
                details={"error": str(e)}
            )
    
    def check_eventual_consistency(self, max_wait_time: int = 30) -> ConsistencyCheck:
        """检查最终一致性"""
        logger.info("检查最终一致性...")
        
        try:
            start_time = time.time()
            check_interval = 5  # 每5秒检查一次
            
            while time.time() - start_time < max_wait_time:
                # 执行一致性检查
                account_check = self.check_account_balance_consistency()
                transaction_check = self.check_transaction_consistency()
                
                if account_check.passed and transaction_check.passed:
                    return ConsistencyCheck(
                        check_name="最终一致性",
                        passed=True,
                        message="系统已达到最终一致性",
                        timestamp=datetime.now(),
                        details={
                            "wait_time": time.time() - start_time,
                            "account_check": account_check.details,
                            "transaction_check": transaction_check.details
                        }
                    )
                
                time.sleep(check_interval)
            
            return ConsistencyCheck(
                check_name="最终一致性",
                passed=False,
                message=f"在 {max_wait_time} 秒内未达到最终一致性",
                timestamp=datetime.now(),
                details={
                    "max_wait_time": max_wait_time,
                    "final_account_check": account_check.details,
                    "final_transaction_check": transaction_check.details
                }
            )
            
        except Exception as e:
            return ConsistencyCheck(
                check_name="最终一致性",
                passed=False,
                message=f"检查过程中发生错误: {str(e)}",
                timestamp=datetime.now(),
                details={"error": str(e)}
            )
    
    def run_all_checks(self) -> List[ConsistencyCheck]:
        """运行所有一致性检查"""
        logger.info("开始运行数据一致性检查...")
        
        checks = [
            self.check_account_balance_consistency,
            self.check_transaction_consistency,
            self.check_database_consistency,
            self.check_eventual_consistency
        ]
        
        results = []
        for check in checks:
            try:
                result = check()
                results.append(result)
                self.results.append(result)
                
                if result.passed:
                    logger.info(f"✅ {result.check_name}: {result.message}")
                else:
                    logger.error(f"❌ {result.check_name}: {result.message}")
                    
            except Exception as e:
                error_result = ConsistencyCheck(
                    check_name=check.__name__,
                    passed=False,
                    message=f"检查执行失败: {str(e)}",
                    timestamp=datetime.now(),
                    details={"error": str(e)}
                )
                results.append(error_result)
                self.results.append(error_result)
                logger.error(f"❌ {check.__name__}: {str(e)}")
        
        return results
    
    def generate_report(self) -> Dict[str, Any]:
        """生成一致性检查报告"""
        if not self.results:
            return {"error": "没有检查结果"}
        
        total_checks = len(self.results)
        passed_checks = len([r for r in self.results if r.passed])
        failed_checks = total_checks - passed_checks
        
        report = {
            "summary": {
                "total_checks": total_checks,
                "passed_checks": passed_checks,
                "failed_checks": failed_checks,
                "success_rate": passed_checks / total_checks * 100,
                "timestamp": datetime.now().isoformat()
            },
            "results": [
                {
                    "check_name": r.check_name,
                    "passed": r.passed,
                    "message": r.message,
                    "timestamp": r.timestamp.isoformat(),
                    "details": r.details
                }
                for r in self.results
            ]
        }
        
        return report
    
    def save_report(self, filename: str = None):
        """保存一致性检查报告"""
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"consistency_check_report_{timestamp}.json"
        
        report = self.generate_report()
        
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        
        logger.info(f"一致性检查报告已保存到: {filename}")
        return filename

def main():
    parser = argparse.ArgumentParser(description='数据一致性检查器')
    parser.add_argument('--services', nargs='+', default=['http://localhost:8080'],
                       help='服务URL列表')
    parser.add_argument('--database', default=None,
                       help='数据库文件路径')
    parser.add_argument('--output', default=None,
                       help='报告输出文件名')
    parser.add_argument('--max-wait', type=int, default=30,
                       help='最终一致性检查最大等待时间(秒)')
    
    args = parser.parse_args()
    
    # 配置数据库连接
    db_config = {}
    if args.database:
        db_config['database'] = args.database
    
    checker = DataConsistencyChecker(args.services, db_config)
    
    try:
        # 运行所有检查
        results = checker.run_all_checks()
        
        # 生成并保存报告
        report_file = checker.save_report(args.output)
        
        # 打印摘要
        report = checker.generate_report()
        summary = report["summary"]
        
        print("\n" + "="*50)
        print("数据一致性检查报告摘要")
        print("="*50)
        print(f"总检查数: {summary['total_checks']}")
        print(f"通过检查: {summary['passed_checks']}")
        print(f"失败检查: {summary['failed_checks']}")
        print(f"成功率: {summary['success_rate']:.2f}%")
        print(f"报告文件: {report_file}")
        print("="*50)
        
        # 如果有失败的检查，退出码为1
        if summary['failed_checks'] > 0:
            sys.exit(1)
            
    except Exception as e:
        logger.error(f"一致性检查过程中发生错误: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
