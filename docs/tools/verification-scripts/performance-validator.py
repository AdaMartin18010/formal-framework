#!/usr/bin/env python3
"""
性能验证器
用于验证系统性能指标是否满足要求
"""

import requests
import time
import json
import statistics
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Any, Tuple
from dataclasses import dataclass
from datetime import datetime
import argparse
import sys
import logging

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class PerformanceMetric:
    """性能指标"""
    name: str
    value: float
    unit: str
    threshold: float
    passed: bool
    timestamp: datetime

@dataclass
class PerformanceResult:
    """性能测试结果"""
    test_name: str
    total_requests: int
    successful_requests: int
    failed_requests: int
    avg_response_time: float
    min_response_time: float
    max_response_time: float
    p50_response_time: float
    p95_response_time: float
    p99_response_time: float
    requests_per_second: float
    throughput: float
    error_rate: float
    duration: float
    timestamp: datetime

class PerformanceValidator:
    """性能验证器"""
    
    def __init__(self, base_url: str = "http://localhost:8080"):
        self.base_url = base_url
        self.session = requests.Session()
        self.session.timeout = 30
        self.results: List[PerformanceResult] = []
        
    def percentile(self, data: List[float], percentile: int) -> float:
        """计算百分位数"""
        if not data:
            return 0.0
        sorted_data = sorted(data)
        index = int(len(sorted_data) * percentile / 100)
        return sorted_data[min(index, len(sorted_data) - 1)]
    
    def single_request(self, endpoint: str, method: str = "GET", 
                      data: Dict[str, Any] = None) -> Tuple[bool, float, int]:
        """执行单个请求"""
        start_time = time.time()
        
        try:
            if method.upper() == "GET":
                response = self.session.get(f"{self.base_url}{endpoint}")
            elif method.upper() == "POST":
                response = self.session.post(
                    f"{self.base_url}{endpoint}",
                    json=data,
                    headers={"Content-Type": "application/json"}
                )
            elif method.upper() == "PUT":
                response = self.session.put(
                    f"{self.base_url}{endpoint}",
                    json=data,
                    headers={"Content-Type": "application/json"}
                )
            elif method.upper() == "DELETE":
                response = self.session.delete(f"{self.base_url}{endpoint}")
            else:
                return False, 0, 0
            
            duration = time.time() - start_time
            success = response.status_code in [200, 201, 202, 204]
            
            return success, duration, response.status_code
            
        except Exception as e:
            duration = time.time() - start_time
            logger.error(f"请求失败: {e}")
            return False, duration, 0
    
    def load_test(self, endpoint: str, method: str = "GET", 
                 data: Dict[str, Any] = None, num_requests: int = 100,
                 max_workers: int = 10) -> PerformanceResult:
        """执行负载测试"""
        logger.info(f"开始负载测试: {method} {endpoint}, {num_requests} 个请求, {max_workers} 个并发")
        
        start_time = time.time()
        results = []
        
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = [
                executor.submit(self.single_request, endpoint, method, data)
                for _ in range(num_requests)
            ]
            
            for future in as_completed(futures):
                success, duration, status_code = future.result()
                results.append({
                    "success": success,
                    "duration": duration,
                    "status_code": status_code
                })
        
        end_time = time.time()
        total_duration = end_time - start_time
        
        # 分析结果
        successful_requests = [r for r in results if r["success"]]
        failed_requests = [r for r in results if not r["success"]]
        
        if successful_requests:
            durations = [r["duration"] for r in successful_requests]
            avg_response_time = statistics.mean(durations)
            min_response_time = min(durations)
            max_response_time = max(durations)
            p50_response_time = self.percentile(durations, 50)
            p95_response_time = self.percentile(durations, 95)
            p99_response_time = self.percentile(durations, 99)
        else:
            avg_response_time = 0
            min_response_time = 0
            max_response_time = 0
            p50_response_time = 0
            p95_response_time = 0
            p99_response_time = 0
        
        total_requests = len(results)
        successful_count = len(successful_requests)
        failed_count = len(failed_requests)
        requests_per_second = total_requests / total_duration
        throughput = successful_count / total_duration
        error_rate = failed_count / total_requests * 100
        
        result = PerformanceResult(
            test_name=f"{method} {endpoint}",
            total_requests=total_requests,
            successful_requests=successful_count,
            failed_requests=failed_count,
            avg_response_time=avg_response_time,
            min_response_time=min_response_time,
            max_response_time=max_response_time,
            p50_response_time=p50_response_time,
            p95_response_time=p95_response_time,
            p99_response_time=p99_response_time,
            requests_per_second=requests_per_second,
            throughput=throughput,
            error_rate=error_rate,
            duration=total_duration,
            timestamp=datetime.now()
        )
        
        self.results.append(result)
        return result
    
    def stress_test(self, endpoint: str, method: str = "GET",
                   data: Dict[str, Any] = None, duration_seconds: int = 60,
                   target_rps: int = 10) -> PerformanceResult:
        """执行压力测试"""
        logger.info(f"开始压力测试: {method} {endpoint}, {duration_seconds} 秒, {target_rps} RPS")
        
        start_time = time.time()
        results = []
        request_count = 0
        
        while time.time() - start_time < duration_seconds:
            batch_start = time.time()
            
            # 发送一批请求
            with ThreadPoolExecutor(max_workers=target_rps) as executor:
                futures = [
                    executor.submit(self.single_request, endpoint, method, data)
                    for _ in range(target_rps)
                ]
                
                for future in as_completed(futures):
                    success, duration, status_code = future.result()
                    results.append({
                        "success": success,
                        "duration": duration,
                        "status_code": status_code
                    })
                    request_count += 1
            
            # 控制请求频率
            batch_duration = time.time() - batch_start
            sleep_time = max(0, 1.0 - batch_duration)
            time.sleep(sleep_time)
        
        total_duration = time.time() - start_time
        
        # 分析结果
        successful_requests = [r for r in results if r["success"]]
        failed_requests = [r for r in results if not r["success"]]
        
        if successful_requests:
            durations = [r["duration"] for r in successful_requests]
            avg_response_time = statistics.mean(durations)
            min_response_time = min(durations)
            max_response_time = max(durations)
            p50_response_time = self.percentile(durations, 50)
            p95_response_time = self.percentile(durations, 95)
            p99_response_time = self.percentile(durations, 99)
        else:
            avg_response_time = 0
            min_response_time = 0
            max_response_time = 0
            p50_response_time = 0
            p95_response_time = 0
            p99_response_time = 0
        
        total_requests = len(results)
        successful_count = len(successful_requests)
        failed_count = len(failed_requests)
        requests_per_second = total_requests / total_duration
        throughput = successful_count / total_duration
        error_rate = failed_count / total_requests * 100
        
        result = PerformanceResult(
            test_name=f"Stress Test {method} {endpoint}",
            total_requests=total_requests,
            successful_requests=successful_count,
            failed_requests=failed_count,
            avg_response_time=avg_response_time,
            min_response_time=min_response_time,
            max_response_time=max_response_time,
            p50_response_time=p50_response_time,
            p95_response_time=p95_response_time,
            p99_response_time=p99_response_time,
            requests_per_second=requests_per_second,
            throughput=throughput,
            error_rate=error_rate,
            duration=total_duration,
            timestamp=datetime.now()
        )
        
        self.results.append(result)
        return result
    
    def validate_performance_requirements(self, requirements: Dict[str, float]) -> List[PerformanceMetric]:
        """验证性能要求"""
        metrics = []
        
        for result in self.results:
            # 验证平均响应时间
            if "avg_response_time" in requirements:
                threshold = requirements["avg_response_time"]
                passed = result.avg_response_time <= threshold
                metrics.append(PerformanceMetric(
                    name=f"{result.test_name} - 平均响应时间",
                    value=result.avg_response_time,
                    unit="秒",
                    threshold=threshold,
                    passed=passed,
                    timestamp=result.timestamp
                ))
            
            # 验证P95响应时间
            if "p95_response_time" in requirements:
                threshold = requirements["p95_response_time"]
                passed = result.p95_response_time <= threshold
                metrics.append(PerformanceMetric(
                    name=f"{result.test_name} - P95响应时间",
                    value=result.p95_response_time,
                    unit="秒",
                    threshold=threshold,
                    passed=passed,
                    timestamp=result.timestamp
                ))
            
            # 验证错误率
            if "error_rate" in requirements:
                threshold = requirements["error_rate"]
                passed = result.error_rate <= threshold
                metrics.append(PerformanceMetric(
                    name=f"{result.test_name} - 错误率",
                    value=result.error_rate,
                    unit="%",
                    threshold=threshold,
                    passed=passed,
                    timestamp=result.timestamp
                ))
            
            # 验证吞吐量
            if "throughput" in requirements:
                threshold = requirements["throughput"]
                passed = result.throughput >= threshold
                metrics.append(PerformanceMetric(
                    name=f"{result.test_name} - 吞吐量",
                    value=result.throughput,
                    unit="请求/秒",
                    threshold=threshold,
                    passed=passed,
                    timestamp=result.timestamp
                ))
        
        return metrics
    
    def generate_report(self) -> Dict[str, Any]:
        """生成性能报告"""
        if not self.results:
            return {"error": "没有测试结果"}
        
        total_tests = len(self.results)
        total_requests = sum(r.total_requests for r in self.results)
        total_successful = sum(r.successful_requests for r in self.results)
        total_failed = sum(r.failed_requests for r in self.results)
        
        avg_response_times = [r.avg_response_time for r in self.results if r.avg_response_time > 0]
        p95_response_times = [r.p95_response_time for r in self.results if r.p95_response_time > 0]
        error_rates = [r.error_rate for r in self.results]
        throughputs = [r.throughput for r in self.results if r.throughput > 0]
        
        report = {
            "summary": {
                "total_tests": total_tests,
                "total_requests": total_requests,
                "total_successful": total_successful,
                "total_failed": total_failed,
                "overall_success_rate": (total_successful / total_requests * 100) if total_requests > 0 else 0,
                "avg_response_time": statistics.mean(avg_response_times) if avg_response_times else 0,
                "max_response_time": max(avg_response_times) if avg_response_times else 0,
                "avg_p95_response_time": statistics.mean(p95_response_times) if p95_response_times else 0,
                "max_p95_response_time": max(p95_response_times) if p95_response_times else 0,
                "avg_error_rate": statistics.mean(error_rates) if error_rates else 0,
                "max_error_rate": max(error_rates) if error_rates else 0,
                "avg_throughput": statistics.mean(throughputs) if throughputs else 0,
                "max_throughput": max(throughputs) if throughputs else 0,
                "timestamp": datetime.now().isoformat()
            },
            "results": [
                {
                    "test_name": r.test_name,
                    "total_requests": r.total_requests,
                    "successful_requests": r.successful_requests,
                    "failed_requests": r.failed_requests,
                    "avg_response_time": r.avg_response_time,
                    "min_response_time": r.min_response_time,
                    "max_response_time": r.max_response_time,
                    "p50_response_time": r.p50_response_time,
                    "p95_response_time": r.p95_response_time,
                    "p99_response_time": r.p99_response_time,
                    "requests_per_second": r.requests_per_second,
                    "throughput": r.throughput,
                    "error_rate": r.error_rate,
                    "duration": r.duration,
                    "timestamp": r.timestamp.isoformat()
                }
                for r in self.results
            ]
        }
        
        return report
    
    def save_report(self, filename: str = None):
        """保存性能报告"""
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"performance_report_{timestamp}.json"
        
        report = self.generate_report()
        
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        
        logger.info(f"性能报告已保存到: {filename}")
        return filename

def main():
    parser = argparse.ArgumentParser(description='性能验证器')
    parser.add_argument('--url', default='http://localhost:8080',
                       help='目标服务URL')
    parser.add_argument('--endpoint', default='/api/accounts',
                       help='测试端点')
    parser.add_argument('--method', default='GET',
                       help='HTTP方法')
    parser.add_argument('--requests', type=int, default=100,
                       help='请求数量')
    parser.add_argument('--workers', type=int, default=10,
                       help='并发工作线程数')
    parser.add_argument('--duration', type=int, default=60,
                       help='压力测试持续时间(秒)')
    parser.add_argument('--rps', type=int, default=10,
                       help='目标请求速率(请求/秒)')
    parser.add_argument('--test-type', choices=['load', 'stress'], default='load',
                       help='测试类型')
    parser.add_argument('--output', default=None,
                       help='报告输出文件名')
    parser.add_argument('--requirements', default=None,
                       help='性能要求JSON文件')
    
    args = parser.parse_args()
    
    validator = PerformanceValidator(args.url)
    
    try:
        # 准备测试数据
        test_data = None
        if args.method.upper() in ['POST', 'PUT']:
            test_data = {
                "name": "Test Data",
                "value": "Test Value"
            }
        
        # 执行测试
        if args.test_type == 'load':
            result = validator.load_test(
                args.endpoint, args.method, test_data, 
                args.requests, args.workers
            )
        else:
            result = validator.stress_test(
                args.endpoint, args.method, test_data,
                args.duration, args.rps
            )
        
        # 验证性能要求
        if args.requirements:
            with open(args.requirements, 'r') as f:
                requirements = json.load(f)
            
            metrics = validator.validate_performance_requirements(requirements)
            
            print("\n性能要求验证结果:")
            print("="*50)
            for metric in metrics:
                status = "✅ 通过" if metric.passed else "❌ 失败"
                print(f"{metric.name}: {metric.value:.3f} {metric.unit} (阈值: {metric.threshold} {metric.unit}) {status}")
        
        # 生成并保存报告
        report_file = validator.save_report(args.output)
        
        # 打印摘要
        report = validator.generate_report()
        summary = report["summary"]
        
        print("\n" + "="*50)
        print("性能测试报告摘要")
        print("="*50)
        print(f"测试数量: {summary['total_tests']}")
        print(f"总请求数: {summary['total_requests']}")
        print(f"成功请求数: {summary['total_successful']}")
        print(f"失败请求数: {summary['total_failed']}")
        print(f"总体成功率: {summary['overall_success_rate']:.2f}%")
        print(f"平均响应时间: {summary['avg_response_time']:.3f} 秒")
        print(f"最大响应时间: {summary['max_response_time']:.3f} 秒")
        print(f"平均P95响应时间: {summary['avg_p95_response_time']:.3f} 秒")
        print(f"平均错误率: {summary['avg_error_rate']:.2f}%")
        print(f"平均吞吐量: {summary['avg_throughput']:.2f} 请求/秒")
        print(f"报告文件: {report_file}")
        print("="*50)
        
    except Exception as e:
        logger.error(f"性能测试过程中发生错误: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
