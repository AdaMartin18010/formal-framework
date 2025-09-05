#!/usr/bin/env python3
"""
正式验证框架性能基准测试套件
提供全面的性能测试和基准对比
"""

import time
import json
import statistics
import subprocess
import psutil
import threading
from typing import Dict, List, Any, Optional, Callable
from dataclasses import dataclass, asdict
from datetime import datetime
import concurrent.futures


@dataclass
class BenchmarkResult:
    """基准测试结果"""
    test_name: str
    test_type: str
    duration_ms: float
    memory_mb: float
    cpu_percent: float
    throughput: float
    error_rate: float
    timestamp: datetime
    metadata: Dict[str, Any]


@dataclass
class PerformanceMetrics:
    """性能指标"""
    avg_duration: float
    min_duration: float
    max_duration: float
    p95_duration: float
    p99_duration: float
    avg_memory: float
    max_memory: float
    avg_cpu: float
    max_cpu: float
    throughput: float
    error_rate: float


class PerformanceMonitor:
    """性能监控器"""
    
    def __init__(self):
        self.monitoring = False
        self.metrics = []
        self.start_time = None
        self.start_memory = None
    
    def start_monitoring(self):
        """开始监控"""
        self.monitoring = True
        self.start_time = time.time()
        self.start_memory = psutil.Process().memory_info().rss / 1024 / 1024
        self.metrics = []
        
        # 启动监控线程
        self.monitor_thread = threading.Thread(target=self._monitor_loop)
        self.monitor_thread.daemon = True
        self.monitor_thread.start()
    
    def stop_monitoring(self) -> Dict[str, float]:
        """停止监控并返回结果"""
        self.monitoring = False
        if self.monitor_thread:
            self.monitor_thread.join(timeout=1)
        
        if not self.metrics:
            return {
                'duration_ms': 0,
                'memory_mb': 0,
                'cpu_percent': 0
            }
        
        duration = (time.time() - self.start_time) * 1000
        memory = max(m['memory'] for m in self.metrics) - self.start_memory
        cpu = statistics.mean(m['cpu'] for m in self.metrics)
        
        return {
            'duration_ms': duration,
            'memory_mb': memory,
            'cpu_percent': cpu
        }
    
    def _monitor_loop(self):
        """监控循环"""
        process = psutil.Process()
        while self.monitoring:
            try:
                memory = process.memory_info().rss / 1024 / 1024
                cpu = process.cpu_percent()
                self.metrics.append({
                    'memory': memory,
                    'cpu': cpu,
                    'timestamp': time.time()
                })
                time.sleep(0.1)
            except:
                break


class BenchmarkSuite:
    """基准测试套件"""
    
    def __init__(self, config_path: str = "benchmark-config.json"):
        self.config = self.load_config(config_path)
        self.results: List[BenchmarkResult] = []
        self.baseline_results: Dict[str, BenchmarkResult] = {}
    
    def load_config(self, config_path: str) -> Dict[str, Any]:
        """加载配置文件"""
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        except FileNotFoundError:
            return self.get_default_config()
    
    def get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            "benchmarks": {
                "model_verification": {
                    "name": "模型验证性能测试",
                    "iterations": 10,
                    "timeout_seconds": 300
                },
                "constraint_solving": {
                    "name": "约束求解性能测试",
                    "iterations": 20,
                    "timeout_seconds": 180
                },
                "model_checking": {
                    "name": "模型检查性能测试",
                    "iterations": 5,
                    "timeout_seconds": 600
                },
                "code_generation": {
                    "name": "代码生成性能测试",
                    "iterations": 15,
                    "timeout_seconds": 120
                }
            },
            "performance_thresholds": {
                "model_verification": {
                    "max_duration_ms": 5000,
                    "max_memory_mb": 512,
                    "min_throughput": 10
                },
                "constraint_solving": {
                    "max_duration_ms": 2000,
                    "max_memory_mb": 256,
                    "min_throughput": 50
                },
                "model_checking": {
                    "max_duration_ms": 10000,
                    "max_memory_mb": 1024,
                    "min_throughput": 5
                },
                "code_generation": {
                    "max_duration_ms": 3000,
                    "max_memory_mb": 384,
                    "min_throughput": 20
                }
            }
        }
    
    def run_benchmark(self, test_name: str, test_func: Callable, 
                     test_type: str = "functional", iterations: int = 10) -> BenchmarkResult:
        """运行基准测试"""
        print(f"运行基准测试: {test_name}")
        
        results = []
        total_errors = 0
        
        for i in range(iterations):
            print(f"  迭代 {i+1}/{iterations}")
            
            monitor = PerformanceMonitor()
            monitor.start_monitoring()
            
            start_time = time.time()
            try:
                # 执行测试函数
                result = test_func()
                success = True
            except Exception as e:
                print(f"    错误: {str(e)}")
                result = None
                success = False
                total_errors += 1
            
            end_time = time.time()
            metrics = monitor.stop_monitoring()
            
            if success:
                duration = (end_time - start_time) * 1000
                results.append({
                    'duration': duration,
                    'memory': metrics['memory_mb'],
                    'cpu': metrics['cpu_percent'],
                    'result': result
                })
        
        if not results:
            return BenchmarkResult(
                test_name=test_name,
                test_type=test_type,
                duration_ms=0,
                memory_mb=0,
                cpu_percent=0,
                throughput=0,
                error_rate=100.0,
                timestamp=datetime.now(),
                metadata={'error': 'All iterations failed'}
            )
        
        # 计算统计指标
        durations = [r['duration'] for r in results]
        memories = [r['memory'] for r in results]
        cpus = [r['cpu'] for r in results]
        
        avg_duration = statistics.mean(durations)
        avg_memory = statistics.mean(memories)
        avg_cpu = statistics.mean(cpus)
        
        # 计算吞吐量（基于测试结果）
        if results and results[0]['result']:
            throughput = self._calculate_throughput(results[0]['result'])
        else:
            throughput = 0
        
        error_rate = (total_errors / iterations) * 100
        
        benchmark_result = BenchmarkResult(
            test_name=test_name,
            test_type=test_type,
            duration_ms=avg_duration,
            memory_mb=avg_memory,
            cpu_percent=avg_cpu,
            throughput=throughput,
            error_rate=error_rate,
            timestamp=datetime.now(),
            metadata={
                'iterations': iterations,
                'successful_iterations': len(results),
                'failed_iterations': total_errors,
                'durations': durations,
                'memories': memories,
                'cpus': cpus
            }
        )
        
        self.results.append(benchmark_result)
        return benchmark_result
    
    def _calculate_throughput(self, result: Any) -> float:
        """计算吞吐量"""
        if isinstance(result, dict):
            if 'items_processed' in result and 'duration' in result:
                return result['items_processed'] / result['duration']
            elif 'operations' in result:
                return result['operations']
        elif isinstance(result, (int, float)):
            return float(result)
        return 0.0
    
    def run_model_verification_benchmark(self) -> BenchmarkResult:
        """运行模型验证基准测试"""
        def test_func():
            # 模拟模型验证过程
            time.sleep(0.1)  # 模拟验证时间
            return {
                'models_verified': 10,
                'duration': 0.1,
                'items_processed': 10
            }
        
        config = self.config['benchmarks']['model_verification']
        return self.run_benchmark(
            "模型验证性能测试",
            test_func,
            "model_verification",
            config['iterations']
        )
    
    def run_constraint_solving_benchmark(self) -> BenchmarkResult:
        """运行约束求解基准测试"""
        def test_func():
            # 模拟约束求解过程
            time.sleep(0.05)  # 模拟求解时间
            return {
                'constraints_solved': 50,
                'duration': 0.05,
                'items_processed': 50
            }
        
        config = self.config['benchmarks']['constraint_solving']
        return self.run_benchmark(
            "约束求解性能测试",
            test_func,
            "constraint_solving",
            config['iterations']
        )
    
    def run_model_checking_benchmark(self) -> BenchmarkResult:
        """运行模型检查基准测试"""
        def test_func():
            # 模拟模型检查过程
            time.sleep(0.2)  # 模拟检查时间
            return {
                'states_checked': 1000,
                'duration': 0.2,
                'items_processed': 1000
            }
        
        config = self.config['benchmarks']['model_checking']
        return self.run_benchmark(
            "模型检查性能测试",
            test_func,
            "model_checking",
            config['iterations']
        )
    
    def run_code_generation_benchmark(self) -> BenchmarkResult:
        """运行代码生成基准测试"""
        def test_func():
            # 模拟代码生成过程
            time.sleep(0.08)  # 模拟生成时间
            return {
                'lines_generated': 200,
                'duration': 0.08,
                'items_processed': 200
            }
        
        config = self.config['benchmarks']['code_generation']
        return self.run_benchmark(
            "代码生成性能测试",
            test_func,
            "code_generation",
            config['iterations']
        )
    
    def run_all_benchmarks(self) -> List[BenchmarkResult]:
        """运行所有基准测试"""
        print("=== 开始运行完整基准测试套件 ===")
        
        benchmarks = [
            self.run_model_verification_benchmark,
            self.run_constraint_solving_benchmark,
            self.run_model_checking_benchmark,
            self.run_code_generation_benchmark
        ]
        
        results = []
        for benchmark_func in benchmarks:
            try:
                result = benchmark_func()
                results.append(result)
                print(f"✓ {result.test_name} 完成")
            except Exception as e:
                print(f"✗ 基准测试失败: {str(e)}")
        
        print("=== 基准测试套件完成 ===")
        return results
    
    def compare_with_baseline(self, test_name: str) -> Dict[str, Any]:
        """与基线结果对比"""
        if test_name not in self.baseline_results:
            return {'error': 'No baseline found'}
        
        current_results = [r for r in self.results if r.test_name == test_name]
        if not current_results:
            return {'error': 'No current results found'}
        
        current = current_results[-1]  # 使用最新的结果
        baseline = self.baseline_results[test_name]
        
        comparison = {
            'test_name': test_name,
            'duration_change': {
                'current': current.duration_ms,
                'baseline': baseline.duration_ms,
                'change_percent': ((current.duration_ms - baseline.duration_ms) / baseline.duration_ms) * 100
            },
            'memory_change': {
                'current': current.memory_mb,
                'baseline': baseline.memory_mb,
                'change_percent': ((current.memory_mb - baseline.memory_mb) / baseline.memory_mb) * 100
            },
            'throughput_change': {
                'current': current.throughput,
                'baseline': baseline.throughput,
                'change_percent': ((current.throughput - baseline.throughput) / baseline.throughput) * 100 if baseline.throughput > 0 else 0
            },
            'error_rate_change': {
                'current': current.error_rate,
                'baseline': baseline.error_rate,
                'change_percent': current.error_rate - baseline.error_rate
            }
        }
        
        return comparison
    
    def check_performance_thresholds(self, test_name: str) -> Dict[str, Any]:
        """检查性能阈值"""
        current_results = [r for r in self.results if r.test_name == test_name]
        if not current_results:
            return {'error': 'No results found'}
        
        current = current_results[-1]
        thresholds = self.config['performance_thresholds'].get(test_name, {})
        
        checks = {
            'test_name': test_name,
            'passed': True,
            'checks': []
        }
        
        # 检查持续时间
        if 'max_duration_ms' in thresholds:
            passed = current.duration_ms <= thresholds['max_duration_ms']
            checks['checks'].append({
                'metric': 'duration',
                'threshold': thresholds['max_duration_ms'],
                'actual': current.duration_ms,
                'passed': passed
            })
            if not passed:
                checks['passed'] = False
        
        # 检查内存使用
        if 'max_memory_mb' in thresholds:
            passed = current.memory_mb <= thresholds['max_memory_mb']
            checks['checks'].append({
                'metric': 'memory',
                'threshold': thresholds['max_memory_mb'],
                'actual': current.memory_mb,
                'passed': passed
            })
            if not passed:
                checks['passed'] = False
        
        # 检查吞吐量
        if 'min_throughput' in thresholds:
            passed = current.throughput >= thresholds['min_throughput']
            checks['checks'].append({
                'metric': 'throughput',
                'threshold': thresholds['min_throughput'],
                'actual': current.throughput,
                'passed': passed
            })
            if not passed:
                checks['passed'] = False
        
        return checks
    
    def generate_report(self) -> str:
        """生成性能报告"""
        if not self.results:
            return "无基准测试结果"
        
        report = f"""
# 正式验证框架性能基准测试报告

## 测试概览
- 测试时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
- 测试项目数: {len(self.results)}
- 总测试次数: {sum(r.metadata.get('iterations', 0) for r in self.results)}

## 详细结果

"""
        
        for result in self.results:
            report += f"""
### {result.test_name}
- **测试类型**: {result.test_type}
- **平均耗时**: {result.duration_ms:.2f} ms
- **平均内存**: {result.memory_mb:.2f} MB
- **平均CPU**: {result.cpu_percent:.2f}%
- **吞吐量**: {result.throughput:.2f} ops/s
- **错误率**: {result.error_rate:.2f}%
- **成功迭代**: {result.metadata.get('successful_iterations', 0)}
- **失败迭代**: {result.metadata.get('failed_iterations', 0)}

"""
        
        # 性能阈值检查
        report += "\n## 性能阈值检查\n\n"
        for result in self.results:
            checks = self.check_performance_thresholds(result.test_name)
            if 'error' not in checks:
                status = "✅ 通过" if checks['passed'] else "❌ 失败"
                report += f"### {result.test_name} - {status}\n"
                for check in checks['checks']:
                    status_icon = "✅" if check['passed'] else "❌"
                    report += f"- {status_icon} {check['metric']}: {check['actual']:.2f} (阈值: {check['threshold']})\n"
                report += "\n"
        
        return report
    
    def save_results(self, filepath: str = "benchmark-results.json"):
        """保存测试结果"""
        data = {
            'timestamp': datetime.now().isoformat(),
            'results': [asdict(result) for result in self.results],
            'summary': {
                'total_tests': len(self.results),
                'total_iterations': sum(r.metadata.get('iterations', 0) for r in self.results),
                'avg_duration': statistics.mean([r.duration_ms for r in self.results]) if self.results else 0,
                'avg_memory': statistics.mean([r.memory_mb for r in self.results]) if self.results else 0,
                'avg_throughput': statistics.mean([r.throughput for r in self.results]) if self.results else 0
            }
        }
        
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False, default=str)
        
        print(f"基准测试结果已保存到: {filepath}")


def main():
    """主函数 - 演示基准测试套件"""
    suite = BenchmarkSuite()
    
    print("=== 正式验证框架性能基准测试套件 ===")
    
    # 运行所有基准测试
    results = suite.run_all_benchmarks()
    
    # 生成报告
    report = suite.generate_report()
    print(report)
    
    # 保存结果
    suite.save_results()
    
    # 性能阈值检查
    print("\n=== 性能阈值检查 ===")
    for result in results:
        checks = suite.check_performance_thresholds(result.test_name)
        if 'error' not in checks:
            status = "通过" if checks['passed'] else "失败"
            print(f"{result.test_name}: {status}")


if __name__ == "__main__":
    main()
