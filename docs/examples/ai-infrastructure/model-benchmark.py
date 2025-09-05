#!/usr/bin/env python3
"""
TensorFlow Serving 模型性能基准测试脚本
用于验证AI模型服务的吞吐量、延迟和稳定性
"""

import requests
import time
import json
import threading
import statistics
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any
import argparse
import sys

class ModelBenchmark:
    def __init__(self, base_url: str, model_name: str):
        self.base_url = base_url
        self.model_name = model_name
        self.results = []
        self.lock = threading.Lock()
        
    def generate_test_data(self, batch_size: int = 1) -> Dict[str, Any]:
        """生成测试数据"""
        # 这里使用随机数据，实际使用时应该使用真实数据
        import numpy as np
        
        # 假设模型输入是图像数据 (224x224x3)
        input_data = np.random.rand(batch_size, 224, 224, 3).astype(np.float32)
        
        return {
            "instances": input_data.tolist()
        }
    
    def single_request(self, request_id: int) -> Dict[str, Any]:
        """执行单个推理请求"""
        start_time = time.time()
        
        try:
            # 准备请求数据
            test_data = self.generate_test_data()
            
            # 发送请求
            response = requests.post(
                f"{self.base_url}/v1/models/{self.model_name}:predict",
                json=test_data,
                timeout=30
            )
            
            end_time = time.time()
            duration = end_time - start_time
            
            result = {
                "request_id": request_id,
                "status_code": response.status_code,
                "duration": duration,
                "success": response.status_code == 200,
                "response_size": len(response.content) if response.content else 0,
                "timestamp": start_time
            }
            
            if response.status_code == 200:
                result["predictions"] = len(response.json().get("predictions", []))
            else:
                result["error"] = response.text
                
        except Exception as e:
            end_time = time.time()
            duration = end_time - start_time
            
            result = {
                "request_id": request_id,
                "status_code": 0,
                "duration": duration,
                "success": False,
                "error": str(e),
                "timestamp": start_time
            }
        
        # 线程安全地添加结果
        with self.lock:
            self.results.append(result)
            
        return result
    
    def run_concurrent_test(self, num_requests: int, max_workers: int = 10) -> Dict[str, Any]:
        """运行并发测试"""
        print(f"开始并发测试: {num_requests} 个请求, {max_workers} 个并发")
        
        start_time = time.time()
        
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = [executor.submit(self.single_request, i) for i in range(num_requests)]
            
            completed = 0
            for future in as_completed(futures):
                completed += 1
                if completed % 100 == 0:
                    print(f"已完成 {completed}/{num_requests} 个请求")
        
        end_time = time.time()
        total_duration = end_time - start_time
        
        return self.analyze_results(total_duration)
    
    def run_sustained_test(self, duration_seconds: int, requests_per_second: int) -> Dict[str, Any]:
        """运行持续负载测试"""
        print(f"开始持续测试: {duration_seconds} 秒, {requests_per_second} 请求/秒")
        
        start_time = time.time()
        request_count = 0
        
        while time.time() - start_time < duration_seconds:
            batch_start = time.time()
            
            # 发送一批请求
            with ThreadPoolExecutor(max_workers=requests_per_second) as executor:
                futures = [executor.submit(self.single_request, request_count + i) 
                          for i in range(requests_per_second)]
                
                for future in as_completed(futures):
                    request_count += 1
            
            # 控制请求频率
            batch_duration = time.time() - batch_start
            sleep_time = max(0, 1.0 - batch_duration)
            time.sleep(sleep_time)
        
        total_duration = time.time() - start_time
        return self.analyze_results(total_duration)
    
    def analyze_results(self, total_duration: float) -> Dict[str, Any]:
        """分析测试结果"""
        if not self.results:
            return {"error": "没有测试结果"}
        
        successful_requests = [r for r in self.results if r["success"]]
        failed_requests = [r for r in self.results if not r["success"]]
        
        if successful_requests:
            durations = [r["duration"] for r in successful_requests]
            response_sizes = [r["response_size"] for r in successful_requests]
        else:
            durations = []
            response_sizes = []
        
        analysis = {
            "total_requests": len(self.results),
            "successful_requests": len(successful_requests),
            "failed_requests": len(failed_requests),
            "success_rate": len(successful_requests) / len(self.results) * 100,
            "total_duration": total_duration,
            "requests_per_second": len(self.results) / total_duration,
            "throughput": len(successful_requests) / total_duration,
        }
        
        if durations:
            analysis.update({
                "avg_latency": statistics.mean(durations),
                "min_latency": min(durations),
                "max_latency": max(durations),
                "p50_latency": statistics.median(durations),
                "p95_latency": self.percentile(durations, 95),
                "p99_latency": self.percentile(durations, 99),
            })
        
        if response_sizes:
            analysis.update({
                "avg_response_size": statistics.mean(response_sizes),
                "total_data_transferred": sum(response_sizes),
            })
        
        # 错误分析
        if failed_requests:
            error_types = {}
            for req in failed_requests:
                error = req.get("error", "Unknown error")
                error_types[error] = error_types.get(error, 0) + 1
            analysis["error_breakdown"] = error_types
        
        return analysis
    
    def percentile(self, data: List[float], percentile: int) -> float:
        """计算百分位数"""
        sorted_data = sorted(data)
        index = int(len(sorted_data) * percentile / 100)
        return sorted_data[min(index, len(sorted_data) - 1)]
    
    def print_results(self, analysis: Dict[str, Any]):
        """打印测试结果"""
        print("\n" + "="*50)
        print("模型性能基准测试结果")
        print("="*50)
        
        print(f"总请求数: {analysis['total_requests']}")
        print(f"成功请求数: {analysis['successful_requests']}")
        print(f"失败请求数: {analysis['failed_requests']}")
        print(f"成功率: {analysis['success_rate']:.2f}%")
        print(f"总测试时间: {analysis['total_duration']:.2f} 秒")
        print(f"请求速率: {analysis['requests_per_second']:.2f} 请求/秒")
        print(f"吞吐量: {analysis['throughput']:.2f} 成功请求/秒")
        
        if 'avg_latency' in analysis:
            print(f"\n延迟统计:")
            print(f"  平均延迟: {analysis['avg_latency']*1000:.2f} ms")
            print(f"  最小延迟: {analysis['min_latency']*1000:.2f} ms")
            print(f"  最大延迟: {analysis['max_latency']*1000:.2f} ms")
            print(f"  P50延迟: {analysis['p50_latency']*1000:.2f} ms")
            print(f"  P95延迟: {analysis['p95_latency']*1000:.2f} ms")
            print(f"  P99延迟: {analysis['p99_latency']*1000:.2f} ms")
        
        if 'avg_response_size' in analysis:
            print(f"\n响应大小:")
            print(f"  平均响应大小: {analysis['avg_response_size']:.2f} bytes")
            print(f"  总数据传输: {analysis['total_data_transferred']:.2f} bytes")
        
        if 'error_breakdown' in analysis:
            print(f"\n错误分析:")
            for error, count in analysis['error_breakdown'].items():
                print(f"  {error}: {count} 次")

def main():
    parser = argparse.ArgumentParser(description='TensorFlow Serving 模型性能基准测试')
    parser.add_argument('--url', default='http://localhost:8501', 
                       help='TensorFlow Serving 服务地址')
    parser.add_argument('--model', default='my_model', 
                       help='模型名称')
    parser.add_argument('--requests', type=int, default=1000, 
                       help='并发请求数量')
    parser.add_argument('--workers', type=int, default=10, 
                       help='并发工作线程数')
    parser.add_argument('--duration', type=int, default=60, 
                       help='持续测试时间(秒)')
    parser.add_argument('--rps', type=int, default=10, 
                       help='持续测试请求速率(请求/秒)')
    parser.add_argument('--test-type', choices=['concurrent', 'sustained'], 
                       default='concurrent', help='测试类型')
    
    args = parser.parse_args()
    
    # 创建基准测试实例
    benchmark = ModelBenchmark(args.url, args.model)
    
    try:
        if args.test_type == 'concurrent':
            # 并发测试
            analysis = benchmark.run_concurrent_test(args.requests, args.workers)
        else:
            # 持续测试
            analysis = benchmark.run_sustained_test(args.duration, args.rps)
        
        # 打印结果
        benchmark.print_results(analysis)
        
        # 保存结果到文件
        with open('benchmark_results.json', 'w') as f:
            json.dump(analysis, f, indent=2)
        
        print(f"\n详细结果已保存到 benchmark_results.json")
        
    except KeyboardInterrupt:
        print("\n测试被用户中断")
        sys.exit(1)
    except Exception as e:
        print(f"\n测试过程中发生错误: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
