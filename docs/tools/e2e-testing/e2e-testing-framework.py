#!/usr/bin/env python3
"""
端到端集成测试框架
提供系统级验证、跨组件测试和性能压力测试
"""

import json
import time
import threading
import concurrent.futures
from typing import Dict, List, Any, Optional, Callable, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
import requests
import subprocess
import psutil
import logging
from datetime import datetime, timedelta


class TestType(Enum):
    """测试类型"""
    UNIT = "unit"
    INTEGRATION = "integration"
    SYSTEM = "system"
    PERFORMANCE = "performance"
    STRESS = "stress"
    LOAD = "load"
    SECURITY = "security"
    COMPATIBILITY = "compatibility"


class TestStatus(Enum):
    """测试状态"""
    PENDING = "pending"
    RUNNING = "running"
    PASSED = "passed"
    FAILED = "failed"
    SKIPPED = "skipped"
    ERROR = "error"


@dataclass
class TestCase:
    """测试用例"""
    test_id: str
    name: str
    description: str
    test_type: TestType
    component: str
    priority: int  # 1-5, 5最高
    timeout: int  # 秒
    dependencies: List[str]
    setup_script: Optional[str]
    teardown_script: Optional[str]
    expected_result: Any
    metadata: Dict[str, Any]


@dataclass
class TestResult:
    """测试结果"""
    test_id: str
    status: TestStatus
    start_time: datetime
    end_time: Optional[datetime]
    duration: float
    output: str
    error_message: Optional[str]
    metrics: Dict[str, Any]
    artifacts: List[str]


@dataclass
class TestSuite:
    """测试套件"""
    suite_id: str
    name: str
    description: str
    test_cases: List[TestCase]
    parallel_execution: bool
    max_parallel_tests: int
    timeout: int
    retry_count: int


class E2ETestingFramework:
    """端到端测试框架"""
    
    def __init__(self, config_path: str = "e2e-testing-config.json"):
        self.config = self.load_config(config_path)
        self.test_suites: Dict[str, TestSuite] = {}
        self.test_results: Dict[str, TestResult] = {}
        self.running_tests: Dict[str, threading.Thread] = {}
        self.system_metrics: Dict[str, Any] = {}
        
        # 设置日志
        self._setup_logging()
        
        # 初始化测试环境
        self._initialize_test_environment()
    
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
            "test_environment": {
                "base_url": "http://localhost:8080",
                "api_endpoint": "/api/v1",
                "timeout": 30,
                "retry_count": 3
            },
            "components": {
                "verification_engine": {
                    "endpoint": "/verify",
                    "health_check": "/health",
                    "expected_response_time": 5.0
                },
                "model_checker": {
                    "endpoint": "/check",
                    "health_check": "/health",
                    "expected_response_time": 10.0
                },
                "constraint_solver": {
                    "endpoint": "/solve",
                    "health_check": "/health",
                    "expected_response_time": 15.0
                },
                "visualization_service": {
                    "endpoint": "/visualize",
                    "health_check": "/health",
                    "expected_response_time": 3.0
                }
            },
            "test_data": {
                "models": [
                    "simple_state_machine.json",
                    "complex_system.json",
                    "concurrent_model.json"
                ],
                "constraints": [
                    "basic_constraints.json",
                    "complex_constraints.json",
                    "performance_constraints.json"
                ]
            },
            "performance_thresholds": {
                "response_time": 5.0,
                "memory_usage": 512,  # MB
                "cpu_usage": 80,  # %
                "throughput": 100  # requests/second
            },
            "reporting": {
                "output_format": "html",
                "include_metrics": True,
                "include_artifacts": True,
                "save_screenshots": True
            }
        }
    
    def _setup_logging(self):
        """设置日志"""
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
            handlers=[
                logging.FileHandler('e2e-testing.log'),
                logging.StreamHandler()
            ]
        )
        self.logger = logging.getLogger(__name__)
    
    def _initialize_test_environment(self):
        """初始化测试环境"""
        self.logger.info("初始化测试环境...")
        
        # 检查系统资源
        self._check_system_resources()
        
        # 启动测试服务
        self._start_test_services()
        
        # 等待服务就绪
        self._wait_for_services()
        
        self.logger.info("测试环境初始化完成")
    
    def _check_system_resources(self):
        """检查系统资源"""
        # 检查内存
        memory = psutil.virtual_memory()
        if memory.available < 1024 * 1024 * 1024:  # 1GB
            self.logger.warning(f"可用内存不足: {memory.available / 1024 / 1024:.1f}MB")
        
        # 检查磁盘空间
        disk = psutil.disk_usage('/')
        if disk.free < 5 * 1024 * 1024 * 1024:  # 5GB
            self.logger.warning(f"可用磁盘空间不足: {disk.free / 1024 / 1024 / 1024:.1f}GB")
        
        # 检查CPU
        cpu_count = psutil.cpu_count()
        if cpu_count < 2:
            self.logger.warning(f"CPU核心数不足: {cpu_count}")
    
    def _start_test_services(self):
        """启动测试服务"""
        self.logger.info("启动测试服务...")
        
        # 这里应该启动实际的测试服务
        # 为了演示，我们模拟服务启动
        services = [
            "verification_engine",
            "model_checker", 
            "constraint_solver",
            "visualization_service"
        ]
        
        for service in services:
            self.logger.info(f"启动服务: {service}")
            # 实际实现中，这里会启动Docker容器或本地服务
            time.sleep(0.5)  # 模拟启动时间
    
    def _wait_for_services(self):
        """等待服务就绪"""
        self.logger.info("等待服务就绪...")
        
        base_url = self.config["test_environment"]["base_url"]
        timeout = self.config["test_environment"]["timeout"]
        
        for component, config in self.config["components"].items():
            health_url = f"{base_url}{config['health_check']}"
            
            for attempt in range(timeout):
                try:
                    response = requests.get(health_url, timeout=5)
                    if response.status_code == 200:
                        self.logger.info(f"服务 {component} 已就绪")
                        break
                except requests.RequestException:
                    pass
                
                if attempt < timeout - 1:
                    time.sleep(1)
            else:
                self.logger.error(f"服务 {component} 启动超时")
                raise Exception(f"服务 {component} 启动失败")
    
    def create_test_suite(self, suite_id: str, name: str, description: str,
                         parallel_execution: bool = True, max_parallel_tests: int = 5) -> TestSuite:
        """创建测试套件"""
        suite = TestSuite(
            suite_id=suite_id,
            name=name,
            description=description,
            test_cases=[],
            parallel_execution=parallel_execution,
            max_parallel_tests=max_parallel_tests,
            timeout=300,  # 5分钟
            retry_count=3
        )
        
        self.test_suites[suite_id] = suite
        self.logger.info(f"创建测试套件: {name}")
        
        return suite
    
    def add_test_case(self, suite_id: str, test_case: TestCase):
        """添加测试用例"""
        if suite_id not in self.test_suites:
            raise ValueError(f"测试套件 {suite_id} 不存在")
        
        self.test_suites[suite_id].test_cases.append(test_case)
        self.logger.info(f"添加测试用例: {test_case.name}")
    
    def create_verification_test_cases(self) -> List[TestCase]:
        """创建验证测试用例"""
        test_cases = []
        
        # 基础验证测试
        test_cases.append(TestCase(
            test_id="verify_basic_model",
            name="基础模型验证",
            description="验证简单状态机模型",
            test_type=TestType.INTEGRATION,
            component="verification_engine",
            priority=5,
            timeout=30,
            dependencies=[],
            setup_script=None,
            teardown_script=None,
            expected_result={"status": "verified", "errors": []},
            metadata={"model_file": "simple_state_machine.json"}
        ))
        
        # 复杂模型验证测试
        test_cases.append(TestCase(
            test_id="verify_complex_model",
            name="复杂模型验证",
            description="验证复杂系统模型",
            test_type=TestType.SYSTEM,
            component="verification_engine",
            priority=4,
            timeout=60,
            dependencies=["verify_basic_model"],
            setup_script=None,
            teardown_script=None,
            expected_result={"status": "verified", "errors": []},
            metadata={"model_file": "complex_system.json"}
        ))
        
        # 并发模型验证测试
        test_cases.append(TestCase(
            test_id="verify_concurrent_model",
            name="并发模型验证",
            description="验证并发系统模型",
            test_type=TestType.SYSTEM,
            component="verification_engine",
            priority=4,
            timeout=90,
            dependencies=["verify_basic_model"],
            setup_script=None,
            teardown_script=None,
            expected_result={"status": "verified", "errors": []},
            metadata={"model_file": "concurrent_model.json"}
        ))
        
        return test_cases
    
    def create_performance_test_cases(self) -> List[TestCase]:
        """创建性能测试用例"""
        test_cases = []
        
        # 响应时间测试
        test_cases.append(TestCase(
            test_id="perf_response_time",
            name="响应时间测试",
            description="测试API响应时间",
            test_type=TestType.PERFORMANCE,
            component="verification_engine",
            priority=3,
            timeout=120,
            dependencies=[],
            setup_script=None,
            teardown_script=None,
            expected_result={"max_response_time": 5.0},
            metadata={"requests_count": 100, "concurrent_users": 10}
        ))
        
        # 吞吐量测试
        test_cases.append(TestCase(
            test_id="perf_throughput",
            name="吞吐量测试",
            description="测试系统吞吐量",
            test_type=TestType.LOAD,
            component="verification_engine",
            priority=3,
            timeout=180,
            dependencies=[],
            setup_script=None,
            teardown_script=None,
            expected_result={"min_throughput": 100},
            metadata={"duration": 60, "concurrent_users": 50}
        ))
        
        # 内存使用测试
        test_cases.append(TestCase(
            test_id="perf_memory_usage",
            name="内存使用测试",
            description="测试内存使用情况",
            test_type=TestType.PERFORMANCE,
            component="verification_engine",
            priority=2,
            timeout=300,
            dependencies=[],
            setup_script=None,
            teardown_script=None,
            expected_result={"max_memory_usage": 512},
            metadata={"monitoring_duration": 300}
        ))
        
        return test_cases
    
    def create_security_test_cases(self) -> List[TestCase]:
        """创建安全测试用例"""
        test_cases = []
        
        # 输入验证测试
        test_cases.append(TestCase(
            test_id="security_input_validation",
            name="输入验证测试",
            description="测试恶意输入处理",
            test_type=TestType.SECURITY,
            component="verification_engine",
            priority=5,
            timeout=60,
            dependencies=[],
            setup_script=None,
            teardown_script=None,
            expected_result={"status": "secure", "vulnerabilities": []},
            metadata={"malicious_inputs": ["sql_injection", "xss", "path_traversal"]}
        ))
        
        # 认证测试
        test_cases.append(TestCase(
            test_id="security_authentication",
            name="认证测试",
            description="测试用户认证机制",
            test_type=TestType.SECURITY,
            component="verification_engine",
            priority=5,
            timeout=30,
            dependencies=[],
            setup_script=None,
            teardown_script=None,
            expected_result={"status": "authenticated"},
            metadata={"test_users": ["valid_user", "invalid_user", "admin_user"]}
        ))
        
        return test_cases
    
    def run_test_case(self, test_case: TestCase) -> TestResult:
        """运行单个测试用例"""
        self.logger.info(f"开始运行测试: {test_case.name}")
        
        start_time = datetime.now()
        result = TestResult(
            test_id=test_case.test_id,
            status=TestStatus.RUNNING,
            start_time=start_time,
            end_time=None,
            duration=0.0,
            output="",
            error_message=None,
            metrics={},
            artifacts=[]
        )
        
        try:
            # 执行前置脚本
            if test_case.setup_script:
                self._execute_script(test_case.setup_script)
            
            # 运行测试
            if test_case.test_type == TestType.INTEGRATION:
                result = self._run_integration_test(test_case, result)
            elif test_case.test_type == TestType.SYSTEM:
                result = self._run_system_test(test_case, result)
            elif test_case.test_type == TestType.PERFORMANCE:
                result = self._run_performance_test(test_case, result)
            elif test_case.test_type == TestType.SECURITY:
                result = self._run_security_test(test_case, result)
            else:
                result = self._run_generic_test(test_case, result)
            
            # 执行后置脚本
            if test_case.teardown_script:
                self._execute_script(test_case.teardown_script)
            
        except Exception as e:
            result.status = TestStatus.ERROR
            result.error_message = str(e)
            self.logger.error(f"测试 {test_case.name} 执行失败: {str(e)}")
        
        finally:
            result.end_time = datetime.now()
            result.duration = (result.end_time - result.start_time).total_seconds()
            self.test_results[test_case.test_id] = result
        
        return result
    
    def _run_integration_test(self, test_case: TestCase, result: TestResult) -> TestResult:
        """运行集成测试"""
        base_url = self.config["test_environment"]["base_url"]
        component_config = self.config["components"][test_case.component]
        endpoint = f"{base_url}{component_config['endpoint']}"
        
        # 加载测试数据
        model_file = test_case.metadata.get("model_file")
        if model_file:
            with open(f"test_data/{model_file}", 'r') as f:
                test_data = json.load(f)
        else:
            test_data = {"model": "test_model"}
        
        # 发送请求
        start_time = time.time()
        response = requests.post(endpoint, json=test_data, timeout=test_case.timeout)
        response_time = time.time() - start_time
        
        # 记录指标
        result.metrics = {
            "response_time": response_time,
            "status_code": response.status_code,
            "response_size": len(response.content)
        }
        
        # 验证结果
        if response.status_code == 200:
            response_data = response.json()
            if self._validate_test_result(response_data, test_case.expected_result):
                result.status = TestStatus.PASSED
                result.output = f"测试通过: {response_data}"
            else:
                result.status = TestStatus.FAILED
                result.output = f"测试失败: 期望 {test_case.expected_result}, 实际 {response_data}"
        else:
            result.status = TestStatus.FAILED
            result.output = f"HTTP错误: {response.status_code} - {response.text}"
        
        return result
    
    def _run_system_test(self, test_case: TestCase, result: TestResult) -> TestResult:
        """运行系统测试"""
        # 系统测试通常涉及多个组件的交互
        # 这里简化为调用多个API端点
        
        base_url = self.config["test_environment"]["base_url"]
        components = ["verification_engine", "model_checker", "constraint_solver"]
        
        results = []
        for component in components:
            component_config = self.config["components"][component]
            endpoint = f"{base_url}{component_config['endpoint']}"
            
            try:
                response = requests.get(f"{base_url}{component_config['health_check']}", timeout=10)
                if response.status_code == 200:
                    results.append(f"{component}: OK")
                else:
                    results.append(f"{component}: FAILED")
            except Exception as e:
                results.append(f"{component}: ERROR - {str(e)}")
        
        result.output = "\n".join(results)
        
        if all("OK" in r for r in results):
            result.status = TestStatus.PASSED
        else:
            result.status = TestStatus.FAILED
        
        return result
    
    def _run_performance_test(self, test_case: TestCase, result: TestResult) -> TestResult:
        """运行性能测试"""
        base_url = self.config["test_environment"]["base_url"]
        component_config = self.config["components"][test_case.component]
        endpoint = f"{base_url}{component_config['endpoint']}"
        
        # 获取性能测试参数
        requests_count = test_case.metadata.get("requests_count", 100)
        concurrent_users = test_case.metadata.get("concurrent_users", 10)
        
        # 执行性能测试
        start_time = time.time()
        response_times = []
        
        def make_request():
            req_start = time.time()
            try:
                response = requests.get(endpoint, timeout=30)
                req_time = time.time() - req_start
                return req_time, response.status_code
            except Exception as e:
                return time.time() - req_start, 0
        
        # 并发执行请求
        with concurrent.futures.ThreadPoolExecutor(max_workers=concurrent_users) as executor:
            futures = [executor.submit(make_request) for _ in range(requests_count)]
            
            for future in concurrent.futures.as_completed(futures):
                response_time, status_code = future.result()
                response_times.append(response_time)
        
        total_time = time.time() - start_time
        
        # 计算性能指标
        avg_response_time = sum(response_times) / len(response_times)
        max_response_time = max(response_times)
        min_response_time = min(response_times)
        throughput = requests_count / total_time
        
        result.metrics = {
            "avg_response_time": avg_response_time,
            "max_response_time": max_response_time,
            "min_response_time": min_response_time,
            "throughput": throughput,
            "total_requests": requests_count,
            "successful_requests": len([r for r in response_times if r > 0])
        }
        
        # 验证性能阈值
        thresholds = self.config["performance_thresholds"]
        if (avg_response_time <= thresholds["response_time"] and 
            throughput >= thresholds["throughput"]):
            result.status = TestStatus.PASSED
            result.output = f"性能测试通过: 平均响应时间 {avg_response_time:.2f}s, 吞吐量 {throughput:.2f} req/s"
        else:
            result.status = TestStatus.FAILED
            result.output = f"性能测试失败: 平均响应时间 {avg_response_time:.2f}s, 吞吐量 {throughput:.2f} req/s"
        
        return result
    
    def _run_security_test(self, test_case: TestCase, result: TestResult) -> TestResult:
        """运行安全测试"""
        base_url = self.config["test_environment"]["base_url"]
        component_config = self.config["components"][test_case.component]
        endpoint = f"{base_url}{component_config['endpoint']}"
        
        # 获取恶意输入
        malicious_inputs = test_case.metadata.get("malicious_inputs", [])
        
        vulnerabilities = []
        
        for malicious_input in malicious_inputs:
            try:
                # 构造恶意请求
                if malicious_input == "sql_injection":
                    payload = {"query": "'; DROP TABLE users; --"}
                elif malicious_input == "xss":
                    payload = {"input": "<script>alert('XSS')</script>"}
                elif malicious_input == "path_traversal":
                    payload = {"file": "../../../etc/passwd"}
                else:
                    payload = {"input": malicious_input}
                
                response = requests.post(endpoint, json=payload, timeout=10)
                
                # 检查是否检测到攻击
                if response.status_code == 400 or "error" in response.text.lower():
                    # 系统正确拒绝了恶意输入
                    continue
                else:
                    vulnerabilities.append(f"未检测到 {malicious_input} 攻击")
                    
            except Exception as e:
                vulnerabilities.append(f"测试 {malicious_input} 时出错: {str(e)}")
        
        result.metrics = {
            "vulnerabilities_found": len(vulnerabilities),
            "tests_performed": len(malicious_inputs)
        }
        
        if not vulnerabilities:
            result.status = TestStatus.PASSED
            result.output = "安全测试通过: 未发现漏洞"
        else:
            result.status = TestStatus.FAILED
            result.output = f"安全测试失败: 发现 {len(vulnerabilities)} 个潜在漏洞"
        
        return result
    
    def _run_generic_test(self, test_case: TestCase, result: TestResult) -> TestResult:
        """运行通用测试"""
        # 默认的健康检查测试
        base_url = self.config["test_environment"]["base_url"]
        component_config = self.config["components"][test_case.component]
        health_url = f"{base_url}{component_config['health_check']}"
        
        try:
            response = requests.get(health_url, timeout=10)
            if response.status_code == 200:
                result.status = TestStatus.PASSED
                result.output = f"健康检查通过: {response.json()}"
            else:
                result.status = TestStatus.FAILED
                result.output = f"健康检查失败: {response.status_code}"
        except Exception as e:
            result.status = TestStatus.ERROR
            result.error_message = str(e)
        
        return result
    
    def _validate_test_result(self, actual: Any, expected: Any) -> bool:
        """验证测试结果"""
        if isinstance(expected, dict):
            if not isinstance(actual, dict):
                return False
            
            for key, expected_value in expected.items():
                if key not in actual:
                    return False
                
                if not self._validate_test_result(actual[key], expected_value):
                    return False
            
            return True
        else:
            return actual == expected
    
    def _execute_script(self, script_path: str):
        """执行脚本"""
        try:
            result = subprocess.run(script_path, shell=True, capture_output=True, text=True, timeout=30)
            if result.returncode != 0:
                self.logger.warning(f"脚本 {script_path} 执行失败: {result.stderr}")
        except Exception as e:
            self.logger.error(f"执行脚本 {script_path} 时出错: {str(e)}")
    
    def run_test_suite(self, suite_id: str) -> Dict[str, TestResult]:
        """运行测试套件"""
        if suite_id not in self.test_suites:
            raise ValueError(f"测试套件 {suite_id} 不存在")
        
        suite = self.test_suites[suite_id]
        self.logger.info(f"开始运行测试套件: {suite.name}")
        
        # 按优先级排序测试用例
        test_cases = sorted(suite.test_cases, key=lambda x: x.priority, reverse=True)
        
        if suite.parallel_execution:
            return self._run_parallel_tests(suite, test_cases)
        else:
            return self._run_sequential_tests(suite, test_cases)
    
    def _run_parallel_tests(self, suite: TestSuite, test_cases: List[TestCase]) -> Dict[str, TestResult]:
        """并行运行测试"""
        results = {}
        max_workers = min(suite.max_parallel_tests, len(test_cases))
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
            # 提交所有测试任务
            future_to_test = {
                executor.submit(self.run_test_case, test_case): test_case
                for test_case in test_cases
            }
            
            # 收集结果
            for future in concurrent.futures.as_completed(future_to_test):
                test_case = future_to_test[future]
                try:
                    result = future.result()
                    results[test_case.test_id] = result
                except Exception as e:
                    self.logger.error(f"测试 {test_case.name} 执行异常: {str(e)}")
        
        return results
    
    def _run_sequential_tests(self, suite: TestSuite, test_cases: List[TestCase]) -> Dict[str, TestResult]:
        """顺序运行测试"""
        results = {}
        
        for test_case in test_cases:
            # 检查依赖
            if not self._check_dependencies(test_case, results):
                self.logger.warning(f"跳过测试 {test_case.name}: 依赖未满足")
                continue
            
            result = self.run_test_case(test_case)
            results[test_case.test_id] = result
        
        return results
    
    def _check_dependencies(self, test_case: TestCase, results: Dict[str, TestResult]) -> bool:
        """检查测试依赖"""
        for dep_id in test_case.dependencies:
            if dep_id not in results:
                return False
            
            if results[dep_id].status != TestStatus.PASSED:
                return False
        
        return True
    
    def generate_test_report(self, suite_id: str) -> str:
        """生成测试报告"""
        if suite_id not in self.test_suites:
            raise ValueError(f"测试套件 {suite_id} 不存在")
        
        suite = self.test_suites[suite_id]
        results = {tid: self.test_results[tid] for tid in self.test_results.keys() 
                  if any(tc.test_id == tid for tc in suite.test_cases)}
        
        # 统计结果
        total_tests = len(results)
        passed_tests = sum(1 for r in results.values() if r.status == TestStatus.PASSED)
        failed_tests = sum(1 for r in results.values() if r.status == TestStatus.FAILED)
        error_tests = sum(1 for r in results.values() if r.status == TestStatus.ERROR)
        
        success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0
        
        report = f"""
# 端到端测试报告

## 测试套件信息
- **名称**: {suite.name}
- **描述**: {suite.description}
- **执行时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 测试统计
- **总测试数**: {total_tests}
- **通过测试**: {passed_tests}
- **失败测试**: {failed_tests}
- **错误测试**: {error_tests}
- **成功率**: {success_rate:.1f}%

## 详细结果

"""
        
        for test_case in suite.test_cases:
            if test_case.test_id in results:
                result = results[test_case.test_id]
                status_icon = "✅" if result.status == TestStatus.PASSED else "❌" if result.status == TestStatus.FAILED else "⚠️"
                
                report += f"""
### {status_icon} {test_case.name}
- **状态**: {result.status.value}
- **持续时间**: {result.duration:.2f}秒
- **输出**: {result.output}
"""
                
                if result.error_message:
                    report += f"- **错误信息**: {result.error_message}\n"
                
                if result.metrics:
                    report += f"- **指标**: {result.metrics}\n"
        
        return report
    
    def save_test_results(self, suite_id: str, filepath: str = None):
        """保存测试结果"""
        if filepath is None:
            filepath = f"test-results-{suite_id}-{datetime.now().strftime('%Y%m%d-%H%M%S')}.json"
        
        suite = self.test_suites[suite_id]
        results = {tid: self.test_results[tid] for tid in self.test_results.keys() 
                  if any(tc.test_id == tid for tc in suite.test_cases)}
        
        data = {
            "suite_info": asdict(suite),
            "results": {tid: asdict(result) for tid, result in results.items()},
            "timestamp": datetime.now().isoformat()
        }
        
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False, default=str)
        
        self.logger.info(f"测试结果已保存到: {filepath}")


def main():
    """主函数 - 演示端到端测试框架"""
    framework = E2ETestingFramework()
    
    print("=== 端到端集成测试框架演示 ===")
    
    # 创建测试套件
    suite = framework.create_test_suite(
        "e2e_suite",
        "端到端测试套件",
        "完整的端到端系统测试",
        parallel_execution=True,
        max_parallel_tests=3
    )
    
    # 添加测试用例
    verification_tests = framework.create_verification_test_cases()
    performance_tests = framework.create_performance_test_cases()
    security_tests = framework.create_security_test_cases()
    
    for test in verification_tests + performance_tests + security_tests:
        framework.add_test_case("e2e_suite", test)
    
    print(f"创建了 {len(suite.test_cases)} 个测试用例")
    
    # 运行测试套件
    print("\n开始运行测试套件...")
    results = framework.run_test_suite("e2e_suite")
    
    # 生成报告
    report = framework.generate_test_report("e2e_suite")
    print(report)
    
    # 保存结果
    framework.save_test_results("e2e_suite")
    
    # 显示统计信息
    total_tests = len(results)
    passed_tests = sum(1 for r in results.values() if r.status.value == "passed")
    success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0
    
    print(f"\n=== 测试完成 ===")
    print(f"总测试数: {total_tests}")
    print(f"通过测试: {passed_tests}")
    print(f"成功率: {success_rate:.1f}%")


if __name__ == "__main__":
    main()
