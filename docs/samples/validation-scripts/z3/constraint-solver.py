#!/usr/bin/env python3
"""
Z3 约束求解器
用于验证形式化框架中的约束一致性和属性完整性
"""

from z3 import *
import json
import argparse
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
import time

@dataclass
class ValidationResult:
    """验证结果数据类"""
    success: bool
    message: str
    counter_examples: List[Dict[str, Any]]
    execution_time: float
    constraints_checked: int
    violations_found: int

class ConstraintSolver:
    """约束求解器主类"""
    
    def __init__(self):
        self.solver = Solver()
        self.variables = {}
        self.constraints = []
        self.results = []
        
    def add_variable(self, name: str, var_type: str, domain: Optional[List] = None):
        """添加变量到求解器"""
        if var_type == "int":
            if domain:
                var = Int(name)
                # 添加域约束
                self.solver.add(Or([var == val for val in domain]))
            else:
                var = Int(name)
        elif var_type == "bool":
            var = Bool(name)
        elif var_type == "string":
            # 字符串用整数表示
            var = Int(name)
        else:
            raise ValueError(f"Unsupported variable type: {var_type}")
            
        self.variables[name] = var
        return var
    
    def add_constraint(self, constraint_expr: str, description: str = ""):
        """添加约束表达式"""
        try:
            # 解析约束表达式
            constraint = eval(constraint_expr, {"__builtins__": {}}, self.variables)
            self.solver.add(constraint)
            self.constraints.append({
                "expression": constraint_expr,
                "description": description,
                "z3_constraint": constraint
            })
        except Exception as e:
            raise ValueError(f"Invalid constraint expression '{constraint_expr}': {e}")
    
    def check_consistency(self) -> ValidationResult:
        """检查约束一致性"""
        start_time = time.time()
        
        # 检查可满足性
        result = self.solver.check()
        
        execution_time = time.time() - start_time
        constraints_checked = len(self.constraints)
        
        if result == sat:
            # 获取模型
            model = self.solver.model()
            counter_examples = []
            
            # 提取变量值作为反例
            for name, var in self.variables.items():
                try:
                    value = model[var]
                    if value is not None:
                        counter_examples.append({
                            "variable": name,
                            "value": str(value),
                            "type": str(type(value))
                        })
                except:
                    pass
            
            return ValidationResult(
                success=True,
                message="约束系统一致，存在满足解",
                counter_examples=counter_examples,
                execution_time=execution_time,
                constraints_checked=constraints_checked,
                violations_found=0
            )
        else:
            # 约束不可满足，尝试找出冲突的约束
            conflicts = self._find_conflicting_constraints()
            
            return ValidationResult(
                success=False,
                message="约束系统不一致，存在冲突",
                counter_examples=conflicts,
                execution_time=execution_time,
                constraints_checked=constraints_checked,
                violations_found=len(conflicts)
            )
    
    def _find_conflicting_constraints(self) -> List[Dict[str, Any]]:
        """找出冲突的约束"""
        conflicts = []
        
        for i, constraint_info in enumerate(self.constraints):
            # 临时移除一个约束
            temp_solver = Solver()
            for j, other_constraint in enumerate(self.constraints):
                if i != j:
                    temp_solver.add(other_constraint["z3_constraint"])
            
            if temp_solver.check() == sat:
                conflicts.append({
                    "constraint_index": i,
                    "constraint": constraint_info["expression"],
                    "description": constraint_info["description"],
                    "reason": "与其他约束冲突"
                })
        
        return conflicts
    
    def validate_property(self, property_expr: str, description: str = "") -> ValidationResult:
        """验证属性是否被所有约束满足"""
        start_time = time.time()
        
        # 添加属性否定到求解器
        property_constraint = eval(property_expr, {"__builtins__": {}}, self.variables)
        self.solver.push()
        self.solver.add(Not(property_constraint))
        
        result = self.solver.check()
        execution_time = time.time() - start_time
        
        if result == sat:
            # 属性被违反，获取反例
            model = self.solver.model()
            counter_examples = []
            
            for name, var in self.variables.items():
                try:
                    value = model[var]
                    if value is not None:
                        counter_examples.append({
                            "variable": name,
                            "value": str(value),
                            "type": str(type(value))
                        })
                except:
                    pass
            
            self.solver.pop()
            
            return ValidationResult(
                success=False,
                message=f"属性 '{description}' 被违反",
                counter_examples=counter_examples,
                execution_time=execution_time,
                constraints_checked=len(self.constraints),
                violations_found=1
            )
        else:
            # 属性被满足
            self.solver.pop()
            
            return ValidationResult(
                success=True,
                message=f"属性 '{description}' 被满足",
                counter_examples=[],
                execution_time=execution_time,
                constraints_checked=len(self.constraints),
                violations_found=0
            )

class DataModelValidator(ConstraintSolver):
    """数据模型约束验证器"""
    
    def __init__(self):
        super().__init__()
        self._setup_data_model_variables()
    
    def _setup_data_model_variables(self):
        """设置数据模型相关变量"""
        # 实体相关变量
        self.add_variable("entity_count", "int", list(range(1, 101)))
        self.add_variable("field_count", "int", list(range(1, 51)))
        self.add_variable("relation_count", "int", list(range(0, 101)))
        
        # 字段相关变量
        self.add_variable("primary_key_count", "int", list(range(1, 6)))
        self.add_variable("foreign_key_count", "int", list(range(0, 21)))
        self.add_variable("unique_constraint_count", "int", list(range(0, 21)))
        
        # 索引相关变量
        self.add_variable("index_count", "int", list(range(0, 51)))
        self.add_variable("unique_index_count", "int", list(range(0, 21)))
        
        # 约束相关变量
        self.add_variable("check_constraint_count", "int", list(range(0, 21)))
        self.add_variable("not_null_constraint_count", "int", list(range(0, 51)))
    
    def validate_data_model_constraints(self) -> ValidationResult:
        """验证数据模型约束"""
        # 基本约束
        self.add_constraint("entity_count >= 1", "至少有一个实体")
        self.add_constraint("field_count >= 1", "至少有一个字段")
        self.add_constraint("primary_key_count >= 1", "至少有一个主键")
        
        # 关系约束
        self.add_constraint("primary_key_count <= field_count", "主键数量不能超过字段数量")
        self.add_constraint("foreign_key_count <= relation_count", "外键数量不能超过关系数量")
        self.add_constraint("unique_constraint_count <= field_count", "唯一约束数量不能超过字段数量")
        
        # 索引约束
        self.add_constraint("index_count <= field_count", "索引数量不能超过字段数量")
        self.add_constraint("unique_index_count <= unique_constraint_count", "唯一索引数量不能超过唯一约束数量")
        
        # 约束完整性
        self.add_constraint("check_constraint_count <= field_count", "检查约束数量不能超过字段数量")
        self.add_constraint("not_null_constraint_count <= field_count", "非空约束数量不能超过字段数量")
        
        # 业务规则约束
        self.add_constraint("entity_count * 2 >= field_count", "字段数量与实体数量比例合理")
        self.add_constraint("relation_count <= entity_count * (entity_count - 1)", "关系数量不能超过实体间可能的最大关系数")
        
        return self.check_consistency()
    
    def validate_data_integrity_properties(self) -> List[ValidationResult]:
        """验证数据完整性属性"""
        properties = [
            ("primary_key_count == 1", "每个实体只有一个主键"),
            ("foreign_key_count <= primary_key_count * relation_count", "外键数量约束"),
            ("unique_constraint_count >= primary_key_count", "唯一约束包含主键"),
            ("index_count >= primary_key_count", "主键必须有索引"),
        ]
        
        results = []
        for prop_expr, description in properties:
            result = self.validate_property(prop_expr, description)
            results.append(result)
        
        return results

class InteractionModelValidator(ConstraintSolver):
    """交互模型约束验证器"""
    
    def __init__(self):
        super().__init__()
        self._setup_interaction_model_variables()
    
    def _setup_interaction_model_variables(self):
        """设置交互模型相关变量"""
        # 端点相关变量
        self.add_variable("endpoint_count", "int", list(range(1, 101)))
        self.add_variable("http_method_count", "int", list(range(1, 9)))
        self.add_variable("api_version_count", "int", list(range(1, 11)))
        
        # 资源相关变量
        self.add_variable("resource_count", "int", list(range(1, 51)))
        self.add_variable("operation_count", "int", list(range(1, 101)))
        
        # 安全相关变量
        self.add_variable("auth_required_count", "int", list(range(0, 101)))
        self.add_variable("rate_limit_count", "int", list(range(0, 101)))
        self.add_variable("timeout_count", "int", list(range(0, 101)))
        
        # 性能相关变量
        self.add_variable("cache_enabled_count", "int", list(range(0, 101)))
        self.add_variable("compression_enabled_count", "int", list(range(0, 101)))
    
    def validate_interaction_model_constraints(self) -> ValidationResult:
        """验证交互模型约束"""
        # 基本约束
        self.add_constraint("endpoint_count >= 1", "至少有一个端点")
        self.add_constraint("resource_count >= 1", "至少有一个资源")
        self.add_constraint("operation_count >= 1", "至少有一个操作")
        
        # HTTP方法约束
        self.add_constraint("http_method_count <= 8", "HTTP方法数量不超过8个")
        self.add_constraint("endpoint_count >= http_method_count", "端点数量不少于HTTP方法数量")
        
        # 版本约束
        self.add_constraint("api_version_count >= 1", "至少有一个API版本")
        self.add_constraint("api_version_count <= endpoint_count", "版本数量不超过端点数量")
        
        # 操作约束
        self.add_constraint("operation_count >= resource_count", "操作数量不少于资源数量")
        self.add_constraint("operation_count <= resource_count * 10", "操作数量与资源数量比例合理")
        
        # 安全约束
        self.add_constraint("auth_required_count <= endpoint_count", "需要认证的端点数量不超过总端点数量")
        self.add_constraint("rate_limit_count <= endpoint_count", "限流端点数量不超过总端点数量")
        self.add_constraint("timeout_count <= endpoint_count", "超时配置端点数量不超过总端点数量")
        
        # 性能约束
        self.add_constraint("cache_enabled_count <= endpoint_count", "启用缓存的端点数量不超过总端点数量")
        self.add_constraint("compression_enabled_count <= endpoint_count", "启用压缩的端点数量不超过总端点数量")
        
        # 业务规则约束
        self.add_constraint("endpoint_count >= resource_count", "端点数量不少于资源数量")
        self.add_constraint("resource_count * 2 >= operation_count", "资源数量与操作数量比例合理")
        
        return self.check_consistency()
    
    def validate_interaction_properties(self) -> List[ValidationResult]:
        """验证交互模型属性"""
        properties = [
            ("endpoint_count >= resource_count", "端点数量不少于资源数量"),
            ("operation_count >= resource_count", "操作数量不少于资源数量"),
            ("auth_required_count <= endpoint_count", "认证要求不超过端点总数"),
            ("rate_limit_count <= endpoint_count", "限流配置不超过端点总数"),
        ]
        
        results = []
        for prop_expr, description in properties:
            result = self.validate_property(prop_expr, description)
            results.append(result)
        
        return results

def print_validation_result(result: ValidationResult, title: str = ""):
    """打印验证结果"""
    if title:
        print(f"\n{'='*50}")
        print(f" {title}")
        print(f"{'='*50}")
    
    print(f"状态: {'✅ 成功' if result.success else '❌ 失败'}")
    print(f"消息: {result.message}")
    print(f"执行时间: {result.execution_time:.3f}秒")
    print(f"检查约束数: {result.constraints_checked}")
    print(f"发现违规数: {result.violations_found}")
    
    if result.counter_examples:
        print(f"\n反例/冲突详情:")
        for i, example in enumerate(result.counter_examples, 1):
            if "constraint" in example:
                print(f"  {i}. 约束 {example['constraint_index']}: {example['constraint']}")
                print(f"     描述: {example['description']}")
                print(f"     原因: {example['reason']}")
            else:
                print(f"  {i}. 变量 {example['variable']} = {example['value']} ({example['type']})")

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Z3 约束求解器 - 形式化框架验证')
    parser.add_argument('--model', choices=['data', 'interaction', 'both'], 
                       default='both', help='要验证的模型类型')
    parser.add_argument('--verbose', '-v', action='store_true', 
                       help='详细输出')
    parser.add_argument('--output', '-o', help='输出结果到JSON文件')
    
    args = parser.parse_args()
    
    results = {}
    
    if args.model in ['data', 'both']:
        print("🔍 验证数据模型约束...")
        data_validator = DataModelValidator()
        
        # 验证约束一致性
        consistency_result = data_validator.validate_data_model_constraints()
        results['data_model_consistency'] = consistency_result
        print_validation_result(consistency_result, "数据模型约束一致性验证")
        
        # 验证属性
        if consistency_result.success:
            property_results = data_validator.validate_data_integrity_properties()
            results['data_model_properties'] = property_results
            
            print(f"\n📋 数据模型属性验证结果:")
            for i, prop_result in enumerate(property_results, 1):
                print_validation_result(prop_result, f"属性 {i}")
    
    if args.model in ['interaction', 'both']:
        print("\n🔍 验证交互模型约束...")
        interaction_validator = InteractionModelValidator()
        
        # 验证约束一致性
        consistency_result = interaction_validator.validate_interaction_model_constraints()
        results['interaction_model_consistency'] = consistency_result
        print_validation_result(consistency_result, "交互模型约束一致性验证")
        
        # 验证属性
        if consistency_result.success:
            property_results = interaction_validator.validate_interaction_properties()
            results['interaction_model_properties'] = property_results
            
            print(f"\n📋 交互模型属性验证结果:")
            for i, prop_result in enumerate(property_results, 1):
                print_validation_result(prop_result, f"属性 {i}")
    
    # 保存结果到文件
    if args.output:
        # 转换结果为可序列化格式
        serializable_results = {}
        for key, value in results.items():
            if isinstance(value, ValidationResult):
                serializable_results[key] = {
                    'success': value.success,
                    'message': value.message,
                    'counter_examples': value.counter_examples,
                    'execution_time': value.execution_time,
                    'constraints_checked': value.constraints_checked,
                    'violations_found': value.violations_found
                }
            elif isinstance(value, list):
                serializable_results[key] = []
                for item in value:
                    if isinstance(item, ValidationResult):
                        serializable_results[key].append({
                            'success': item.success,
                            'message': item.message,
                            'counter_examples': item.counter_examples,
                            'execution_time': item.execution_time,
                            'constraints_checked': item.constraints_checked,
                            'violations_found': item.violations_found
                        })
        
        with open(args.output, 'w', encoding='utf-8') as f:
            json.dump(serializable_results, f, indent=2, ensure_ascii=False)
        
        print(f"\n💾 结果已保存到: {args.output}")
    
    # 总结
    print(f"\n{'='*50}")
    print(" 验证总结")
    print(f"{'='*50}")
    
    total_checks = 0
    total_violations = 0
    
    for key, value in results.items():
        if isinstance(value, ValidationResult):
            total_checks += value.constraints_checked
            total_violations += value.violations_found
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, ValidationResult):
                    total_checks += item.constraints_checked
                    total_violations += item.violations_found
    
    print(f"总检查约束数: {total_checks}")
    print(f"总发现违规数: {total_violations}")
    print(f"合规率: {((total_checks - total_violations) / total_checks * 100):.1f}%" if total_checks > 0 else "合规率: N/A")

if __name__ == "__main__":
    main()
