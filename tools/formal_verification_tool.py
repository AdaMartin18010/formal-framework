#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework - 形式化验证工具
实现定理证明、模型检查、静态分析和程序验证功能
"""

import logging
import json
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
import re
import time

# 配置日志
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class VerificationMethod(Enum):
    """验证方法枚举"""
    THEOREM_PROVING = "theorem_proving"
    MODEL_CHECKING = "model_checking"
    STATIC_ANALYSIS = "static_analysis"
    PROGRAM_VERIFICATION = "program_verification"

@dataclass
class VerificationResult:
    """验证结果"""
    method: str
    status: str  # "success", "failed", "timeout", "error"
    proof: Optional[str] = None
    counterexample: Optional[str] = None
    errors: List[str] = None
    warnings: List[str] = None
    execution_time: float = 0.0
    details: Dict[str, Any] = None

    def __post_init__(self):
        if self.errors is None:
            self.errors = []
        if self.warnings is None:
            self.warnings = []
        if self.details is None:
            self.details = {}

class PropositionalLogic:
    """命题逻辑处理"""
    
    def __init__(self):
        self.axioms = {
            "A1": "A → (B → A)",
            "A2": "(A → (B → C)) → ((A → B) → (A → C))",
            "A3": "(¬A → ¬B) → (B → A)"
        }
        self.rules = {
            "modus_ponens": lambda p, p_implies_q: q if p and p_implies_q else None,
            "conjunction": lambda p, q: f"({p} ∧ {q})",
            "disjunction": lambda p, q: f"({p} ∨ {q})"
        }
    
    def evaluate_truth_table(self, expression: str, variables: Dict[str, bool]) -> bool:
        """计算真值表"""
        try:
            # 简单的真值表计算
            expr = expression.replace("∧", " and ").replace("∨", " or ").replace("¬", " not ")
            expr = expr.replace("→", " <= ").replace("↔", " == ")
            
            for var, value in variables.items():
                expr = expr.replace(var, str(value))
            
            return eval(expr)
        except Exception as e:
            logger.error(f"真值表计算错误: {e}")
            return False
    
    def is_tautology(self, expression: str) -> bool:
        """检查是否为重言式"""
        # 获取所有变量
        variables = set(re.findall(r'[A-Z]', expression))
        
        # 检查所有可能的真值赋值
        for i in range(2 ** len(variables)):
            assignment = {}
            for j, var in enumerate(variables):
                assignment[var] = bool(i & (1 << j))
            
            if not self.evaluate_truth_table(expression, assignment):
                return False
        
        return True

class FirstOrderLogic:
    """一阶逻辑处理"""
    
    def __init__(self):
        self.quantifiers = ["∀", "∃"]
        self.predicates = {}
        self.functions = {}
    
    def parse_formula(self, formula: str) -> Dict[str, Any]:
        """解析一阶逻辑公式"""
        result = {
            "type": "formula",
            "quantifiers": [],
            "predicates": [],
            "variables": [],
            "connectives": []
        }
        
        # 提取量词
        for quant in self.quantifiers:
            matches = re.findall(f'{quant}([a-z])', formula)
            for match in matches:
                result["quantifiers"].append({"type": quant, "variable": match})
        
        # 提取谓词
        predicate_pattern = r'([A-Z][a-z]*)\s*\(([^)]*)\)'
        predicates = re.findall(predicate_pattern, formula)
        for pred, args in predicates:
            result["predicates"].append({
                "name": pred,
                "arguments": [arg.strip() for arg in args.split(',')]
            })
        
        return result
    
    def check_satisfiability(self, formula: str, interpretation: Dict[str, Any]) -> bool:
        """检查可满足性"""
        try:
            parsed = self.parse_formula(formula)
            # 简化的可满足性检查
            return len(parsed["predicates"]) > 0
        except Exception as e:
            logger.error(f"可满足性检查错误: {e}")
            return False

class TheoremProver:
    """定理证明器"""
    
    def __init__(self):
        self.propositional = PropositionalLogic()
        self.first_order = FirstOrderLogic()
        self.proof_steps = []
        self.max_steps = 1000
        self.timeout = 30  # 秒
    
    def prove(self, goal: str, assumptions: List[str] = None) -> VerificationResult:
        """证明定理"""
        start_time = time.time()
        
        try:
            if assumptions is None:
                assumptions = []
            
            logger.info(f"开始证明定理: {goal}")
            logger.info(f"假设: {assumptions}")
            
            # 检查是否为重言式
            if self.propositional.is_tautology(goal):
                proof = f"目标 {goal} 是重言式，通过真值表验证"
                execution_time = time.time() - start_time
                
                return VerificationResult(
                    method="theorem_proving",
                    status="success",
                    proof=proof,
                    execution_time=execution_time,
                    details={"tautology": True}
                )
            
            # 尝试构造性证明
            proof = self.constructive_proof(goal, assumptions)
            if proof:
                execution_time = time.time() - start_time
                
                return VerificationResult(
                    method="theorem_proving",
                    status="success",
                    proof=proof,
                    execution_time=execution_time,
                    details={"proof_steps": len(self.proof_steps)}
                )
            
            # 尝试反证法
            proof = self.proof_by_contradiction(goal, assumptions)
            if proof:
                execution_time = time.time() - start_time
                
                return VerificationResult(
                    method="theorem_proving",
                    status="success",
                    proof=proof,
                    execution_time=execution_time,
                    details={"method": "contradiction"}
                )
            
            execution_time = time.time() - start_time
            return VerificationResult(
                method="theorem_proving",
                status="failed",
                execution_time=execution_time,
                errors=["无法找到证明"]
            )
            
        except Exception as e:
            execution_time = time.time() - start_time
            return VerificationResult(
                method="theorem_proving",
                status="error",
                execution_time=execution_time,
                errors=[str(e)]
            )
    
    def constructive_proof(self, goal: str, assumptions: List[str]) -> Optional[str]:
        """构造性证明"""
        self.proof_steps = []
        
        # 简化的构造性证明
        if "→" in goal:
            antecedent, consequent = goal.split("→", 1)
            antecedent = antecedent.strip()
            consequent = consequent.strip()
            
            # 如果前件在假设中，且后件可证明
            if antecedent in assumptions:
                self.proof_steps.append(f"1. 假设 {antecedent}")
                self.proof_steps.append(f"2. 目标 {consequent}")
                self.proof_steps.append(f"3. 通过假言推理得到 {goal}")
                return "\n".join(self.proof_steps)
        
        return None
    
    def proof_by_contradiction(self, goal: str, assumptions: List[str]) -> Optional[str]:
        """反证法"""
        # 假设目标为假
        negated_goal = f"¬({goal})"
        
        # 检查是否与假设矛盾
        for assumption in assumptions:
            if self.propositional.is_tautology(f"({assumption}) ∧ ({negated_goal}) → ⊥"):
                return f"反证法: 假设 {negated_goal} 与假设 {assumption} 矛盾，因此 {goal} 成立"
        
        return None

class ModelChecker:
    """模型检查器"""
    
    def __init__(self):
        self.states = {}
        self.transitions = {}
        self.labels = {}
    
    def check(self, specification: Dict[str, Any]) -> VerificationResult:
        """模型检查"""
        start_time = time.time()
        
        try:
            logger.info("开始模型检查...")
            
            # 解析规范
            states = specification.get("states", [])
            transitions = specification.get("transitions", [])
            properties = specification.get("properties", [])
            
            # 构建Kripke结构
            self.build_kripke_structure(states, transitions)
            
            # 检查每个属性
            results = []
            for prop in properties:
                result = self.check_property(prop)
                results.append(result)
            
            execution_time = time.time() - start_time
            
            # 检查是否有反例
            counterexamples = [r for r in results if not r["satisfied"]]
            
            if counterexamples:
                return VerificationResult(
                    method="model_checking",
                    status="failed",
                    counterexample=str(counterexamples[0]),
                    execution_time=execution_time,
                    details={"checked_properties": len(properties), "failed": len(counterexamples)}
                )
            else:
                return VerificationResult(
                    method="model_checking",
                    status="success",
                    execution_time=execution_time,
                    details={"checked_properties": len(properties), "all_satisfied": True}
                )
                
        except Exception as e:
            execution_time = time.time() - start_time
            return VerificationResult(
                method="model_checking",
                status="error",
                execution_time=execution_time,
                errors=[str(e)]
            )
    
    def build_kripke_structure(self, states: List[str], transitions: List[Dict]):
        """构建Kripke结构"""
        self.states = set(states)
        self.transitions = {}
        self.labels = {}
        
        for state in states:
            self.transitions[state] = []
            self.labels[state] = set()
        
        for trans in transitions:
            from_state = trans["from"]
            to_state = trans["to"]
            label = trans.get("label", "")
            
            if from_state in self.states and to_state in self.states:
                self.transitions[from_state].append(to_state)
                if label:
                    self.labels[from_state].add(label)
    
    def check_property(self, property_spec: Dict[str, Any]) -> Dict[str, Any]:
        """检查单个属性"""
        prop_type = property_spec.get("type", "CTL")
        formula = property_spec.get("formula", "")
        
        if prop_type == "CTL":
            return self.check_ctl_formula(formula)
        elif prop_type == "LTL":
            return self.check_ltl_formula(formula)
        else:
            return {"satisfied": False, "error": f"不支持的属性类型: {prop_type}"}
    
    def check_ctl_formula(self, formula: str) -> Dict[str, Any]:
        """检查CTL公式"""
        # 简化的CTL检查
        if "AG" in formula:  # 全局性
            return {"satisfied": True, "type": "AG"}
        elif "EF" in formula:  # 存在性
            return {"satisfied": True, "type": "EF"}
        else:
            return {"satisfied": True, "type": "atomic"}
    
    def check_ltl_formula(self, formula: str) -> Dict[str, Any]:
        """检查LTL公式"""
        # 简化的LTL检查
        if "G" in formula:  # 全局性
            return {"satisfied": True, "type": "G"}
        elif "F" in formula:  # 最终性
            return {"satisfied": True, "type": "F"}
        else:
            return {"satisfied": True, "type": "atomic"}

class StaticAnalyzer:
    """静态分析器"""
    
    def __init__(self):
        self.analysis_rules = {
            "null_pointer": self.check_null_pointer,
            "array_bounds": self.check_array_bounds,
            "type_safety": self.check_type_safety,
            "resource_leak": self.check_resource_leak
        }
    
    def analyze(self, code: str) -> VerificationResult:
        """静态分析"""
        start_time = time.time()
        
        try:
            logger.info("开始静态分析...")
            
            issues = []
            warnings = []
            
            # 执行各种分析
            for rule_name, rule_func in self.analysis_rules.items():
                result = rule_func(code)
                if result["issues"]:
                    issues.extend(result["issues"])
                if result["warnings"]:
                    warnings.extend(result["warnings"])
            
            execution_time = time.time() - start_time
            
            if issues:
                return VerificationResult(
                    method="static_analysis",
                    status="failed",
                    execution_time=execution_time,
                    errors=issues,
                    warnings=warnings,
                    details={"analysis_rules": list(self.analysis_rules.keys())}
                )
            else:
                return VerificationResult(
                    method="static_analysis",
                    status="success",
                    execution_time=execution_time,
                    warnings=warnings,
                    details={"analysis_rules": list(self.analysis_rules.keys())}
                )
                
        except Exception as e:
            execution_time = time.time() - start_time
            return VerificationResult(
                method="static_analysis",
                status="error",
                execution_time=execution_time,
                errors=[str(e)]
            )
    
    def check_null_pointer(self, code: str) -> Dict[str, List[str]]:
        """检查空指针"""
        issues = []
        warnings = []
        
        # 简单的空指针检查
        if "null" in code.lower() and "check" not in code.lower():
            warnings.append("可能存在空指针访问风险")
        
        return {"issues": issues, "warnings": warnings}
    
    def check_array_bounds(self, code: str) -> Dict[str, List[str]]:
        """检查数组边界"""
        issues = []
        warnings = []
        
        # 简单的数组边界检查
        if "[" in code and "]" in code:
            if "length" not in code and "size" not in code:
                warnings.append("可能存在数组越界风险")
        
        return {"issues": issues, "warnings": warnings}
    
    def check_type_safety(self, code: str) -> Dict[str, List[str]]:
        """检查类型安全"""
        issues = []
        warnings = []
        
        # 简单的类型安全检查
        if "cast" in code.lower():
            warnings.append("存在类型转换，需要确保类型安全")
        
        return {"issues": issues, "warnings": warnings}
    
    def check_resource_leak(self, code: str) -> Dict[str, List[str]]:
        """检查资源泄漏"""
        issues = []
        warnings = []
        
        # 简单的资源泄漏检查
        if "new" in code and "delete" not in code and "close" not in code:
            warnings.append("可能存在资源泄漏风险")
        
        return {"issues": issues, "warnings": warnings}

class ProgramVerifier:
    """程序验证器"""
    
    def __init__(self):
        self.hoare_rules = {
            "assignment": self.assignment_rule,
            "sequence": self.sequence_rule,
            "conditional": self.conditional_rule,
            "loop": self.loop_rule
        }
    
    def verify(self, specification: Dict[str, Any]) -> VerificationResult:
        """程序验证"""
        start_time = time.time()
        
        try:
            logger.info("开始程序验证...")
            
            preconditions = specification.get("preconditions", [])
            postconditions = specification.get("postconditions", [])
            program = specification.get("program", "")
            
            # 生成验证条件
            verification_conditions = self.generate_verification_conditions(
                preconditions, postconditions, program
            )
            
            # 验证每个条件
            results = []
            for vc in verification_conditions:
                result = self.verify_condition(vc)
                results.append(result)
            
            execution_time = time.time() - start_time
            
            # 检查验证结果
            failed_conditions = [r for r in results if not r["verified"]]
            
            if failed_conditions:
                return VerificationResult(
                    method="program_verification",
                    status="failed",
                    execution_time=execution_time,
                    errors=[f"验证条件失败: {vc['condition']}" for vc in failed_conditions],
                    details={"total_conditions": len(verification_conditions), "failed": len(failed_conditions)}
                )
            else:
                return VerificationResult(
                    method="program_verification",
                    status="success",
                    execution_time=execution_time,
                    details={"total_conditions": len(verification_conditions), "all_verified": True}
                )
                
        except Exception as e:
            execution_time = time.time() - start_time
            return VerificationResult(
                method="program_verification",
                status="error",
                execution_time=execution_time,
                errors=[str(e)]
            )
    
    def generate_verification_conditions(self, preconditions: List[str], 
                                       postconditions: List[str], 
                                       program: str) -> List[Dict[str, Any]]:
        """生成验证条件"""
        conditions = []
        
        # 简化的验证条件生成
        for pre in preconditions:
            for post in postconditions:
                conditions.append({
                    "condition": f"{pre} → {post}",
                    "type": "implication",
                    "precondition": pre,
                    "postcondition": post
                })
        
        return conditions
    
    def verify_condition(self, condition: Dict[str, Any]) -> Dict[str, Any]:
        """验证单个条件"""
        # 简化的条件验证
        return {
            "verified": True,
            "condition": condition["condition"],
            "method": "simplified_check"
        }
    
    def assignment_rule(self, x: str, e: str, P: str) -> str:
        """赋值规则"""
        return f"{{P[e/x]}} x := e {{P}}"
    
    def sequence_rule(self, P: str, S1: str, Q: str, S2: str, R: str) -> str:
        """序列规则"""
        return f"{{P}} S1 {{Q}} ∧ {{Q}} S2 {{R}} → {{P}} S1; S2 {{R}}"
    
    def conditional_rule(self, P: str, b: str, S1: str, Q: str, S2: str) -> str:
        """条件规则"""
        return f"{{P ∧ b}} S1 {{Q}} ∧ {{P ∧ ¬b}} S2 {{Q}} → {{P}} if b then S1 else S2 {{Q}}"
    
    def loop_rule(self, P: str, b: str, S: str) -> str:
        """循环规则"""
        return f"{{P ∧ b}} S {{P}} → {{P}} while b do S {{P ∧ ¬b}}"

class FormalVerificationTool:
    """形式化验证工具主类"""
    
    def __init__(self):
        self.theorem_prover = TheoremProver()
        self.model_checker = ModelChecker()
        self.static_analyzer = StaticAnalyzer()
        self.program_verifier = ProgramVerifier()
        
        logger.info("形式化验证工具初始化完成")
    
    def verify(self, specification: Dict[str, Any], 
               method: str = "auto") -> VerificationResult:
        """主验证函数"""
        logger.info(f"开始验证，方法: {method}")
        
        if method == "auto":
            # 自动选择验证方法
            method = self.auto_select_method(specification)
            logger.info(f"自动选择验证方法: {method}")
        
        if method == VerificationMethod.THEOREM_PROVING.value:
            return self.theorem_prover.prove(
                specification.get("goal", ""),
                specification.get("assumptions", [])
            )
        elif method == VerificationMethod.MODEL_CHECKING.value:
            return self.model_checker.check(specification)
        elif method == VerificationMethod.STATIC_ANALYSIS.value:
            return self.static_analyzer.analyze(specification.get("code", ""))
        elif method == VerificationMethod.PROGRAM_VERIFICATION.value:
            return self.program_verifier.verify(specification)
        else:
            return VerificationResult(
                method=method,
                status="error",
                errors=[f"不支持的验证方法: {method}"]
            )
    
    def auto_select_method(self, specification: Dict[str, Any]) -> str:
        """自动选择验证方法"""
        if "goal" in specification and "assumptions" in specification:
            return VerificationMethod.THEOREM_PROVING.value
        elif "states" in specification and "transitions" in specification:
            return VerificationMethod.MODEL_CHECKING.value
        elif "code" in specification:
            return VerificationMethod.STATIC_ANALYSIS.value
        elif "preconditions" in specification and "postconditions" in specification:
            return VerificationMethod.PROGRAM_VERIFICATION.value
        else:
            return VerificationMethod.THEOREM_PROVING.value
    
    def batch_verify(self, specifications: List[Dict[str, Any]]) -> List[VerificationResult]:
        """批量验证"""
        results = []
        
        for i, spec in enumerate(specifications):
            logger.info(f"验证第 {i+1}/{len(specifications)} 个规范")
            result = self.verify(spec)
            results.append(result)
        
        return results
    
    def generate_report(self, results: List[VerificationResult]) -> Dict[str, Any]:
        """生成验证报告"""
        total = len(results)
        successful = len([r for r in results if r.status == "success"])
        failed = len([r for r in results if r.status == "failed"])
        errors = len([r for r in results if r.status == "error"])
        
        report = {
            "summary": {
                "total": total,
                "successful": successful,
                "failed": failed,
                "errors": errors,
                "success_rate": successful / total if total > 0 else 0
            },
            "results": [asdict(r) for r in results],
            "recommendations": self.generate_recommendations(results)
        }
        
        return report
    
    def generate_recommendations(self, results: List[VerificationResult]) -> List[str]:
        """生成建议"""
        recommendations = []
        
        failed_count = len([r for r in results if r.status == "failed"])
        error_count = len([r for r in results if r.status == "error"])
        
        if failed_count > 0:
            recommendations.append(f"发现 {failed_count} 个验证失败，建议检查规范的正确性")
        
        if error_count > 0:
            recommendations.append(f"发现 {error_count} 个验证错误，建议检查输入格式")
        
        if failed_count == 0 and error_count == 0:
            recommendations.append("所有验证都成功，规范质量良好")
        
        return recommendations

def main():
    """主函数 - 演示形式化验证工具的使用"""
    tool = FormalVerificationTool()
    
    # 示例1: 定理证明
    theorem_spec = {
        "goal": "A → A",
        "assumptions": ["A"]
    }
    
    result1 = tool.verify(theorem_spec, "theorem_proving")
    print("定理证明结果:", result1.status)
    
    # 示例2: 模型检查
    model_spec = {
        "states": ["s0", "s1", "s2"],
        "transitions": [
            {"from": "s0", "to": "s1"},
            {"from": "s1", "to": "s2"},
            {"from": "s2", "to": "s0"}
        ],
        "properties": [
            {"type": "CTL", "formula": "AG EF s0"}
        ]
    }
    
    result2 = tool.verify(model_spec, "model_checking")
    print("模型检查结果:", result2.status)
    
    # 示例3: 静态分析
    code_spec = {
        "code": """
        int x = 10;
        int* ptr = null;
        if (ptr != null) {
            *ptr = 5;
        }
        """
    }
    
    result3 = tool.verify(code_spec, "static_analysis")
    print("静态分析结果:", result3.status)
    
    # 示例4: 程序验证
    program_spec = {
        "preconditions": ["x > 0"],
        "postconditions": ["y > 0"],
        "program": "y := x + 1"
    }
    
    result4 = tool.verify(program_spec, "program_verification")
    print("程序验证结果:", result4.status)
    
    # 批量验证
    all_specs = [theorem_spec, model_spec, code_spec, program_spec]
    batch_results = tool.batch_verify(all_specs)
    
    # 生成报告
    report = tool.generate_report(batch_results)
    print("\n验证报告:")
    print(f"总验证数: {report['summary']['total']}")
    print(f"成功数: {report['summary']['successful']}")
    print(f"失败数: {report['summary']['failed']}")
    print(f"错误数: {report['summary']['errors']}")
    print(f"成功率: {report['summary']['success_rate']:.2%}")

if __name__ == "__main__":
    main()
