#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Framework - 自动化推理引擎
实现前向推理、后向推理、归结推理和知识图谱推理功能
"""

import logging
import json
from typing import Dict, List, Optional, Any, Tuple, Set
from dataclasses import dataclass, asdict
from enum import Enum
import re
import time
from collections import defaultdict, deque

# 配置日志
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class ReasoningMethod(Enum):
    """推理方法枚举"""
    FORWARD_CHAINING = "forward_chaining"
    BACKWARD_CHAINING = "backward_chaining"
    RESOLUTION = "resolution"
    KNOWLEDGE_GRAPH = "knowledge_graph"

@dataclass
class ReasoningResult:
    """推理结果"""
    method: str
    status: str  # "success", "failed", "timeout", "error"
    conclusion: Optional[str] = None
    proof_path: List[str] = None
    confidence: float = 0.0
    execution_time: float = 0.0
    details: Dict[str, Any] = None

    def __post_init__(self):
        if self.proof_path is None:
            self.proof_path = []
        if self.details is None:
            self.details = {}

@dataclass
class Rule:
    """推理规则"""
    name: str
    premises: List[str]
    conclusion: str
    confidence: float = 1.0
    description: str = ""

@dataclass
class Fact:
    """事实"""
    statement: str
    confidence: float = 1.0
    source: str = ""
    timestamp: float = 0.0

class KnowledgeBase:
    """知识库"""
    
    def __init__(self):
        self.facts: Set[str] = set()
        self.rules: List[Rule] = []
        self.fact_confidence: Dict[str, float] = {}
        self.fact_sources: Dict[str, str] = {}
        
        logger.info("知识库初始化完成")
    
    def add_fact(self, fact: str, confidence: float = 1.0, source: str = ""):
        """添加事实"""
        self.facts.add(fact)
        self.fact_confidence[fact] = confidence
        self.fact_sources[fact] = source
        logger.info(f"添加事实: {fact} (置信度: {confidence})")
    
    def add_rule(self, rule: Rule):
        """添加规则"""
        self.rules.append(rule)
        logger.info(f"添加规则: {rule.name}")
    
    def get_facts(self) -> Set[str]:
        """获取所有事实"""
        return self.facts.copy()
    
    def get_rules(self) -> List[Rule]:
        """获取所有规则"""
        return self.rules.copy()
    
    def contains_fact(self, fact: str) -> bool:
        """检查是否包含事实"""
        return fact in self.facts
    
    def get_fact_confidence(self, fact: str) -> float:
        """获取事实置信度"""
        return self.fact_confidence.get(fact, 0.0)

class ForwardChainingEngine:
    """前向推理引擎"""
    
    def __init__(self, knowledge_base: KnowledgeBase):
        self.kb = knowledge_base
        self.inferred_facts: Set[str] = set()
        self.inference_history: List[Dict[str, Any]] = []
        
        logger.info("前向推理引擎初始化完成")
    
    def reason(self, goal: str = None) -> ReasoningResult:
        """前向推理"""
        start_time = time.time()
        
        try:
            logger.info("开始前向推理...")
            
            self.inferred_facts = self.kb.get_facts().copy()
            self.inference_history = []
            
            # 执行推理循环
            changed = True
            iteration = 0
            max_iterations = 1000
            
            while changed and iteration < max_iterations:
                changed = False
                iteration += 1
                
                for rule in self.kb.get_rules():
                    # 检查规则前提是否满足
                    if self.check_premises(rule.premises):
                        # 检查结论是否已经存在
                        if rule.conclusion not in self.inferred_facts:
                            # 添加新结论
                            self.inferred_facts.add(rule.conclusion)
                            self.kb.add_fact(rule.conclusion, rule.confidence, f"推理规则: {rule.name}")
                            
                            # 记录推理历史
                            self.inference_history.append({
                                "iteration": iteration,
                                "rule": rule.name,
                                "premises": rule.premises,
                                "conclusion": rule.conclusion,
                                "confidence": rule.confidence
                            })
                            
                            changed = True
                            logger.info(f"推理步骤 {iteration}: 使用规则 {rule.name} 推导出 {rule.conclusion}")
            
            execution_time = time.time() - start_time
            
            # 检查目标是否达成
            if goal and goal in self.inferred_facts:
                return ReasoningResult(
                    method="forward_chaining",
                    status="success",
                    conclusion=goal,
                    proof_path=self.build_proof_path(goal),
                    confidence=self.kb.get_fact_confidence(goal),
                    execution_time=execution_time,
                    details={
                        "iterations": iteration,
                        "new_facts": len(self.inferred_facts) - len(self.kb.get_facts()),
                        "inference_history": self.inference_history
                    }
                )
            else:
                return ReasoningResult(
                    method="forward_chaining",
                    status="success" if not goal else "failed",
                    conclusion="推理完成，但未达到目标" if goal else "推理完成",
                    proof_path=[],
                    confidence=0.0,
                    execution_time=execution_time,
                    details={
                        "iterations": iteration,
                        "new_facts": len(self.inferred_facts) - len(self.kb.get_facts()),
                        "inference_history": self.inference_history
                    }
                )
                
        except Exception as e:
            execution_time = time.time() - start_time
            return ReasoningResult(
                method="forward_chaining",
                status="error",
                execution_time=execution_time,
                errors=[str(e)]
            )
    
    def check_premises(self, premises: List[str]) -> bool:
        """检查前提是否满足"""
        for premise in premises:
            if premise not in self.inferred_facts:
                return False
        return True
    
    def build_proof_path(self, goal: str) -> List[str]:
        """构建证明路径"""
        path = []
        
        # 从推理历史中构建路径
        for step in reversed(self.inference_history):
            if step["conclusion"] == goal:
                path.append(f"使用规则 {step['rule']}: {step['premises']} → {step['conclusion']}")
                # 递归构建前提的证明路径
                for premise in step["premises"]:
                    if premise not in self.kb.get_facts():  # 如果不是初始事实
                        sub_path = self.build_proof_path(premise)
                        path.extend(sub_path)
                break
        
        return path

class BackwardChainingEngine:
    """后向推理引擎"""
    
    def __init__(self, knowledge_base: KnowledgeBase):
        self.kb = knowledge_base
        self.proof_tree: Dict[str, Any] = {}
        self.visited_goals: Set[str] = set()
        
        logger.info("后向推理引擎初始化完成")
    
    def reason(self, goal: str) -> ReasoningResult:
        """后向推理"""
        start_time = time.time()
        
        try:
            logger.info(f"开始后向推理，目标: {goal}")
            
            self.proof_tree = {}
            self.visited_goals = set()
            
            # 执行后向推理
            success, proof_tree = self.backward_chain(goal)
            
            execution_time = time.time() - start_time
            
            if success:
                proof_path = self.build_proof_path(proof_tree)
                return ReasoningResult(
                    method="backward_chaining",
                    status="success",
                    conclusion=goal,
                    proof_path=proof_path,
                    confidence=self.kb.get_fact_confidence(goal),
                    execution_time=execution_time,
                    details={"proof_tree": proof_tree}
                )
            else:
                return ReasoningResult(
                    method="backward_chaining",
                    status="failed",
                    conclusion=goal,
                    proof_path=[],
                    confidence=0.0,
                    execution_time=execution_time,
                    details={"proof_tree": proof_tree}
                )
                
        except Exception as e:
            execution_time = time.time() - start_time
            return ReasoningResult(
                method="backward_chaining",
                status="error",
                execution_time=execution_time,
                errors=[str(e)]
            )
    
    def backward_chain(self, goal: str) -> Tuple[bool, Dict[str, Any]]:
        """后向推理核心算法"""
        # 避免循环推理
        if goal in self.visited_goals:
            return False, {}
        
        self.visited_goals.add(goal)
        
        # 检查目标是否为已知事实
        if self.kb.contains_fact(goal):
            return True, {"type": "fact", "statement": goal}
        
        # 查找可以推导目标的规则
        applicable_rules = []
        for rule in self.kb.get_rules():
            if rule.conclusion == goal:
                applicable_rules.append(rule)
        
        if not applicable_rules:
            return False, {"type": "failed", "reason": "no_applicable_rules"}
        
        # 尝试每个适用规则
        for rule in applicable_rules:
            # 递归证明前提
            premises_proofs = {}
            all_premises_proven = True
            
            for premise in rule.premises:
                success, proof = self.backward_chain(premise)
                if success:
                    premises_proofs[premise] = proof
                else:
                    all_premises_proven = False
                    break
            
            if all_premises_proven:
                return True, {
                    "type": "rule",
                    "rule_name": rule.name,
                    "conclusion": goal,
                    "premises": premises_proofs,
                    "confidence": rule.confidence
                }
        
        return False, {"type": "failed", "reason": "no_proof_found"}
    
    def build_proof_path(self, proof_tree: Dict[str, Any]) -> List[str]:
        """构建证明路径"""
        path = []
        
        if proof_tree.get("type") == "fact":
            path.append(f"已知事实: {proof_tree['statement']}")
        elif proof_tree.get("type") == "rule":
            path.append(f"使用规则 {proof_tree['rule_name']}: {proof_tree['conclusion']}")
            # 递归构建前提的证明路径
            for premise, premise_proof in proof_tree["premises"].items():
                sub_path = self.build_proof_path(premise_proof)
                path.extend(sub_path)
        
        return path

class ResolutionEngine:
    """归结推理引擎"""
    
    def __init__(self, knowledge_base: KnowledgeBase):
        self.kb = knowledge_base
        self.clauses: List[List[str]] = []
        self.resolution_history: List[Dict[str, Any]] = []
        
        logger.info("归结推理引擎初始化完成")
    
    def reason(self, goal: str) -> ReasoningResult:
        """归结推理"""
        start_time = time.time()
        
        try:
            logger.info(f"开始归结推理，目标: {goal}")
            
            # 将知识库转换为子句形式
            self.convert_to_clauses()
            
            # 添加目标的否定
            negated_goal = self.negate_literal(goal)
            self.clauses.append([negated_goal])
            
            # 执行归结
            success, proof = self.resolution_procedure()
            
            execution_time = time.time() - start_time
            
            if success:
                return ReasoningResult(
                    method="resolution",
                    status="success",
                    conclusion=goal,
                    proof_path=self.build_resolution_proof(proof),
                    confidence=1.0,
                    execution_time=execution_time,
                    details={"resolution_steps": len(self.resolution_history)}
                )
            else:
                return ReasoningResult(
                    method="resolution",
                    status="failed",
                    conclusion=goal,
                    proof_path=[],
                    confidence=0.0,
                    execution_time=execution_time,
                    details={"resolution_steps": len(self.resolution_history)}
                )
                
        except Exception as e:
            execution_time = time.time() - start_time
            return ReasoningResult(
                method="resolution",
                status="error",
                execution_time=execution_time,
                errors=[str(e)]
            )
    
    def convert_to_clauses(self):
        """将知识库转换为子句形式"""
        self.clauses = []
        
        # 转换事实为子句
        for fact in self.kb.get_facts():
            self.clauses.append([fact])
        
        # 转换规则为子句
        for rule in self.kb.get_rules():
            # 规则 A ∧ B → C 转换为子句 ¬A ∨ ¬B ∨ C
            clause = []
            for premise in rule.premises:
                clause.append(self.negate_literal(premise))
            clause.append(rule.conclusion)
            self.clauses.append(clause)
    
    def negate_literal(self, literal: str) -> str:
        """否定文字"""
        if literal.startswith("¬"):
            return literal[1:]
        else:
            return f"¬{literal}"
    
    def resolution_procedure(self) -> Tuple[bool, List[Dict[str, Any]]]:
        """归结过程"""
        self.resolution_history = []
        new_clauses = []
        
        while True:
            # 尝试归结所有子句对
            for i, clause1 in enumerate(self.clauses):
                for j, clause2 in enumerate(self.clauses[i+1:], i+1):
                    resolvent = self.resolve_clauses(clause1, clause2)
                    if resolvent is not None:
                        if not resolvent:  # 空子句，证明成功
                            self.resolution_history.append({
                                "clause1": clause1,
                                "clause2": clause2,
                                "resolvent": [],
                                "result": "contradiction_found"
                            })
                            return True, self.resolution_history
                        
                        # 检查是否是新子句
                        if resolvent not in self.clauses and resolvent not in new_clauses:
                            new_clauses.append(resolvent)
                            self.resolution_history.append({
                                "clause1": clause1,
                                "clause2": clause2,
                                "resolvent": resolvent,
                                "result": "new_clause"
                            })
            
            # 检查是否有新子句
            if not new_clauses:
                return False, self.resolution_history
            
            # 添加新子句
            self.clauses.extend(new_clauses)
            new_clauses = []
    
    def resolve_clauses(self, clause1: List[str], clause2: List[str]) -> Optional[List[str]]:
        """归结两个子句"""
        # 寻找互补文字
        for literal1 in clause1:
            for literal2 in clause2:
                if literal1 == self.negate_literal(literal2):
                    # 找到互补文字，执行归结
                    resolvent = []
                    
                    # 添加clause1中除literal1外的所有文字
                    for lit in clause1:
                        if lit != literal1:
                            resolvent.append(lit)
                    
                    # 添加clause2中除literal2外的所有文字
                    for lit in clause2:
                        if lit != literal2:
                            resolvent.append(lit)
                    
                    # 去重
                    resolvent = list(set(resolvent))
                    
                    return resolvent
        
        return None
    
    def build_resolution_proof(self, proof: List[Dict[str, Any]]) -> List[str]:
        """构建归结证明路径"""
        path = []
        
        for step in proof:
            if step["result"] == "new_clause":
                path.append(f"归结: {step['clause1']} + {step['clause2']} → {step['resolvent']}")
            elif step["result"] == "contradiction_found":
                path.append(f"发现矛盾: {step['clause1']} + {step['clause2']} → 空子句")
        
        return path

class KnowledgeGraphEngine:
    """知识图谱推理引擎"""
    
    def __init__(self, knowledge_base: KnowledgeBase):
        self.kb = knowledge_base
        self.graph: Dict[str, Dict[str, Any]] = defaultdict(dict)
        self.entities: Set[str] = set()
        self.relationships: List[Dict[str, Any]] = []
        
        logger.info("知识图谱推理引擎初始化完成")
    
    def build_graph(self):
        """构建知识图谱"""
        self.graph.clear()
        self.entities.clear()
        self.relationships.clear()
        
        # 从事实中提取实体和关系
        for fact in self.kb.get_facts():
            self.extract_entities_and_relationships(fact)
        
        # 从规则中提取实体和关系
        for rule in self.kb.get_rules():
            self.extract_entities_and_relationships(rule.conclusion)
            for premise in rule.premises:
                self.extract_entities_and_relationships(premise)
        
        logger.info(f"知识图谱构建完成: {len(self.entities)} 个实体, {len(self.relationships)} 个关系")
    
    def extract_entities_and_relationships(self, statement: str):
        """从语句中提取实体和关系"""
        # 简单的实体和关系提取
        # 假设格式: Entity1 relation Entity2 或 relation(Entity1, Entity2)
        
        # 处理二元关系
        relation_pattern = r'(\w+)\s+(\w+)\s+(\w+)'
        matches = re.findall(relation_pattern, statement)
        
        for match in matches:
            entity1, relation, entity2 = match
            self.entities.add(entity1)
            self.entities.add(entity2)
            
            # 添加关系
            self.relationships.append({
                "source": entity1,
                "relation": relation,
                "target": entity2,
                "statement": statement
            })
            
            # 构建图结构
            if entity1 not in self.graph:
                self.graph[entity1] = {}
            if entity2 not in self.graph:
                self.graph[entity2] = {}
            
            if relation not in self.graph[entity1]:
                self.graph[entity1][relation] = []
            self.graph[entity1][relation].append(entity2)
    
    def reason(self, query: str) -> ReasoningResult:
        """知识图谱推理"""
        start_time = time.time()
        
        try:
            logger.info(f"开始知识图谱推理，查询: {query}")
            
            # 构建知识图谱
            self.build_graph()
            
            # 解析查询
            query_type, entities = self.parse_query(query)
            
            if query_type == "path_query":
                # 路径查询
                if len(entities) >= 2:
                    paths = self.find_paths(entities[0], entities[1])
                    execution_time = time.time() - start_time
                    
                    if paths:
                        return ReasoningResult(
                            method="knowledge_graph",
                            status="success",
                            conclusion=f"找到 {len(paths)} 条路径",
                            proof_path=self.build_path_proof(paths),
                            confidence=1.0,
                            execution_time=execution_time,
                            details={"paths": paths}
                        )
                    else:
                        return ReasoningResult(
                            method="knowledge_graph",
                            status="failed",
                            conclusion="未找到路径",
                            proof_path=[],
                            confidence=0.0,
                            execution_time=execution_time
                        )
            
            elif query_type == "neighbor_query":
                # 邻居查询
                neighbors = self.find_neighbors(entities[0])
                execution_time = time.time() - start_time
                
                return ReasoningResult(
                    method="knowledge_graph",
                    status="success",
                    conclusion=f"找到 {len(neighbors)} 个邻居",
                    proof_path=self.build_neighbor_proof(neighbors),
                    confidence=1.0,
                    execution_time=execution_time,
                    details={"neighbors": neighbors}
                )
            
            else:
                execution_time = time.time() - start_time
                return ReasoningResult(
                    method="knowledge_graph",
                    status="error",
                    execution_time=execution_time,
                    errors=["不支持的查询类型"]
                )
                
        except Exception as e:
            execution_time = time.time() - start_time
            return ReasoningResult(
                method="knowledge_graph",
                status="error",
                execution_time=execution_time,
                errors=[str(e)]
            )
    
    def parse_query(self, query: str) -> Tuple[str, List[str]]:
        """解析查询"""
        # 简单的查询解析
        if "到" in query or "path" in query.lower():
            # 路径查询
            entities = re.findall(r'\w+', query)
            return "path_query", entities
        else:
            # 邻居查询
            entities = re.findall(r'\w+', query)
            return "neighbor_query", entities[:1]
    
    def find_paths(self, source: str, target: str, max_depth: int = 3) -> List[List[str]]:
        """查找路径"""
        paths = []
        
        def dfs(current: str, path: List[str], depth: int):
            if depth > max_depth:
                return
            
            if current == target:
                paths.append(path[:])
                return
            
            if current in self.graph:
                for relation, targets in self.graph[current].items():
                    for target_entity in targets:
                        if target_entity not in path:  # 避免循环
                            new_path = path + [relation, target_entity]
                            dfs(target_entity, new_path, depth + 1)
        
        dfs(source, [source], 0)
        return paths
    
    def find_neighbors(self, entity: str) -> List[Dict[str, Any]]:
        """查找邻居"""
        neighbors = []
        
        if entity in self.graph:
            for relation, targets in self.graph[entity].items():
                for target in targets:
                    neighbors.append({
                        "relation": relation,
                        "target": target
                    })
        
        return neighbors
    
    def build_path_proof(self, paths: List[List[str]]) -> List[str]:
        """构建路径证明"""
        proof = []
        
        for i, path in enumerate(paths):
            path_str = " → ".join(path)
            proof.append(f"路径 {i+1}: {path_str}")
        
        return proof
    
    def build_neighbor_proof(self, neighbors: List[Dict[str, Any]]) -> List[str]:
        """构建邻居证明"""
        proof = []
        
        for neighbor in neighbors:
            proof.append(f"{neighbor['relation']}: {neighbor['target']}")
        
        return proof

class AutomatedReasoningEngine:
    """自动化推理引擎主类"""
    
    def __init__(self):
        self.knowledge_base = KnowledgeBase()
        self.forward_engine = ForwardChainingEngine(self.knowledge_base)
        self.backward_engine = BackwardChainingEngine(self.knowledge_base)
        self.resolution_engine = ResolutionEngine(self.knowledge_base)
        self.graph_engine = KnowledgeGraphEngine(self.knowledge_base)
        
        # 初始化示例知识
        self.initialize_sample_knowledge()
        
        logger.info("自动化推理引擎初始化完成")
    
    def initialize_sample_knowledge(self):
        """初始化示例知识"""
        # 添加事实
        self.knowledge_base.add_fact("鸟会飞", 0.9, "常识")
        self.knowledge_base.add_fact("企鹅是鸟", 1.0, "分类学")
        self.knowledge_base.add_fact("企鹅不会飞", 1.0, "观察")
        self.knowledge_base.add_fact("哺乳动物有毛发", 0.95, "生物学")
        self.knowledge_base.add_fact("猫是哺乳动物", 1.0, "分类学")
        
        # 添加规则
        self.knowledge_base.add_rule(Rule(
            name="飞行规则",
            premises=["X是鸟", "X不是企鹅"],
            conclusion="X会飞",
            confidence=0.8,
            description="一般鸟类会飞，但企鹅例外"
        ))
        
        self.knowledge_base.add_rule(Rule(
            name="毛发规则",
            premises=["X是哺乳动物"],
            conclusion="X有毛发",
            confidence=0.95,
            description="哺乳动物都有毛发"
        ))
        
        self.knowledge_base.add_rule(Rule(
            name="猫的毛发",
            premises=["X是猫"],
            conclusion="X有毛发",
            confidence=1.0,
            description="猫有毛发"
        ))
    
    def reason(self, query: str, method: str = "auto") -> ReasoningResult:
        """主推理函数"""
        logger.info(f"开始推理，查询: {query}, 方法: {method}")
        
        if method == "auto":
            # 自动选择推理方法
            method = self.auto_select_method(query)
            logger.info(f"自动选择推理方法: {method}")
        
        if method == ReasoningMethod.FORWARD_CHAINING.value:
            return self.forward_engine.reason()
        elif method == ReasoningMethod.BACKWARD_CHAINING.value:
            return self.backward_engine.reason(query)
        elif method == ReasoningMethod.RESOLUTION.value:
            return self.resolution_engine.reason(query)
        elif method == ReasoningMethod.KNOWLEDGE_GRAPH.value:
            return self.graph_engine.reason(query)
        else:
            return ReasoningResult(
                method=method,
                status="error",
                errors=[f"不支持的推理方法: {method}"]
            )
    
    def auto_select_method(self, query: str) -> str:
        """自动选择推理方法"""
        if "?" in query or "查询" in query:
            return ReasoningMethod.KNOWLEDGE_GRAPH.value
        elif "证明" in query or "推导" in query:
            return ReasoningMethod.BACKWARD_CHAINING.value
        elif "归结" in query or "矛盾" in query:
            return ReasoningMethod.RESOLUTION.value
        else:
            return ReasoningMethod.FORWARD_CHAINING.value
    
    def batch_reason(self, queries: List[str], method: str = "auto") -> List[ReasoningResult]:
        """批量推理"""
        results = []
        
        for i, query in enumerate(queries):
            logger.info(f"推理第 {i+1}/{len(queries)} 个查询")
            result = self.reason(query, method)
            results.append(result)
        
        return results
    
    def add_knowledge(self, facts: List[str] = None, rules: List[Rule] = None):
        """添加知识"""
        if facts:
            for fact in facts:
                self.knowledge_base.add_fact(fact)
        
        if rules:
            for rule in rules:
                self.knowledge_base.add_rule(rule)
        
        logger.info(f"添加了 {len(facts) if facts else 0} 个事实, {len(rules) if rules else 0} 个规则")
    
    def generate_report(self, results: List[ReasoningResult]) -> Dict[str, Any]:
        """生成推理报告"""
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
            "knowledge_base_stats": {
                "facts": len(self.knowledge_base.get_facts()),
                "rules": len(self.knowledge_base.get_rules())
            }
        }
        
        return report

def main():
    """主函数 - 演示自动化推理引擎的使用"""
    engine = AutomatedReasoningEngine()
    
    # 示例1: 前向推理
    print("=== 前向推理示例 ===")
    result1 = engine.reason("", "forward_chaining")
    print(f"推理结果: {result1.status}")
    print(f"新推导的事实数: {result1.details.get('new_facts', 0)}")
    
    # 示例2: 后向推理
    print("\n=== 后向推理示例 ===")
    result2 = engine.reason("企鹅会飞", "backward_chaining")
    print(f"推理结果: {result2.status}")
    if result2.proof_path:
        print("证明路径:")
        for step in result2.proof_path:
            print(f"  {step}")
    
    # 示例3: 归结推理
    print("\n=== 归结推理示例 ===")
    result3 = engine.reason("企鹅会飞", "resolution")
    print(f"推理结果: {result3.status}")
    
    # 示例4: 知识图谱推理
    print("\n=== 知识图谱推理示例 ===")
    result4 = engine.reason("企鹅 鸟 关系", "knowledge_graph")
    print(f"推理结果: {result4.status}")
    if result4.details and "neighbors" in result4.details:
        print("邻居关系:")
        for neighbor in result4.details["neighbors"]:
            print(f"  {neighbor['relation']}: {neighbor['target']}")
    
    # 批量推理
    print("\n=== 批量推理示例 ===")
    queries = ["企鹅会飞", "猫有毛发", "鸟会飞"]
    batch_results = engine.batch_reason(queries)
    
    # 生成报告
    report = engine.generate_report(batch_results)
    print(f"\n推理报告:")
    print(f"总查询数: {report['summary']['total']}")
    print(f"成功数: {report['summary']['successful']}")
    print(f"失败数: {report['summary']['failed']}")
    print(f"错误数: {report['summary']['errors']}")
    print(f"成功率: {report['summary']['success_rate']:.2%}")

if __name__ == "__main__":
    main()
