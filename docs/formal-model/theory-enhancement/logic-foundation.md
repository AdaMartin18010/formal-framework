# 逻辑学基础

**本理论与 core-concepts 对应**：本理论支撑 [形式化验证](../core-concepts/formal-verification.md)、[自动推理](../core-concepts/automated-reasoning.md)、[程序验证](../core-concepts/program-verification.md)、[时序逻辑](../core-concepts/temporal-logic.md) 等核心概念中的推理与证明。

## 1. 概述

逻辑学是研究推理和论证的学科，为形式化框架中的推理机制、证明系统和验证方法提供理论基础。本文档详细阐述逻辑学在形式化建模中的应用。

## 2. 基本概念

### 2.1 逻辑的基本概念

#### 2.1.1 逻辑的定义

逻辑是研究有效推理形式的学科，关注从前提推导出结论的正确性。

**形式化定义**：

```text
Logic = (Language, Axioms, Rules, Semantics)
```

其中：

- `Language` 是逻辑语言
- `Axioms` 是公理集合
- `Rules` 是推理规则
- `Semantics` 是语义解释

#### 2.1.2 逻辑的基本性质

- **有效性**：推理形式保证结论的正确性
- **完备性**：所有有效推理都能被形式化
- **一致性**：公理系统不会产生矛盾
- **可判定性**：能够机械地判断推理的有效性

### 2.2 命题逻辑

#### 2.2.1 命题

命题是可以判断真假的陈述句。

**形式化定义**：

```text
Proposition = {p | p ∈ AtomicPropositions ∨ 
              p = ¬q ∨ p = q ∧ r ∨ p = q ∨ r ∨ p = q → r ∨ p = q ↔ r}
```

#### 2.2.2 逻辑连接词

- **否定**：`¬p`（非p）
- **合取**：`p ∧ q`（p且q）
- **析取**：`p ∨ q`（p或q）
- **蕴含**：`p → q`（如果p则q）
- **等价**：`p ↔ q`（p当且仅当q）

### 2.3 一阶逻辑

#### 2.3.1 量词

- **全称量词**：`∀x • P(x)`（对所有x，P(x)成立）
- **存在量词**：`∃x • P(x)`（存在x，使得P(x)成立）

#### 2.3.2 谓词

谓词是描述对象性质的函数。

```text
Predicate = {P | P : Domain → Bool}
```

## 3. 在形式化建模中的应用

### 3.1 模型约束表达

#### 3.1.1 约束逻辑

模型约束可以表示为逻辑公式：

```text
ModelConstraint = ∀x : Model • Constraint(x)
```

#### 3.1.2 关系约束

模型间关系的约束：

```text
RelationshipConstraint = ∀x, y : Model • 
  Related(x, y) ⇒ (Property(x) ∧ Property(y))
```

### 3.2 推理机制

#### 3.2.1 自动推理

基于逻辑规则的自动推理：

```text
AutoReasoning = (Premises, Rules) ⊢ Conclusion
```

#### 3.2.2 证明系统

形式化证明的构造：

```text
ProofSystem = (Axioms, InferenceRules, Proofs)
```

### 3.3 验证逻辑

#### 3.3.1 模型验证

验证模型是否满足规格：

```text
ModelVerification = Model ⊨ Specification
```

#### 3.3.2 性质验证

验证模型是否满足特定性质：

```text
PropertyVerification = Model ⊨ Property
```

## 4. 形式化规格

### 4.1 Z Notation规格

#### 4.1.1 基本逻辑定义

```z
[Proposition, Predicate]
LogicSystem ::= language : P Proposition
               axioms : P Proposition
               rules : P InferenceRule
               semantics : Interpretation

∀ l : LogicSystem •
  (∀ p : l.axioms • p ∈ l.language) ∧
  (∀ r : l.rules • r.input ⊆ l.language ∧ r.output ⊆ l.language)
```

#### 4.1.2 推理规则规格

```z
InferenceRule ::= input : P Proposition
                 output : Proposition
                 condition : Predicate

ValidInference : LogicSystem × InferenceRule → Bool
∀ l : LogicSystem; r : InferenceRule •
  ValidInference(l, r) = 
    r.input ⊆ l.language ∧ r.output ∈ l.language ∧
    (∀ p : r.input • l.axioms(p) ∨ ∃r' : l.rules • r'.output = p)
```

### 4.2 逻辑公理

#### 4.2.1 命题逻辑公理

- **同一律**：`p → p`
- **排中律**：`p ∨ ¬p`
- **矛盾律**：`¬(p ∧ ¬p)`
- **双重否定**：`¬¬p ↔ p`

#### 4.2.2 一阶逻辑公理

- **全称实例化**：`∀x • P(x) → P(a)`
- **存在概括**：`P(a) → ∃x • P(x)`
- **等词公理**：`a = a` 和 `a = b → (P(a) ↔ P(b))`

## 5. 在框架中的具体应用

### 5.1 抽象语法树验证

#### 5.1.1 语法正确性

验证AST的语法正确性：

```text
SyntaxCorrectness = ∀node : AST • ValidSyntax(node)
```

#### 5.1.2 结构完整性

验证AST的结构完整性：

```text
StructuralIntegrity = ∀node : AST • 
  HasValidParent(node) ∧ HasValidChildren(node)
```

### 5.2 领域特定语言验证

#### 5.2.1 语法规则验证

验证DSL语法规则的一致性：

```text
GrammarConsistency = ∀rule1, rule2 : GrammarRule • 
  ¬(rule1.conflicts(rule2))
```

#### 5.2.2 语义规则验证

验证DSL语义规则的正确性：

```text
SemanticCorrectness = ∀rule : SemanticRule • 
  rule.input ⊨ rule.output
```

### 5.3 形式化验证系统

#### 5.3.1 模型检查

使用逻辑验证模型性质：

```text
ModelChecking = Check(Model, Property) = 
  if Model ⊨ Property then Valid else CounterExample
```

#### 5.3.2 定理证明

构造形式化证明：

```text
TheoremProving = Prove(Conjecture) = 
  ConstructProof(Axioms, Rules, Conjecture)
```

## 6. 高级逻辑概念

### 6.1 模态逻辑

#### 6.1.1 模态算子

- **必然性**：`□p`（必然p）
- **可能性**：`◇p`（可能p）

#### 6.1.2 在系统建模中的应用

```text
SystemProperty = □(SafeState → □SafeState)
```

### 6.2 时序逻辑

#### 6.2.1 时序算子

- **总是**：`G p`（总是p）
- **最终**：`F p`（最终p）
- **下一个**：`X p`（下一个时刻p）
- **直到**：`p U q`（p直到q）

#### 6.2.2 在并发系统中的应用

```text
LivenessProperty = G(request → F response)
SafetyProperty = G(¬(critical1 ∧ critical2))
```

### 6.3 直觉逻辑

#### 6.3.1 构造性证明

直觉逻辑强调构造性证明：

```text
ConstructiveProof = ∀p • (p ∨ ¬p) → (p ∨ ¬p)
```

#### 6.3.2 在程序验证中的应用

```text
ProgramCorrectness = ∀input • ∃output • 
  Program(input) = output ∧ Specification(input, output)
```

## 7. 逻辑系统实现

### 7.1 命题逻辑求解器

#### 7.1.1 真值表方法

```python
def truth_table_solver(proposition):
    variables = extract_variables(proposition)
    truth_table = generate_truth_table(variables)
    
    for assignment in truth_table:
        if not evaluate(proposition, assignment):
            return False, assignment  # 反例
    return True, None  # 永真
```

#### 7.1.2 DPLL算法

```python
def dpll_solver(clauses):
    if not clauses:
        return True
    if [] in clauses:
        return False
    
    # 单元传播
    unit_clauses = [c for c in clauses if len(c) == 1]
    if unit_clauses:
        literal = unit_clauses[0][0]
        return dpll_solver(unit_propagate(clauses, literal))
    
    # 选择变量
    variable = choose_variable(clauses)
    return (dpll_solver(clauses + [[variable]]) or 
            dpll_solver(clauses + [[-variable]]))
```

### 7.2 一阶逻辑求解器

#### 7.2.1 归结推理

```python
def resolution_prover(axioms, goal):
    clauses = cnf_conversion(axioms + [negate(goal)])
    
    while True:
        new_clauses = []
        for i, clause1 in enumerate(clauses):
            for clause2 in clauses[i+1:]:
                resolvent = resolve(clause1, clause2)
                if resolvent == []:  # 空子句
                    return True  # 证明成功
                if resolvent not in clauses:
                    new_clauses.append(resolvent)
        
        if not new_clauses:
            return False  # 无法证明
        
        clauses.extend(new_clauses)
```

### 7.3 模型检查器

#### 7.3.1 状态空间搜索

```python
def model_checker(model, property):
    initial_states = model.initial_states
    visited = set()
    queue = [(state, []) for state in initial_states]
    
    while queue:
        state, path = queue.pop(0)
        
        if state in visited:
            continue
        visited.add(state)
        
        # 检查性质
        if not property.check(state):
            return False, path  # 反例路径
        
        # 扩展后继状态
        for next_state in model.successors(state):
            if next_state not in visited:
                queue.append((next_state, path + [state]))
    
    return True, None  # 性质满足
```

## 8. 数学性质

### 8.1 逻辑系统的性质

#### 8.1.1 可靠性

逻辑系统是可靠的：

```text
Soundness = ∀Proof • (Axioms ⊢ Proof) ⇒ (Axioms ⊨ Proof)
```

#### 8.1.2 完备性

逻辑系统是完备的：

```text
Completeness = ∀Formula • (Axioms ⊨ Formula) ⇒ (Axioms ⊢ Formula)
```

#### 8.1.3 一致性

逻辑系统是一致的：

```text
Consistency = ¬(Axioms ⊢ ⊥)
```

### 8.2 逻辑运算的性质

#### 8.2.1 德摩根律

- `¬(p ∧ q) ↔ ¬p ∨ ¬q`
- `¬(p ∨ q) ↔ ¬p ∧ ¬q`

#### 8.2.2 分配律

- `p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)`
- `p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)`

#### 8.2.3 蕴含的性质

- `p → q ↔ ¬p ∨ q`
- `¬(p → q) ↔ p ∧ ¬q`

## 9. 证明技术

### 9.1 自然演绎

#### 9.1.1 引入规则

- **合取引入**：从 `p` 和 `q` 推出 `p ∧ q`
- **析取引入**：从 `p` 推出 `p ∨ q`
- **蕴含引入**：从假设 `p` 推出 `q`，然后推出 `p → q`

#### 9.1.2 消除规则

- **合取消除**：从 `p ∧ q` 推出 `p` 或 `q`
- **析取消除**：从 `p ∨ q` 和 `p → r` 和 `q → r` 推出 `r`
- **蕴含消除**：从 `p → q` 和 `p` 推出 `q`

### 9.2 归结证明

#### 9.2.1 归结规则

从 `p ∨ q` 和 `¬p ∨ r` 推出 `q ∨ r`

#### 9.2.2 归结证明示例

证明 `p → q, q → r ⊢ p → r`：

```text
1. ¬p ∨ q          (前提1的等价形式)
2. ¬q ∨ r          (前提2的等价形式)
3. p               (假设)
4. q               (从1和3归结)
5. r               (从2和4归结)
6. p → r           (蕴含引入)
```

### 9.3 构造性证明

#### 9.3.1 存在性证明

通过构造对象证明存在性：

```text
Theorem: 存在无限多个素数
Proof: 构造素数序列 p₁, p₂, p₃, ...
       p₁ = 2
       p_{n+1} = p₁ × p₂ × ... × p_n + 1
```

#### 9.3.2 算法构造

通过构造算法证明可计算性：

```text
Theorem: 排序问题是可计算的
Proof: 构造快速排序算法
```

## 10. 实际应用案例

### 10.1 软件验证

#### 10.1.1 程序正确性

验证程序的正确性：

```text
ProgramCorrectness = ∀input • 
  Precondition(input) → 
  (Program(input) = output ∧ Postcondition(input, output))
```

#### 10.1.2 循环不变式

验证循环的不变式：

```text
LoopInvariant = Invariant(initial) ∧
  (Invariant(i) ∧ Condition(i) → Invariant(Next(i))) ∧
  (Invariant(i) ∧ ¬Condition(i) → FinalCondition(i))
```

### 10.2 系统建模

#### 10.2.1 状态机验证

验证状态机的性质：

```text
StateMachineProperty = G(State1 → X(State2 ∨ State3))
```

#### 10.2.2 并发系统验证

验证并发系统的安全性：

```text
MutualExclusion = G(¬(Critical1 ∧ Critical2))
```

### 10.3 数据库系统

#### 10.3.1 完整性约束

验证数据库的完整性约束：

```text
ReferentialIntegrity = ∀r : Record • 
  ForeignKey(r) → ∃r' : Record • PrimaryKey(r') = ForeignKey(r)
```

#### 10.3.2 事务一致性

验证事务的一致性：

```text
TransactionConsistency = ∀t : Transaction • 
  Begin(t) → (Commit(t) ∨ Abort(t))
```

## 11. 国际标准对标

### 11.1 逻辑标准

#### 11.1.1 ISO 80000-2

数学符号和表达式的国际标准，包含逻辑符号的定义。

#### 11.1.2 IEEE 1850

属性规格语言标准，基于时序逻辑。

### 11.2 形式化方法标准

#### 11.2.1 Z Notation

形式化规格语言，基于一阶逻辑和集合论。

#### 11.2.2 VDM

维也纳开发方法，基于一阶逻辑。

## 12. 大学课程参考

### 12.1 本科课程

#### 12.1.1 离散数学

- 命题逻辑
- 一阶逻辑
- 证明技术

#### 12.1.2 数理逻辑

- 形式逻辑系统
- 证明论
- 模型论

### 12.2 研究生课程

#### 12.2.1 逻辑学

- 模态逻辑
- 时序逻辑
- 直觉逻辑

#### 12.2.2 形式化方法

- 程序验证
- 模型检查
- 定理证明

## 13. 参考文献

### 13.1 经典教材

1. Enderton, H. B. (2001). *A Mathematical Introduction to Logic*. Academic Press.
2. Mendelson, E. (2009). *Introduction to Mathematical Logic*. Chapman & Hall.
3. van Dalen, D. (2013). *Logic and Structure*. Springer.

### 13.2 形式化方法

1. Spivey, J. M. (1992). *The Z Notation: A Reference Manual*. Prentice Hall.
2. Woodcock, J., & Davies, J. (1996). *Using Z: Specification, Refinement, and Proof*. Prentice Hall.

### 13.3 计算机科学

1. Huth, M., & Ryan, M. (2004). *Logic in Computer Science: Modelling and Reasoning about Systems*. Cambridge University Press.
2. Clarke, E. M., Grumberg, O., & Peled, D. A. (1999). *Model Checking*. MIT Press.

## 与标准/课程对照要点

- **L2/L3 映射**：本理论支撑 L2/L3 形式化规格、验证与 L3_D08；对象/属性/不变式对齐见 [AUTHORITY_STANDARD_COURSE_L2L3_MATRIX](../../reference/AUTHORITY_STANDARD_COURSE_L2L3_MATRIX.md)。
- **标准与课程**：逻辑与形式化验证相关标准（TLA+、Alloy、Z 等）及名校课程（Stanford CS 256/357S、CMU 15-311/15-414、Berkeley EECS 219C 等）见 [AUTHORITY_ALIGNMENT_INDEX](../../reference/AUTHORITY_ALIGNMENT_INDEX.md) 第 2–3 节。

**参见（对应 core-concepts）**：[形式化验证](../core-concepts/formal-verification.md)、[自动推理](../core-concepts/automated-reasoning.md)、[时序逻辑](../core-concepts/temporal-logic.md)。

---

## 附录

### A. 符号表

| 符号 | 含义 | 示例 |
|------|------|------|
| ¬ | 否定 | ¬p |
| ∧ | 合取 | p ∧ q |
| ∨ | 析取 | p ∨ q |
| → | 蕴含 | p → q |
| ↔ | 等价 | p ↔ q |
| ∀ | 全称量词 | ∀x • P(x) |
| ∃ | 存在量词 | ∃x • P(x) |
| ⊨ | 语义蕴含 | A ⊨ B |
| ⊢ | 语法推导 | A ⊢ B |

### B. 常用定理

1. **德摩根律**：`¬(p ∧ q) ↔ ¬p ∨ ¬q`
2. **分配律**：`p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)`
3. **蕴含等价**：`p → q ↔ ¬p ∨ q`
4. **双重否定**：`¬¬p ↔ p`

### C. 练习题目

1. 证明：`p → q, q → r ⊢ p → r`
2. 证明：`¬(p ∧ q) ↔ ¬p ∨ ¬q`
3. 证明：`p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)`
4. 构造：一个简单的逻辑推理系统
