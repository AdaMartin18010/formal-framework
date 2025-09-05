# 数学基础

## 📋 概述

正式验证框架基于坚实的数学基础，包括集合论、逻辑学、图论和概率论等数学分支。

## 🔢 核心数学概念

### 1. 集合论 (Set Theory)

#### 基本概念

- **集合**：具有某种性质的对象的全体
- **元素**：集合中的对象
- **子集**：一个集合的所有元素都属于另一个集合
- **并集**：两个集合中所有元素的集合
- **交集**：两个集合中共同元素的集合

#### 形式化定义

```text
集合 A = {x | P(x)}  // P(x) 是性质谓词
A ⊆ B ⇔ ∀x(x ∈ A → x ∈ B)  // A 是 B 的子集
A ∪ B = {x | x ∈ A ∨ x ∈ B}  // A 和 B 的并集
A ∩ B = {x | x ∈ A ∧ x ∈ B}  // A 和 B 的交集
```

#### 应用场景

- **状态空间**：系统所有可能状态的集合
- **输入输出**：系统输入输出的集合
- **属性集合**：系统属性的集合

### 2. 逻辑学 (Logic)

#### 2.1 命题逻辑

- **命题**：可以判断真假的陈述
- **逻辑连接词**：¬（非）、∧（与）、∨（或）、→（蕴含）、↔（等价）
- **真值表**：描述逻辑连接词的真值

#### 2.2 谓词逻辑

- **谓词**：描述对象性质的函数
- **量词**：∀（全称量词）、∃（存在量词）
- **变元**：可以取不同值的符号

#### 2.3 形式化定义

```text
命题逻辑公式：
φ ::= p | ¬φ | φ ∧ ψ | φ ∨ ψ | φ → ψ | φ ↔ ψ

谓词逻辑公式：
φ ::= P(x₁,...,xₙ) | ¬φ | φ ∧ ψ | φ ∨ ψ | φ → ψ | ∀x φ | ∃x φ
```

#### 2.4 应用场景

- **系统规范**：描述系统行为的逻辑公式
- **不变式**：系统状态中始终为真的条件
- **前置条件**：操作执行前必须满足的条件
- **后置条件**：操作执行后必须满足的条件

### 3. 图论 (Graph Theory)

#### 3.1 基本概念

- **图**：由顶点和边组成的结构
- **有向图**：边有方向的图
- **无向图**：边没有方向的图
- **路径**：顶点序列，相邻顶点间有边
- **环**：起点和终点相同的路径

#### 3.2 形式化定义

```text
图 G = (V, E)
V: 顶点集合
E: 边集合

有向图：E ⊆ V × V
无向图：E ⊆ {{u,v} | u,v ∈ V, u ≠ v}
```

#### 3.3 应用场景

- **状态转换图**：系统状态间的转换关系
- **依赖图**：组件间的依赖关系
- **控制流图**：程序执行的控制流
- **数据流图**：数据在系统中的流动

### 4. 概率论 (Probability Theory)

#### 4.1 基本概念

- **样本空间**：所有可能结果的集合
- **事件**：样本空间的子集
- **概率**：事件发生的可能性度量
- **随机变量**：将样本空间映射到实数的函数

#### 4.2 形式化定义

```text
概率空间 (Ω, F, P)
Ω: 样本空间
F: 事件集合（σ-代数）
P: 概率测度

概率公理：
1. P(A) ≥ 0 对所有 A ∈ F
2. P(Ω) = 1
3. 对互不相容事件 A₁, A₂, ...：P(∪ᵢAᵢ) = ΣᵢP(Aᵢ)
```

#### 4.3 应用场景

- **可靠性分析**：系统故障的概率
- **性能分析**：系统性能的概率分布
- **随机算法**：基于概率的算法分析
- **蒙特卡洛方法**：基于随机采样的验证方法

## 🧮 数学方法

### 1. 形式化方法

#### 模型检查 (Model Checking)

- **有限状态机**：描述系统行为的状态机
- **时序逻辑**：描述时间相关性质的逻辑
- **不动点计算**：计算系统的不变性质

#### 定理证明 (Theorem Proving)

- **公理化方法**：基于公理和推理规则
- **自然演绎**：基于自然推理规则
- **归结原理**：基于归结的自动推理

#### 抽象解释 (Abstract Interpretation)

- **抽象域**：抽象值的集合
- **抽象函数**：具体值到抽象值的映射
- **不动点计算**：计算抽象语义的不动点

### 2. 算法分析

#### 时间复杂度

- **大O记号**：描述算法时间复杂度的上界
- **递归关系**：描述递归算法的时间复杂度
- **主定理**：求解递归关系的方法

#### 空间复杂度

- **空间使用**：算法使用的内存空间
- **空间优化**：减少空间使用的方法
- **空间-时间权衡**：空间和时间之间的权衡

### 3. 数值方法

#### 数值分析

- **数值稳定性**：数值计算的稳定性
- **误差分析**：数值计算的误差分析
- **收敛性**：数值方法的收敛性

#### 优化方法

- **线性规划**：线性约束下的优化
- **非线性规划**：非线性约束下的优化
- **整数规划**：整数约束下的优化

## 📊 数学工具

### 1. 证明助手

#### Coq

```coq
(* Coq 证明示例 *)
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
```

#### Isabelle/HOL

```isabelle
(* Isabelle/HOL 证明示例 *)
lemma plus_comm: "n + m = m + (n::nat)"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed
```

#### Lean

```lean
-- Lean 证明示例
theorem plus_comm (n m : ℕ) : n + m = m + n :=
begin
  induction n with n ih,
  { simp },
  { simp [ih] }
end
```

### 2. 模型检查器

#### SPIN

```promela
/* SPIN 模型示例 */
active proctype P() {
    int x = 0;
    do
    :: x < 10 -> x++
    :: x >= 10 -> break
    od;
    assert(x == 10)
}
```

#### TLA+

```tla
(* TLA+ 规范示例 *)
VARIABLES x, y
TypeOK == x \in Nat /\ y \in Nat
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + 1
Spec == Init /\ [][Next]_<<x,y>>
```

#### UPPAAL

```xml
<!-- UPPAAL 模型示例 -->
<template>
  <name>Process</name>
  <parameter>int id</parameter>
  <location id="id0">
    <name>Start</name>
  </location>
  <location id="id1">
    <name>End</name>
  </location>
  <transition>
    <source ref="id0"/>
    <target ref="id1"/>
    <label kind="guard">x < 10</label>
    <label kind="assignment">x++</label>
  </transition>
</template>
```

### 3. 数值计算工具

#### MATLAB

```matlab
% MATLAB 数值计算示例
function result = solve_ode()
    tspan = [0 10];
    y0 = 0;
    [t, y] = ode45(@(t,y) -2*y, tspan, y0);
    plot(t, y);
    result = y(end);
end
```

#### Python (NumPy/SciPy)

```python
# Python 数值计算示例
import numpy as np
from scipy.integrate import odeint

def model(y, t):
    return -2 * y

t = np.linspace(0, 10, 100)
y0 = 0
y = odeint(model, y0, t)
```

## 🔗 相关文档

- [理论基础概览](README.md)
- [形式化方法](formal-methods.md)
- [验证原理](verification-principles.md)
- [参考文献](references/)

---

*最后更新：2024-12-19*-
