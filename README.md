# BICMR-ai4math 寒假研讨班第七组：一二三维 Lie 代数分类 (一维、二维)

小组成员：刘谦、胡杨、路原、秦宇轩。

---

### 项目说明

本项目就 Lie 括号的性态完成了对低维 Lie 代数的分类。其中一二维较完善，三维由于工作量过大，尚仅完成了导子代数维数为 0 或 1 维的分类，鉴于此，三维项目与前两种情况分别上传。


### 项目难点

`mathlib4` 的向量以一种抽象的方式定义：向量是从指标集 $\iota$ 到域 $k$ 的映射。这个观点使形式化中遇到的计算几乎不可算：我们没有具体的向量分解公式、判定无关组是基的方法。

Typeclass 中 lean4 无法像人类一样合理推断 instance，造成令人感到奇怪的冲突，例如无法证明 `0 = 0`.

### Zulip

项目完成过程中，我们得到了 Zulip 社区成员的大力帮助，见 [Decomposition of vectors](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Decomposition.20of.20vectors/near/417150187)、[Classification of two-dimensional Lie algebras](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Classification.20of.20two-dimensional.20Lie.20algebras)。

（其中第二个帖子甚至得到了 Kevin Buzzard 的回复）

### 统计

- 一二维情况共 157 行，4 个 `sorry`：繁重的计算、几乎一模一样情况的讨论、让人摸不着头脑的 `mathlib` 定理 (对于新手而言，抽象的定理几乎没法使用，如构造基的定理)。

- 三维情况共 486 行，12 个 `sorry`。

### 感想

~~引用其中一位助教的话：我的建议是不要形式化数学。~~
`Lean4` 实在是太美。