import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Span
open FiniteDimensional

variable [Field K] [LieRing L] [LieAlgebra K L]

@[simp]
---x.repr is the linear equivalence sending a vector x to
---its coordinates: the cs such that x = ∑ i, c i.
---suppose x = ∑ b i ×  i (b i 是基向量, i 是系数)
---通俗易懂地说,b.repr x,是指送一个向量x给repr,返回在基底b下的坐标,如b.repr x 0
theorem decompose (b : Basis (Fin 1) K L) :
    ∀ (v : L), v = (b.repr v 0) • (b 0) := by
  intro v
  nth_rewrite 1 [← b.total_repr v]
  have hsubset : (b.repr v).support ⊆ {0} := by ----指标集的支集(support)是{0}的子集,也即∅ 或者{0}本身
    intro x _
    rewrite [Finset.mem_singleton]
    exact Fin.eq_zero x
  have hzero : ∀ x ∈ ({0} : Finset (Fin 1)), x ∉ (b.repr v).support → (b.repr v) x • b x = 0 := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    rw [hi, Finsupp.mem_support_iff.not, not_ne_iff]
    intro hc
    rw [hc]
    exact zero_smul K (b 0)
  rw [Finsupp.total_apply, Finsupp.sum, Finset.sum_subset hsubset hzero,---一步一步利用rw改写
   Finset.sum_singleton]


theorem one_dim (b : Basis (Fin 1) K L) : ∀ x y : L, ⁅x, y⁆ = 0 := by
  intro x y
  have x_decom : x = (b.repr x 0) • (b 0) := by exact decompose b x
  have y_decom : y = (b.repr y 0) • (b 0) := by exact decompose b y
  rw [x_decom, y_decom]
  ---∀ x : L , we have ⁅x , x⁆ == 0.
  simp




theorem decompose2 (b : Basis (Fin 2) K L) :
  ∀ x : L, x = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := sorry

theorem two_dim (b : Basis (Fin 2) K L) :
  (∀ x y : L, ⁅x, y⁆ = 0) ∨ ∃ base : Basis (Fin 2) K L, ⁅base 0, base 1⁆ = base 1 := by
    by_cases h : ∀ x y : L, ⁅x, y⁆ = 0
    · left
      exact h
    -- 上述讨论排除了平凡情况
    · right
      by_contra nexist  -- 我们可以构造一组基与 `nexsit` 矛盾，由爆炸原理证明命题
      let ω := ⁅b 0, b 1⁆
      have ωeq : ω = ⁅b 0, b 1⁆ := by simp
      have nontri : ω ≠ 0 := by
        intro p
        apply h
        intro x y
        have decom_x : x = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := by apply decompose2 b x
        have decom_y : y = (b.repr y 0) • b 0 + (b.repr y 1) • b 1 := by apply decompose2 b y
        rw [decom_x, decom_y]
        simp
        have definition : ⁅b 1, b 0⁆ = -⁅b 0, b 1⁆ := by simp
        rw [ωeq] at p
        rw [definition, p]
        simp
      have decomposition :  ω = (b.repr ω 0) • b 0 + (b.repr ω 1) • b 1 := by
        apply decompose2 b ω
      by_cases case : b.repr ω 1 = 0
      · sorry  -- similar to the other one.
      push_neg at case
      let β₀ := (b.repr ω 1)⁻¹ • (b 0)
      let β₁ := ω
      have key : ⁅β₀, β₁⁆ = β₁ := by
        have : β₁ = ω := by simp
        rw [this, decomposition]
        have : β₀ = (b.repr ω 1)⁻¹ • (b 0) := by simp
        rw [this]
        calc
          ⁅((b.repr ω) 1)⁻¹ • b 0, (b.repr ω) 0 • b 0 + (b.repr ω) 1 • b 1⁆ = ⁅((b.repr ω) 1)⁻¹ • b 0, (b.repr ω) 0 • b 0⁆ + ⁅((b.repr ω) 1)⁻¹ • b 0, (b.repr ω) 1 • b 1⁆ := by simp
          _ = 0 + ⁅((b.repr ω) 1)⁻¹ • b 0, (b.repr ω) 1 • b 1⁆ := by simp
          _ = ⁅((b.repr ω) 1)⁻¹ • b 0, (b.repr ω) 1 • b 1⁆ := by simp
          _ = ((b.repr ω) 1)⁻¹ • ⁅b 0, (b.repr ω) 1 • b 1⁆ := by
            exact smul_lie ((b.repr ω) 1)⁻¹ (b 0) ((b.repr ω) 1 • b 1)
          _ = ((b.repr ω) 1)⁻¹ • ((b.repr ω) 1) • ⁅b 0, b 1⁆ := by
            have fuck : ⁅b 0, (b.repr ω) 1 • b 1⁆ = (b.repr ω) 1 • ⁅b 0, b 1⁆ := by simp
            rw [fuck]
          _ = ⁅b 0, b 1⁆ := by
            have fuck : ((b.repr ω) 1)⁻¹ * (b.repr ω) 1 = 1 := by
              exact inv_mul_cancel case
            have you : ((b.repr ω) 1)⁻¹ • (b.repr ω) 1 • ⁅b 0, b 1⁆ = (((b.repr ω) 1)⁻¹ * (b.repr ω) 1) • ⁅b 0, b 1⁆ := by
              exact smul_smul ((b.repr ω) 1)⁻¹ ((b.repr ω) 1) ⁅b 0, b 1⁆
            rw [you, fuck]
            simp
          _ = (b.repr ω) 0 • b 0 + (b.repr ω) 1 • b 1 := by
            rw [← decomposition]
      apply nexist
      let v : (Fin 2) -> L := fun i => match i with
        | 0 => β₀
        | 1 => β₁
      have v0_eq_β₀ : v 0 = β₀ := by rfl
      have v1_eq_β₁ : v 1 = β₁ := by rfl
      let hli : LinearIndependent K v := by
        apply linearIndependent_fin2.2
        constructor
        · rw [v1_eq_β₁]
          exact nontri
        · intro a
          rw [v1_eq_β₁, v0_eq_β₀]
          simp
          intro neq
          apply nontri
          simp
          have eq1 : ((b.repr ω) 1) • a • ⁅b 0, b 1⁆ = b 0 :=
            calc
              ((b.repr ω) 1) • a • ⁅b 0, b 1⁆ = ((b.repr ω) 1) • ((b.repr ⁅b 0, b 1⁆) 1)⁻¹ • b 0 := by rw [neq]
              _ = ((b.repr ω) 1) • ((b.repr ω) 1)⁻¹ • b 0 := by rw [← ωeq]
              _ = (((b.repr ω) 1) * ((b.repr ω) 1)⁻¹) • b 0 := by exact smul_smul ((b.repr ω) 1) ((b.repr ω) 1)⁻¹ (b 0)
              _ = 1 • b 0 := by
                have : ((b.repr ω) 1) * ((b.repr ω) 1)⁻¹ = 1 := by exact mul_inv_cancel case
                rw [this]
                simp
              _ = b 0 := by exact one_nsmul (b 0)
          have eq2 : b 0 = ((b.repr ω) 1) • a • ((b.repr ω) 0 • b 0 + (b.repr ω) 1 • b 1) :=
            calc
              b 0 = ((b.repr ω) 1) • a • ⁅b 0, b 1⁆ := eq1.symm
              _ = ((b.repr ω) 1) • a • ((b.repr ω) 0 • b 0 + (b.repr ω) 1 • b 1) := by rw [← ωeq, ← decomposition]
          have : a ≠ 0 := by
            intro aeq
            rw [aeq] at eq2
            simp at eq2
            apply Basis.ne_zero b 0
            exact eq2
          have eq3 : b 1 = ((b.repr ω) 1)⁻¹ • (((b.repr ω) 1)⁻¹ * a - (b.repr ω) 0) • b 0 := by
            sorry  -- these calculus is similar to the other one.
          rw [eq3]
          simp
      have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
        sorry
      let β : Basis (Fin 2) K L := by
        apply Basis.mk
        pick_goal 3
        · exact v
        exact hli
        exact hsp
      use β
      have : β 0 = β₀ := by
        rw [← v0_eq_β₀]
        simp
      rw [this]
      have : β 1 = β₁ := by
        rw [← v1_eq_β₁]
        simp
      rw [this]
      assumption
