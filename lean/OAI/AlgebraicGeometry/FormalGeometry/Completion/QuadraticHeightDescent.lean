import Mathlib.GroupTheory.Descent
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! # Quadratic Height Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticHeightDescent.Construction

noncomputable section

/-! A discrete positive quadratic height and finite reductions imply finite generation.
This is the arithmetic descent step; constructing the geometric height is a separate obligation. -/

universe u

variable {G : Type u} [AddCommGroup G]

/-- The quantitative properties required of an integral positive quadratic height. -/
structure DiscreteQuadraticHeight (G : Type u) [AddCommGroup G] where
  value : G → ℝ
  zero : value 0 = 0
  positive : ∀ x, x ≠ 0 → 1 ≤ value x
  parallelogram : ∀ x y, value (x + y) + value (x - y) = 2 * (value x + value y)

namespace DiscreteQuadraticHeight

variable (h : DiscreteQuadraticHeight G)

theorem nonneg (x : G) : 0 ≤ h.value x := by
  by_cases hx : x = 0
  · rw [hx, h.zero]
  · exact le_trans (by norm_num) (h.positive x hx)

theorem nsmul (n : ℕ) (x : G) : h.value (n • x) = (n : ℝ) ^ 2 * h.value x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [h.zero]
  | one => simp
  | more n hn hn1 =>
    have hp := h.parallelogram ((n + 1) • x) x
    have hadd : (n + 1) • x + x = (n + 2) • x := by simp [add_nsmul, two_nsmul, add_assoc]
    have hsub : (n + 1) • x - x = n • x := by simp [add_nsmul]
    rw [hadd, hsub, hn, hn1] at hp
    push_cast at hp ⊢
    nlinarith

theorem sub_le (x y : G) : h.value (x - y) ≤ 2 * h.value x + 2 * h.value y := by
  have hp := h.parallelogram x y
  have hn := h.nonneg (x + y)
  linarith

/-- A sufficiently deep finite reduction separates every bounded-height set. -/
theorem northcott_of_finite_reductions (n : ℕ) (hn : 2 ≤ n)
    (hfinite : ∀ r : ℕ,
      Finite (G ⧸ (nsmulAddMonoidHom (n ^ r) : G →+ G).range)) : Northcott h.value := by
  constructor
  intro B
  have hnR : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (max (4 * B) 1) hnR
  have hN : 1 < ((n ^ r : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact lt_of_le_of_lt (le_max_right _ _) hr
  have hB : 4 * B < ((n ^ r : ℕ) : ℝ) ^ 2 := by
    have hle : 4 * B < ((n ^ r : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
      exact lt_of_le_of_lt (le_max_left _ _) hr
    nlinarith
  have := hfinite r
  let q : G → G ⧸ (nsmulAddMonoidHom (n ^ r) : G →+ G).range := QuotientAddGroup.mk
  have hi : Function.Injective (fun x : {x : G // h.value x ≤ B} => q x.val) := by
    intro x y he
    apply Subtype.ext
    by_contra hxy
    have hm : x.val - y.val ∈ (nsmulAddMonoidHom (n ^ r) : G →+ G).range :=
      QuotientAddGroup.eq_iff_sub_mem.mp he
    obtain ⟨z, hz⟩ := hm
    change (n ^ r) • z = x.val - y.val at hz
    have hz0 : z ≠ 0 := by
      intro hzero
      rw [hzero, smul_zero] at hz
      exact hxy (sub_eq_zero.mp hz.symm)
    have hp := h.positive z hz0
    have hs := h.nsmul (n ^ r) z
    rw [hz] at hs
    have hu := h.sub_le x.val y.val
    have hx := x.property
    have hy := y.property
    have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (((n ^ r : ℕ) : ℝ)))
    nlinarith
  have : Finite {x : G // h.value x ≤ B} := Finite.of_injective _ hi
  exact Set.finite_coe_iff.mpr this

include h in
/-- The same finite reductions and height supply a finite set of additive generators. -/
theorem finiteGenerated_of_finite_reductions (n : ℕ) (hn : 2 ≤ n)
    (hfinite : ∀ r : ℕ,
      Finite (G ⧸ (nsmulAddMonoidHom (n ^ r) : G →+ G).range)) : AddGroup.FG G := by
  have : Northcott h.value := h.northcott_of_finite_reductions n hn hfinite
  have : Finite (G ⧸ (nsmulAddMonoidHom n : G →+ G).range) := by
    simpa only [pow_one] using hfinite 1
  have hf : (nsmulAddMonoidHom n : G →+ G).range.FiniteIndex :=
    AddSubgroup.finiteIndex_of_finite_quotient
  have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hab : (2 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
  refine AddCommGroup.fg_of_descent (n := n) (h := h.value) (a := 2) (b := (n : ℝ) ^ 2)
    (c₀ := 0) (c := fun g => 2 * h.value g) (by norm_num) hab hf ?_ ?_
  · intro g x
    have hx : (g + x) - g = x := by abel
    simpa only [hx] using h.sub_le (g + x) g
  · intro x
    rw [h.nsmul, sub_zero]

end DiscreteQuadraticHeight

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticHeightDescent.Construction
