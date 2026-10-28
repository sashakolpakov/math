import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

/-! # Weighted Hermitian -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.WeightedHermitian.Construction

noncomputable section

/-! A positive weighted coordinate pairing constructs a complex inner
product without presupposing any norm on the underlying vector space. -/

universe u v
open scoped BigOperators ComplexConjugate

variable {ι : Type u} [Fintype ι] {V : Type v} [AddCommGroup V] [Module ℂ V]
  (b : Module.Basis ι ℂ V) (w : ι → ℝ)

def weightedHermitian (x y : V) : ℂ :=
  ∑ i, (w i : ℂ) * (conj (b.repr x i) * b.repr y i)

theorem weightedHermitian_self_re (x : V) :
    (weightedHermitian b w x x).re = ∑ i, w i * Complex.normSq (b.repr x i) := by
  unfold weightedHermitian
  simp_rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul]
  simp

theorem weightedHermitian_self_pos (hw : ∀ i, 0 < w i) (x : V) (hx : x ≠ 0) :
    0 < (weightedHermitian b w x x).re := by
  rw [weightedHermitian_self_re]
  have hne : ∃ i, b.repr x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply b.repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using h i
  obtain ⟨i, hi⟩ := hne
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j).le (Complex.normSq_nonneg _))
    ⟨i, Finset.mem_univ i, mul_pos (hw i) (Complex.normSq_pos.mpr hi)⟩

@[instance_reducible]
def weightedHermitianCore (hw : ∀ i, 0 < w i) : InnerProductSpace.Core ℂ V where
  inner := weightedHermitian b w
  conj_inner_symm x y := by
    change conj (weightedHermitian b w y x) = weightedHermitian b w x y
    simp [weightedHermitian, map_sum, mul_comm]
  re_inner_nonneg x := by
    change 0 ≤ (weightedHermitian b w x x).re
    rw [weightedHermitian_self_re]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (Complex.normSq_nonneg _))
  add_left x y z := by
    simp [weightedHermitian, map_add, Finsupp.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  smul_left x y r := by
    change weightedHermitian b w (r • x) y = conj r * weightedHermitian b w x y
    simp [weightedHermitian, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_comm, mul_left_comm]
  definite x hx := by
    by_contra hne
    have hp := weightedHermitian_self_pos b w hw x hne
    change weightedHermitian b w x x = 0 at hx
    rw [hx, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.WeightedHermitian.Construction
