import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Cycle Linear Expansion -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleLinearExpansion

noncomputable section

/-! Finite support expansions retain the original supports when an
intersection is evaluated or composed with another intersection. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem linear_sum {α M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : (α →₀ ℚ) →ₗ[ℚ] M) (a : α →₀ ℚ) :
    f a = ∑ A ∈ a.support, a A • f (Finsupp.single A 1) := by
  calc
    f a = f (a.sum Finsupp.single) := congrArg f (Finsupp.sum_single a).symm
    _ = ∑ A ∈ a.support, f (Finsupp.single A (a A)) := by rw [Finsupp.sum, map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      have hs : Finsupp.single A (a A) = a A • Finsupp.single A 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul]

theorem bilinear_sum {α β M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : (α →₀ ℚ) →ₗ[ℚ] (β →₀ ℚ) →ₗ[ℚ] M) (a : α →₀ ℚ) (b : β →₀ ℚ) :
    f a b = ∑ A ∈ a.support, ∑ B ∈ b.support,
      (a A * b B) • f (Finsupp.single A 1) (Finsupp.single B 1) := by
  rw [show f a b = f.flip b a from rfl, linear_sum]
  apply Finset.sum_congr rfl
  intro A _
  change a A • f (Finsupp.single A 1) b = _
  rw [linear_sum (f (Finsupp.single A 1)) b, Finset.smul_sum]
  simp only [smul_smul]

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

theorem intersection (p q : ℕ) (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    Supports.ProperCycle.intersectionBilinear X m p q a b = ∑ A ∈ a.support, ∑ B ∈ b.support,
      (a A * b B) • Supports.ProperCycle.pairCycle X m p q A B := by
  rw [bilinear_sum]
  simp only [Supports.ProperCycle.intersectionBilinear, Finsupp.linearCombination_single, one_smul]

theorem nested (p q t : ℕ) (a : X.RationalDimensionCycle p)
    (b : X.RationalDimensionCycle q) (c : X.RationalDimensionCycle t) :
    Supports.ProperCycle.intersectionBilinear X m (p + q) t (Supports.ProperCycle.intersectionBilinear X m p q a b) c =
      ∑ A ∈ a.support, ∑ B ∈ b.support, ∑ D ∈ c.support,
        (a A * b B * c D) • Supports.ProperCycle.intersectionBilinear X m (p + q) t
          (Supports.ProperCycle.pairCycle X m p q A B) (Finsupp.single D 1) := by
  rw [intersection X m p q a b]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  rw [linear_sum (Supports.ProperCycle.intersectionBilinear X m (p + q) t (Supports.ProperCycle.pairCycle X m p q A B)) c,
    Finset.smul_sum]
  simp only [smul_smul]

theorem support (p q : ℕ) (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (E : X.DimensionCycleSupport (p + q)) (hE : E ∈ (Supports.ProperCycle.intersectionBilinear X m p q a b).support) :
    ∃ A ∈ a.support, ∃ B ∈ b.support, E ∈ (Supports.ProperCycle.pairCycle X m p q A B).support := by
  by_contra hn
  have hz : Supports.ProperCycle.intersectionBilinear X m p q a b E = 0 := by
    rw [intersection X m p q a b]
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro A hA
    apply Finset.sum_eq_zero
    intro B hB
    have he : E ∉ (Supports.ProperCycle.pairCycle X m p q A B).support := fun he => hn ⟨A, hA, B, hB, he⟩
    rw [Finsupp.notMem_support_iff.mp he, mul_zero]
  exact (Finsupp.mem_support_iff.mp hE) hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleLinearExpansion
