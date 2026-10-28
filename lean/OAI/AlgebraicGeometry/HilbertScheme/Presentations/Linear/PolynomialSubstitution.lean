import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Polynomial Substitution -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.PolynomialSubstitution.GradedModules

noncomputable section

/-! Substitution of homogeneous linear polynomials preserves the actual integer grading. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} {τ : Type v} [Fintype σ] [Fintype τ]
variable (R : Type w) [CommRing R]

theorem linearSubstitution_integer_homogeneous (a : σ → MvPolynomial τ R)
    (ha : ∀ i : σ, (a i).IsHomogeneous 1) {d : ℤ} {p : MvPolynomial σ R}
    (hp : p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R d) : MvPolynomial.aeval a p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R d := by
  classical
  by_cases hpzero : p = 0
  · rw [hpzero, map_zero]
    exact Submodule.zero_mem _
  have hne : p.support.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact hpzero (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨m, hm⟩ := hne
  have hd : (m.degree : ℤ) = d := by
    have h := hp (mem_support_iff.mp hm)
    simpa only [IntegerPolynomialGrading.GradedModules.integerWeight_eq_degree] using h
  rw [← hd, IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat] at hp ⊢
  change (MvPolynomial.eval₂ (algebraMap R (MvPolynomial τ R)) a p).IsHomogeneous m.degree
  simpa only [one_mul] using hp.eval₂ (algebraMap R (MvPolynomial τ R)) a
    (fun r => isHomogeneous_C τ r) ha

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.PolynomialSubstitution.GradedModules
