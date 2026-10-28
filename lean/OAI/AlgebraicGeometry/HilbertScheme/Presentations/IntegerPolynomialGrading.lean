import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFreeModules
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Integer Polynomial Grading -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules

noncomputable section

/-! Comparison of the natural and integer polynomial gradings. -/

open _root_.MvPolynomial

universe u v

variable {σ : Type u} [Fintype σ]
variable (R : Type v) [CommRing R]

theorem integerWeight_eq_degree (m : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) m = (m.degree : ℤ) := by
  rw [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Nat.cast_sum]
  simp only [nsmul_eq_mul, mul_one]

theorem polynomialIntegerGrading_nat (n : ℕ) :
    WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R (n : ℤ) = homogeneousSubmodule σ R n := by
  apply Submodule.ext
  intro p
  constructor
  · intro hp m hm
    have hi := hp hm
    rw [integerWeight_eq_degree] at hi
    have hn : Finsupp.weight (1 : σ → ℕ) m = m.degree :=
      DFunLike.congr_fun (Finsupp.degree_eq_weight_one (R := ℕ) (σ := σ)).symm m
    rw [hn]
    exact_mod_cast hi
  · intro hp m hm
    have hi := hp hm
    have hn : Finsupp.weight (1 : σ → ℕ) m = m.degree :=
      DFunLike.congr_fun (Finsupp.degree_eq_weight_one (R := ℕ) (σ := σ)).symm m
    rw [hn] at hi
    rw [integerWeight_eq_degree, hi]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ideal_integer_homogeneous (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) :
    I.IsHomogeneous (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (homogeneousSubmodule σ R) I).mp hI
  rw [hS]
  apply Ideal.homogeneous_span
  rintro p ⟨x, _, rfl⟩
  obtain ⟨n, hn⟩ := x.property
  refine ⟨(n : ℤ), ?_⟩
  rw [polynomialIntegerGrading_nat]
  exact hn

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules
