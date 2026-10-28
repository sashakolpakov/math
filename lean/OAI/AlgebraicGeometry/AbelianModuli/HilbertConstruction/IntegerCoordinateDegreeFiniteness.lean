import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient

/-! # Integer Coordinate Degree Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerCoordinateDegreeFiniteness

noncomputable section

/-! Every integer homogeneous piece of a projective coordinate quotient is finite. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert

universe u v

theorem polynomialIntegerGrading_eq_bot_of_neg {σ : Type u} [Fintype σ]
    (R : Type v) [CommRing R] (z : ℤ) (hz : z < 0) :
    HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R z = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  change p = 0
  apply MvPolynomial.ext
  intro m
  rw [AddMonoidAlgebra.coeff_zero]
  by_contra hm
  have h := hp hm
  rw [HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.integerWeight_eq_degree] at h
  have hn : (0 : ℤ) ≤ (m.degree : ℤ) := Int.natCast_nonneg _
  exact (not_lt_of_ge (h ▸ hn)) hz

theorem integerQuotientGrading_eq_bot_of_neg {R : Type u} [CommRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (z : ℤ) (hz : z < 0) :
    HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I z = ⊥ := by
  unfold HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading HilbertScheme.Presentations.IntegerGradedQuotient.GradedModules.IntegerQuotient.grading
  rw [polynomialIntegerGrading_eq_bot_of_neg R z hz, Submodule.map_bot]
  rfl

theorem integerQuotientGrading_finite {R : Type u} [CommRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (z : ℤ) :
    Module.Finite R (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I z) := by
  by_cases hz : 0 ≤ z
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    exact Module.Finite.equiv (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d)
  · rw [integerQuotientGrading_eq_bot_of_neg I z (lt_of_not_ge hz)]
    infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerCoordinateDegreeFiniteness
