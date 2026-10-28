import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis

/-! # Linear Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LinearCompleteness.StableHilbertCoverage

noncomputable section

/-! The standard projective frame detects every degree-one homogeneous
polynomial, over the original coefficient ring. -/

open _root_.MvPolynomial
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert
universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem linearPolynomial_eq_zero_of_frame_values
    (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n 1)
    (hp : ∀ i : Fin (n + 1),
      MvPolynomial.eval₂Hom (algebraMap R R) (Pi.single i 1) p.val = 0) : p = 0 := by
  classical
  have hspan : p.val ∈ Submodule.span R (Set.range (X : Fin (n + 1) → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact p.property
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hspan
  have hzero (i : Fin (n + 1)) : c i = 0 := by
    have he : (MvPolynomial.aeval (Pi.single i (1 : R))) p.val = c i := by
      rw [← hc]
      simp only [map_sum, map_smul, aeval_X]
      simp [Pi.single_apply, eq_comm]
    exact he.symm.trans (hp i)
  apply Subtype.ext
  change p.val = 0
  rw [← hc]
  simp only [hzero, zero_smul, Finset.sum_const_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LinearCompleteness.StableHilbertCoverage
