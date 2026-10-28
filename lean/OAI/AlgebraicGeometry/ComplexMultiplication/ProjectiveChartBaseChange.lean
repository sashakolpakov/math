import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartNaturality
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Projective Chart Base Change -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartBaseChange.ProjectiveCharts

noncomputable section

/-! # Base change on the actual polynomial projective charts

The square is a categorical pullback of the actual spectrum morphisms, using
the proved polynomial tensor-product equivalence in Mathlib.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The actual affine polynomial coordinate chart base changes along the coefficient map. -/
theorem projectivePolynomialChart_isPullback (n : ℕ) (i : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R S) :
        CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i →+* CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial S n i)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : S →+* CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial S n i)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have h := CommRingCat.isPushout_of_isPushout R S
    (CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i) (CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial S n i)
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ h
  simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_def] using hp.flip

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartBaseChange.ProjectiveCharts
