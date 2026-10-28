import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationChartPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.AffineCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ValuationPolynomialFamily

/-! # Valuation Parameter Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationParameterFamily.GradedHilbert

noncomputable section

/-! The actual bounded Hilbert parameter scheme contains the valuation
closure, and its universal family restricts to the prescribed generic family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n : ℕ}

theorem exists_valuation_hilbert_parameter_family (f : Spec (.of R) ⟶ S)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (N : ℕ) (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) =
          Intrinsic.ValuationPolynomialFamily.GradedHilbert.nativeValuationFamilyOfIdeal f I hI := by
  obtain ⟨a, Q, hQ, _, _, hsat, y, hy, _⟩ :=
    ValuationChartPoint.GradedHilbert.exists_valuation_hilbert_chart_point f I hI P hP N hN ι hr
  refine ⟨y ≫ BoundedHilbert.ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S _, ?_⟩
  apply Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n f
  rw [NormalizedHilbert.AffineCoordinates.GradedHilbert.boundedHilbertUniversalFamily_affine_chart_coordinates, hy, NormalizedHilbert.AffineCoordinates.GradedHilbert.affineChartMatrix_of_matrix,
    hsat, Intrinsic.ValuationPolynomialFamily.GradedHilbert.nativeValuationFamilyOfIdeal_coordinates]

theorem exists_valuation_hilbert_parameter_generic_family (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f)))
    (P : Polynomial ℚ)
    (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f) F).toIdeal P)
    (N : ℕ) (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f (algebraMap R K) ≫ x)
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f) F
  have hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n _ F
  obtain ⟨x, hx⟩ := exists_valuation_hilbert_parameter_family f I hI P hP N hN ι hr
  refine ⟨x, ?_⟩
  rw [Hilbert.Functor.pullbackFamily_comp, hx]
  apply Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f)
  exact Intrinsic.ValuationPolynomialFamily.GradedHilbert.nativeValuationFamilyOfIdeal_generic_coordinates f I hI

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationParameterFamily.GradedHilbert
