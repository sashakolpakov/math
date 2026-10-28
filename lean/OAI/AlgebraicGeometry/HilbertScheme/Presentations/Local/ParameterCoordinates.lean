import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineGrassmannian
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalClassification
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPointRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.DegreeCoordinateRecovery

/-! # Parameter Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ParameterCoordinates.GradedHilbert

noncomputable section

/-! The local noetherian Hilbert parameter of a native family has exactly
the Grassmannian point of that family's canonical degree quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem noetherianLocal_hilbert_parameter_coordinates (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))
    (hx : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F) :
    x ≫ BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) =
      Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr := by
  let q := Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P
  obtain ⟨a, y, hy⟩ := BoundedHilbert.LocalChartLift.GradedHilbert.boundedHilbert_local_chart_lift q f x
  let z := y ≫ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q
  let Q := NormalizedHilbert.AffineCoordinates.GradedHilbert.affineChartMatrix a f z
  have hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q := NormalizedHilbert.AffineCoordinates.GradedHilbert.affineChartMatrix_normalized a f z
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  have hc := NormalizedHilbert.AffineCoordinates.GradedHilbert.boundedHilbertUniversalFamily_affine_chart_coordinates a f q y
  rw [hy, hx] at hc
  have hideal : Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N :=
    Normalized.NoetherianIdealRecovery.GradedHilbert.normalizedNoetherianIdeal_eq_degreeGenerated a Q hQ I (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F)
      hc.symm P hP hN hr
  have hg := Normalized.DegreeCoordinateRecovery.GradedHilbert.normalizedGrassmannian_eq_of_generatedIdeal I
    (Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian f F P hP N hN ι hr)
    (Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian_toSubmodule f F P hP N hN ι hr) a Q hQ hideal
  rw [← hy, Category.assoc, BoundedHilbert.ChartPullback.GradedHilbert.boundedHilbertChartOverMap_parameter, ← Category.assoc]
  change z ≫ Grassmannian.Gluing.grassmannianChartOverMap a S =
    Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f (Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian f F P hP N hN ι hr)
  rw [← hg, Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint_normalized]
  exact congrArg (fun k => k ≫ Grassmannian.Gluing.grassmannianChartOverMap a S)
    (Affine.ChartPointRecovery.GradedHilbert.affineNormalizedChartPoint_of_affineChartMatrix a f z).symm

theorem exists_noetherianLocal_hilbert_coordinate_lift (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      x ≫ BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) =
        Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr := by
  obtain ⟨x, hx⟩ := Noetherian.LocalParameter.GradedHilbert.exists_noetherian_local_hilbert_parameter f F P hP N hN ι hr
  exact ⟨x, noetherianLocal_hilbert_parameter_coordinates f F P hP hN hr x hx⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ParameterCoordinates.GradedHilbert
