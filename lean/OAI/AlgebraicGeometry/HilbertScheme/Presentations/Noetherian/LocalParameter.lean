import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalNormalizedCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.AffineCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.DegreeRankProfile
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction

/-! # Local Parameter -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalParameter.GradedHilbert

noncomputable section

/-! Native families over local noetherian tests are realized by actual
bounded Hilbert parameters from their canonical residue-fiber polynomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n : ℕ}

theorem exists_noetherian_local_hilbert_parameter (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (N : ℕ) (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  have hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  obtain ⟨a, Q, hQ, _, _, hsat, hdeg⟩ :=
    LocalNormalizedCoordinates.GradedHilbert.exists_noetherian_local_normalized_hilbert_coordinates I hI P hP N hN ι hr
  let p : PrimeSpectrum R := IsLocalRing.closedPoint R
  let K := p.asIdeal.ResidueField
  let J := Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I)
  have hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal := Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _
  have hPJ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P := hP p
  have hNP : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N := (le_max_right _ _).trans hN
  have hmem := Affine.NormalizedCriterion.GradedHilbert.affineNormalizedChartPoint_hilbert_mem f a Q hQ
    (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) (by
      intro d _
      have hd := hdeg (d + N) (Nat.le_add_left N d)
      refine ⟨hd.1, ?_⟩
      have hdim : Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal (d + N) =
          Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal (d + N) := by
        have h := hd.2.trans ((Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K J hJ hPJ).2 (d + N)
          (hNP.trans (Nat.le_add_left N d))).symm
        exact_mod_cast h
      rw [hdim]
      exact Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile_add J hJ P hPJ N hNP d)
  obtain ⟨y, hy, _⟩ := (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_factorization_iff a S _ _).mp hmem
  refine ⟨y ≫ BoundedHilbert.ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S _, ?_⟩
  apply Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n f
  rw [NormalizedHilbert.AffineCoordinates.GradedHilbert.boundedHilbertUniversalFamily_affine_chart_coordinates, hy, NormalizedHilbert.AffineCoordinates.GradedHilbert.affineChartMatrix_of_matrix, hsat]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalParameter.GradedHilbert
