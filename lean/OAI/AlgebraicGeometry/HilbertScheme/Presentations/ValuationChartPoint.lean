import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationNormalizedCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.DegreeRankProfile

/-! # Valuation Chart Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationChartPoint.GradedHilbert

noncomputable section

/-! The valuation closure defines an actual point of a normalized Hilbert
chart over the original base, with the polynomial relation-rank profile. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {S : Scheme.{u}} {n : ℕ}

theorem exists_valuation_hilbert_chart_point (f : Spec (.of R) ⟶ S)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (N : ℕ) (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R)
      (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q), Function.Injective a ∧
      Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I) N ∧
      Projective.Saturation.GradedHilbert.projectiveSaturation (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q) = ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I ∧
      ∃! y : Over.mk f ⟶ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
        y ≫ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) =
          Affine.NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint f a Q hQ := by
  obtain ⟨a, Q, hQ, ha, he, hsat, hdeg⟩ :=
    ValuationNormalizedCoordinates.GradedHilbert.exists_valuation_normalized_hilbert_coordinates (R := R) I hI P hP N hN ι hr
  refine ⟨a, Q, hQ, ha, he, hsat,
    Affine.NormalizedCriterion.GradedHilbert.existsUnique_affineNormalizedHilbertChartPoint f a Q hQ _ ?_⟩
  intro d _
  have hd := hdeg (d + N) (Nat.le_add_left N d)
  refine ⟨hd.1, ?_⟩
  have hdim : Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal (d + N) =
      Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal (d + N) := by
    have h := hd.2.trans
      ((Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K I hI hP).2 (d + N)
        (hN.trans (Nat.le_add_left N d))).symm
    exact_mod_cast h
  rw [hdim]
  exact Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile_add I hI P hP N hN d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationChartPoint.GradedHilbert
