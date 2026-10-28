import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineFactoring
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreRegularEquations

/-! # Segre Closed Subscheme -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreClosedSubscheme.Constructions.Algebraization

noncomputable section

/-!
# Algebraic inverse images of homogeneous Segre equations

Two actual maps to projective schemes pull homogeneous Segre equations back
to a reduced closed subscheme. This is proved in affine charts, without
assuming a scheme-level Segre map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

theorem exists_projective_chart_point_lift {n : ℕ} (p : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) :
    ∃ i : Fin (n + 1), p ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i)) := by
  obtain ⟨q, rfl⟩ := ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_surjective n p
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch q
  refine ⟨i, ?_⟩
  rw [ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_on_patch n i ⟨q, hi⟩]
  exact ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)
    ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm
      (ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i ⟨q, hi⟩)), rfl⟩

def segreOfSchemeMaps {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} {m n : ℕ}
    (a : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    (b : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : Projectivization ℂ (Fin (m + 1) × Fin (n + 1) → ℂ) :=
  SegreAt.Constructions.Segre.segre ((Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv m).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a p))
    ((Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b p))

theorem exists_reduced_closed_subscheme_of_segre_equations
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} {m n : ℕ} {α : Type*}
    (a : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    (b : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (P : α → MvPolynomial (Fin (m + 1) × Fin (n + 1)) ℂ)
    (degree : α → ℕ) (hP : ∀ k, (P k).IsHomogeneous (degree k)) :
    ∃ (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (i : Z ⟶ X),
      IsReduced Z.left ∧ IsClosedImmersion i.left ∧
      range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) =
        (segreOfSchemeMaps a b) ⁻¹' Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus P degree hP := by
  let S := (segreOfSchemeMaps a b) ⁻¹' Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus P degree hP
  apply SchemePointSeparation.Constructions.Algebraization.exists_reduced_closed_subscheme_of_open_separators X S
  intro p hp
  have hp' : ¬∀ k, segreOfSchemeMaps a b p ∈ Foundations.Scheme.ProjectiveZeroLocus.homogeneousProjectiveZeroLocus (P k) (hP k) := by
    simpa only [S, mem_preimage, Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus, mem_iInter] using hp
  obtain ⟨k, hk⟩ := not_forall.mp hp'
  obtain ⟨i, hi⟩ := exists_projective_chart_point_lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a p)
  obtain ⟨j, hj⟩ := exists_projective_chart_point_lift (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b p)
  obtain ⟨T, t, q, a', b', hT, ht, hq, ha', hb'⟩ :=
    AffineFactoring.Constructions.Algebraization.exists_affine_neighborhood_factoring_two_maps a b
      (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap m i) (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n j) p hi hj
  let : IsAffine T.left := hT
  let : IsOpenImmersion t.left := ht
  let r := SegreRegularEquations.Constructions.Algebraization.segreChartSection i j a' b' (P k)
  have hzero (q' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T) : Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T q' r = 0 ↔
      segreOfSchemeMaps a b (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map t q') ∈
        Foundations.Scheme.ProjectiveZeroLocus.homogeneousProjectiveZeroLocus (P k) (hP k) := by
    simpa only [r, ha', hb', ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, segreOfSchemeMaps] using
      SegreRegularEquations.Constructions.Algebraization.segreChartSection_eq_zero_iff i j a' b' (P k) (hP k) q'
  have hr : Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T q r ≠ 0 := by
    intro hr
    apply hk
    rw [← hq]
    exact (hzero q).mp hr
  obtain ⟨U, hU, hUS⟩ := SchemePointSeparation.Constructions.Algebraization.exists_open_separator_of_affine_regular_function (S := S) t q r hr (by
    intro q' hq'S
    apply (hzero q').mpr
    exact mem_iInter.mp hq'S k)
  exact ⟨U, by rwa [hq] at hU, hUS⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreClosedSubscheme.Constructions.Algebraization
