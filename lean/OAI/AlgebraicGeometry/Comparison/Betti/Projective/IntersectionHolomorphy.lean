import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionDomains
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts

/-! # Intersection Holomorphy -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionHolomorphy.Dolbeault

noncomputable section

/-! The coordinate-product identifications of projective intersections are
holomorphic in both directions for the independently constructed native atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction

local instance projectiveIntegral (n : ℕ) : IsIntegral (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left :=
  ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveScheme_integral n
local instance projectiveSmooth (n : ℕ) : Smooth (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).hom :=
  Albanese.Construction.ProjectiveCover.projectiveSpace_smooth n
local instance projectiveNativeChartedSpace (n : ℕ) :
    ChartedSpace (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) :=
  (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticSpace_chartedSpace

theorem projectiveAffineSchemePoint_eq_nativeChart_symm (n : ℕ) (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i z = (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart n i).symm
      (fun k => z ((Fintype.equivFin {j : Fin (n + 1) // j ≠ i}).symm k)) := by
  rw [ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart, ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply]
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap _ _ _ =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap _ _ _
  congr 1
  ext p
  simp only [ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph_symm_apply, ComplexMultiplication.HodgeComparison.PolynomialCharts.CM.Construction.polynomialRegularChart_symm_apply,
    Equiv.symm_apply_apply]

theorem projectiveAffineSchemePoint_holomorphic (n : ℕ) (i : Fin (n + 1)) :
    ContMDiff 𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ)
      𝓘(ℂ, (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel) ∞ (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i) := by
  have h := (ComplexMultiplication.HodgeComparison.PolynomialCharts.CM.Construction.native_affineChart_symm_smooth
    (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineChartOverMap n i)
    _ (ComplexMultiplication.HodgeComparison.PolynomialCharts.CM.Construction.polynomialRegularChart_mem_atlas _)).of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)
  have h' : ContMDiff 𝓘(ℂ, Fin (Fintype.card {j : Fin (n + 1) // j ≠ i}) → ℂ)
      𝓘(ℂ, (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel) ∞
      (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.nativeProjectiveCoordinateChart n i).symm := contMDiffOn_univ.mp h
  have hr : ContMDiff 𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ)
      𝓘(ℂ, Fin (Fintype.card {j : Fin (n + 1) // j ≠ i}) → ℂ) ∞
      (fun (z : {j : Fin (n + 1) // j ≠ i} → ℂ) k =>
        z ((Fintype.equivFin {j : Fin (n + 1) // j ≠ i}).symm k)) := by
    apply contMDiff_pi_space.mpr
    intro k
    exact (ContinuousLinearMap.proj
      ((Fintype.equivFin {j : Fin (n + 1) // j ≠ i}).symm k) :
        ({j : Fin (n + 1) // j ≠ i} → ℂ) →L[ℂ] ℂ).contMDiff
  exact (h'.comp hr).congr (projectiveAffineSchemePoint_eq_nativeChart_symm n i)

theorem projectiveSchemeIntersectionChart_holomorphic (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) :
    ContMDiff 𝓘(ℂ, (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel)
      𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ) ∞
      (IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  apply contMDiff_pi_space.mpr
  intro j p
  change ContMDiffAt _ _ ∞ (fun p : IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s =>
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)) p
  apply (contMDiffAt_subtype_iff (U := IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) (x := p)
    (f := fun q : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n =>
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q))).mpr
  have hp : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := p.property i hi
  exact ((contMDiffOn_pi_space.mp (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.projectiveCoordinates_holomorphic n i) j.val) p.val hp).contMDiffAt
    (((ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage
      (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.continuous).mem_nhds hp)

theorem projectiveSchemeIntersectionChart_symm_holomorphic (n : ℕ)
    (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) :
    ContMDiff 𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ)
      𝓘(ℂ, (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel) ∞
      (IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi).symm := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  have h := (projectiveAffineSchemePoint_holomorphic n i).comp
    (contMDiff_subtype_val (I := 𝓘(ℂ, {j : Fin (n + 1) // j ≠ i} → ℂ))
      (U := ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (IntersectionDomains.Dolbeault.projectiveIntersectionPunctures s i)))
  exact h.congr (IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart_symm_apply n s i hi)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionHolomorphy.Dolbeault
