import OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth

/-! # Open Intrinsic Regular Chart -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenIntrinsicRegularChart

noncomputable section

/-! Every actual point of an affine open admits regular coordinates in the native scheme dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

theorem affineOpen_exists_nativeRegularChart
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) :
    ∃ e : OpenPartialHomeomorph
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U))
        (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ),
      e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
        (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) ∧ x ∈ e.source := by
  let p := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x
  have hpU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ U := by
    have hm : p ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨x, rfl⟩
    rwa [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hm
  let : Nonempty U := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, hpU⟩⟩
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let : IsDomain A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X U
  let : Algebra.Smooth ℂ A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU
  have hd := OpenChartDimension.affineOpen_genericDifferentialRank_eq X A (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) x
  rw [← hd]
  exact ⟨chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) x,
    chart_mem_atlas _ x, mem_chart_source _ x⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenIntrinsicRegularChart
