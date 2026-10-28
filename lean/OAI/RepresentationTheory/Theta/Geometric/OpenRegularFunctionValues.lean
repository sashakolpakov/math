import OAI.RepresentationTheory.Theta.Geometric.RegularFunctionContinuity
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion

/-! # Open Regular Function Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionValues

noncomputable section

section

/-! Actual regular functions are holomorphic in the native complex
manifold structure of every smooth integral scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps ChartedSpace
open scoped _root_.Manifold ContDiff

theorem regularFunctionValue_contMDiff (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (s : Γ(X.left, ⊤)) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (𝓘(ℂ, ℂ)) r (RegularFunctionContinuity.regularFunctionValue X s) := by
  apply contMDiff_iff.mpr
  refine ⟨RegularFunctionContinuity.regularFunctionValue_continuous X s, ?_⟩
  intro x y
  have hc : chartAt (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) x ∈
      AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) :=
    chart_mem_atlas _ x
  obtain ⟨U, hU, e, he, hchart⟩ := hc
  have htarget : (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e).target = e.target := rfl
  have H := (he.1 ((Scheme.ΓSpecIso (.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U))).hom
    ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU).left.appTop s))).of_le (show r ≤ ω from le_top)
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source, extChartAt_target,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
    Set.preimage_id, Set.range_id, Set.inter_univ, Function.comp_def, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_source, Set.preimage_univ,
    id_eq, Set.preimage, Set.mem_ofPred_eq, Set.ofPred_mem_eq, Set.mem_univ, Set.ofPred_true,
    hchart, htarget, AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply, RegularFunctionContinuity.regularFunctionValue_affineTest] using H

end

/-! Regular-section values on an open subscheme, expressed on the
original native scheme-point space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def regularOpenScheme (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (U.ι ≫ X.hom)

def regularOpenInclusion (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) : regularOpenScheme X U ⟶ X :=
  Over.homMk U.ι

instance regularOpenInclusion_isOpenImmersion (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) :
    IsOpenImmersion (regularOpenInclusion X U).left := inferInstanceAs (IsOpenImmersion U.ι)

def openRegularFunctionValue (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (s : Γ(X.left, U))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : ℂ := by
  classical
  exact if h : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U then Complex.SectionEvaluation.complexSectionValue p.left U h s else 0

theorem openRegularFunctionValue_of_mem (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (s : Γ(X.left, U))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U) :
    openRegularFunctionValue X U s p = Complex.SectionEvaluation.complexSectionValue p.left U hp s := by
  classical
  exact dite_eq_left hp

theorem openRegularFunctionValue_inclusion (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (s : Γ(X.left, U))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (regularOpenScheme X U)) :
    openRegularFunctionValue X U s (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularOpenInclusion X U) p) =
      RegularFunctionContinuity.regularFunctionValue (regularOpenScheme X U) (U.topIso.inv s) p := by
  have hp : (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularOpenInclusion X U) p).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U :=
    (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).property
  rw [openRegularFunctionValue_of_mem X U s _ hp]
  exact Complex.SectionEvaluation.complexSectionValue_open U p.left s

end

end OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionValues
