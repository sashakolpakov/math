import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicAbelianAnalyticGroup
import OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldScalarRestriction
import OAI.Analysis.DifferentialForms.Manifold.ComplexCharts

/-! # Intrinsic Abelian Real Group -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicAbelianRealGroup

noncomputable section

/-! # The actual underlying real analytic group of the original abelian scheme -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)

/-- The real Lie group uses the same original algebraic group law and native atlas. -/
instance nativePointManifoldRealLieGroup (r : ℕ∞ω) :
    LieGroup 𝓘(ℝ, N) r (AnalyticIntrinsicAtlasRegular.NativePointManifold X) :=
  AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology.pointRealLieGroup (BundledAbelianBridge.originalAbelianVariety X) r

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X] in
/-- The proved analytic identity is smooth on the actual underlying real manifolds. -/
theorem originalToNativeAbelianPoint_realSmooth :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm :=
  ManifoldScalarRestriction.contMDiff_complex_to_real ((IntrinsicAbelianAnalyticGroup.originalToNativeAbelianPoint_analytic X).of_le le_top)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicAbelianRealGroup
