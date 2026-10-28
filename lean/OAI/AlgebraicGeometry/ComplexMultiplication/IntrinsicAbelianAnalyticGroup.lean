import OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular
import OAI.AlgebraicGeometry.AbelianVariety.AnalyticGroup

/-! # Intrinsic Abelian Analytic Group -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicAbelianAnalyticGroup

noncomputable section

/-! # The actual native analytic group on the unchanged original abelian scheme

The group law is the original algebraic group law on scheme points. The native
analytic atlas and its Lie-group structure are the existing proved ones.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)

/-- The actual original scheme group law on the native point carrier. -/
instance nativePointManifoldGroup : Group (AnalyticIntrinsicAtlasRegular.NativePointManifold X) :=
  inferInstanceAs (Group (BundledAbelianBridge.originalAbelianVariety X).variety.analyticSpace)

/-- The existing actual native analytic Lie group, with no analytic-group premise added. -/
instance nativePointManifoldComplexLieGroup (r : ℕ∞ω) :
    LieGroup 𝓘(ℂ, N) r (AnalyticIntrinsicAtlasRegular.NativePointManifold X) :=
  AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology.pointComplexLieGroup (BundledAbelianBridge.originalAbelianVariety X) r

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X] in
/-- The actual original-to-native point identity is analytic in the proved Lie-group atlas. -/
theorem originalToNativeAbelianPoint_analytic :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, N) ω (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm :=
  AnalyticIntrinsicAtlasRegular.contMDiff_nativePointManifoldHomeomorph_symm X ω

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicAbelianAnalyticGroup
