import OAI.AlgebraicGeometry.ComplexMultiplication.OpenEmbeddingDifferentiable
import OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Intrinsic Open Immersion Differentiable -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicOpenImmersionDifferentiable

noncomputable section

/-! # The actual native open-immersion point map and its inverse are complex differentiable -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable {Y X : Over (Spec (.of ℂ))} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral X.left] [Smooth X.hom] [Nonempty (AnalyticIntrinsicAtlasRegular.NativePointManifold Y)]
  (φ : Y ⟶ X) [IsOpenImmersion φ.left]

omit [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral X.left] [Smooth X.hom] in
/-- The partial homeomorphism has the unchanged actual scheme-point map as its forward map. -/
def nativeOpenImmersionPointPartialHomeomorph :
    OpenPartialHomeomorph (AnalyticIntrinsicAtlasRegular.NativePointManifold Y) (AnalyticIntrinsicAtlasRegular.NativePointManifold X) :=
  let f : AnalyticIntrinsicAtlasRegular.NativePointManifold Y → AnalyticIntrinsicAtlasRegular.NativePointManifold X := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ
  let he : Topology.IsOpenEmbedding f :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion φ
  he.toOpenPartialHomeomorph f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem nativeOpenImmersionPointPartialHomeomorph_mDifferentiable :
    (nativeOpenImmersionPointPartialHomeomorph φ).MDifferentiable
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) := by
  let f : AnalyticIntrinsicAtlasRegular.NativePointManifold Y → AnalyticIntrinsicAtlasRegular.NativePointManifold X := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ
  have h : ContMDiff
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) 1 f :=
    ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1
  apply OpenEmbeddingDifferentiable.openEmbedding_mDifferentiable
    (M := AnalyticIntrinsicAtlasRegular.NativePointManifold Y) (N := AnalyticIntrinsicAtlasRegular.NativePointManifold X) f
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion φ)
  · exact h.mdifferentiable one_ne_zero
  · intro x
    exact ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective φ x

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicOpenImmersionDifferentiable
