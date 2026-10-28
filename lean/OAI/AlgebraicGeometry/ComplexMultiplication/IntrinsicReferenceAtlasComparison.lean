import OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular
import OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldScalarRestriction
import OAI.AlgebraicGeometry.ComplexMultiplication.PointBettiBridge
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexDiffeomorph

/-! # Intrinsic Reference Atlas Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceAtlasComparison

noncomputable section

/-! # The actual identity of atlases retains genuine integration and singular restriction -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "N" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "G" => OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular.NativePointManifold X
local notation "A" => ModuleCat.of ℂ ℂ

/-- The actual native-to-original identity is smooth over the underlying real field. -/
theorem nativePointManifoldHomeomorph_realSmooth :
    ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, E) ∞ (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X) :=
  ManifoldScalarRestriction.contMDiff_complex_to_real (AnalyticIntrinsicAtlasRegular.contMDiff_nativePointManifoldHomeomorph X ∞)

/-- The actual inverse identity is smooth over the underlying real field. -/
theorem nativePointManifoldHomeomorph_symm_realSmooth :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm :=
  ManifoldScalarRestriction.contMDiff_complex_to_real (AnalyticIntrinsicAtlasRegular.contMDiff_nativePointManifoldHomeomorph_symm X ∞)

/-- The identity on unchanged scheme points with both actual real atlases explicit. -/
def nativePointManifoldRealDiffeomorph : Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, E) G M ∞ where
  toEquiv := (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).toEquiv
  contMDiff_toFun := nativePointManifoldHomeomorph_realSmooth X
  contMDiff_invFun := nativePointManifoldHomeomorph_symm_realSmooth X

/-- Genuine form pullback transports native forms to the unchanged original atlas. -/
def nativeOriginalDeRhamComplexIso :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex N G ≅ Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M :=
  Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamDiffeomorph (nativePointManifoldRealDiffeomorph X).symm

/-- Actual smooth singular cochains transport by the same identity diffeomorphism. -/
def nativeOriginalSmoothCochainComplexIso :
    AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains N A G ≅
      AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E A M :=
  AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison.manifoldSmoothCochainsDiffeomorphIso A
    (nativePointManifoldRealDiffeomorph X).symm

/-- Actual ordinary singular cochains transport by the same underlying identity. -/
def nativeOriginalOrdinaryCochainComplexIso :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A (Betti.Scheme.schemePointSpace X) ≅
      AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A (TopCat.of M) :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCochainsFunctor A).mapIso (PointBettiBridge.complexPointSpaceIso X).symm.op

/-- Genuine simplex integration retains the identity transport between actual atlases. -/
theorem nativeOriginalIntegration_square :
    (nativeOriginalDeRhamComplexIso X).hom ≫
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M =
      AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap N G ≫
        (nativeOriginalSmoothCochainComplexIso X).hom :=
  AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_naturality
    (nativePointManifoldRealDiffeomorph X).symm
      (nativePointManifoldRealDiffeomorph X).symm.contMDiff

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary-to-smooth restriction retains the exact same identity transport. -/
theorem nativeOriginalSmoothRestriction_square :
    (nativeOriginalOrdinaryCochainComplexIso X).hom ≫
        AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E A M =
      AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction N A G ≫
        (nativeOriginalSmoothCochainComplexIso X).hom := by
  simpa only [nativeOriginalOrdinaryCochainComplexIso,
    nativeOriginalSmoothCochainComplexIso] using!
    AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A
    (nativePointManifoldRealDiffeomorph X).symm
      (nativePointManifoldRealDiffeomorph X).symm.contMDiff

omit [IsIntegral X.left] [Smooth X.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- The ordinary cochain map is precisely the identity point-space pullback used by Betti. -/
theorem nativeOriginalOrdinaryCochainComplexIso_hom_eq :
    (nativeOriginalOrdinaryCochainComplexIso X).hom =
      AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A (PointBettiBridge.complexPointSpaceIso X).inv := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceAtlasComparison
