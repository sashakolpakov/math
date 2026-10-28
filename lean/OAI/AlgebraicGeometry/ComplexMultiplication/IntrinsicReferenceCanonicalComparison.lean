import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceAtlasComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Intrinsic Reference Canonical Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceCanonicalComparison

noncomputable section

/-! # The native canonical de Rham-Betti comparison retains the actual original atlas

The projective bundle has precisely the unchanged original scheme. Its canonical
comparison is normalized by integration and restriction on actual singular simplices.
-/

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
local notation "IN" => OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) (AnalyticIntrinsicAtlasRegular.NativePointManifold X)
local notation "IO" => OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap
  (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) (ComplexPoint.Basic.ComplexSchemePoint X)
local notation "RN" => OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
  (ModuleCat.of ℂ ℂ) (AnalyticIntrinsicAtlasRegular.NativePointManifold X)
local notation "RO" => OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction
  (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) (ModuleCat.of ℂ ℂ) (ComplexPoint.Basic.ComplexSchemePoint X)

/-- Actual form pullback gives the native-to-original de Rham cohomology isomorphism. -/
def nativeOriginalDeRhamCohomologyIso (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology N G n ≅
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M n :=
  HomologicalComplex.homologyMapIso (IntrinsicReferenceAtlasComparison.nativeOriginalDeRhamComplexIso X) n

/-- The actual smooth-singular identity gives its cohomology isomorphism. -/
def nativeOriginalSmoothCohomologyIso (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains N A G).homology n ≅
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E A M).homology n :=
  HomologicalComplex.homologyMapIso (IntrinsicReferenceAtlasComparison.nativeOriginalSmoothCochainComplexIso X) n

/-- The ordinary Betti transport is the actual identity point-space pullback. -/
def nativeOriginalOrdinaryCohomologyIso (n : ℕ) :
    Betti.Scheme.schemeBetti A X n ≅
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology A (TopCat.of M) n :=
  HomologicalComplex.homologyMapIso (IntrinsicReferenceAtlasComparison.nativeOriginalOrdinaryCochainComplexIso X) n

set_option backward.isDefEq.respectTransparency false in
/-- Actual integration retains the full cohomology identity between the two atlases. -/
theorem nativeOriginalIntegration_homology_square (n : ℕ) :
    (nativeOriginalDeRhamCohomologyIso X n).hom ≫
        HomologicalComplex.homologyMap (IO) n =
      HomologicalComplex.homologyMap (IN) n ≫
        (nativeOriginalSmoothCohomologyIso X n).hom := by
  simpa only [nativeOriginalDeRhamCohomologyIso, nativeOriginalSmoothCohomologyIso,
    HomologicalComplex.homologyMap_comp] using!
    congrArg (fun f => HomologicalComplex.homologyMap f n)
      (IntrinsicReferenceAtlasComparison.nativeOriginalIntegration_square X)

set_option backward.isDefEq.respectTransparency false in
/-- The same cohomology identity retains genuine ordinary-to-smooth restriction. -/
theorem nativeOriginalSmoothRestriction_homology_square (n : ℕ) :
    (nativeOriginalOrdinaryCohomologyIso X n).hom ≫
        HomologicalComplex.homologyMap (RO) n =
      HomologicalComplex.homologyMap (RN) n ≫
        (nativeOriginalSmoothCohomologyIso X n).hom := by
  simpa only [nativeOriginalOrdinaryCohomologyIso, nativeOriginalSmoothCohomologyIso,
    HomologicalComplex.homologyMap_comp] using!
    congrArg (fun f => HomologicalComplex.homologyMap f n)
      (IntrinsicReferenceAtlasComparison.nativeOriginalSmoothRestriction_square X)

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

set_option backward.isDefEq.respectTransparency false in
/-- The native canonical comparison is normalized by actual original-atlas simplex integrals. -/
theorem nativeOriginalCanonicalComparison_square (n : ℕ) :
    ((V).deRhamBettiIso n).hom ≫
        (nativeOriginalOrdinaryCohomologyIso X n).hom ≫
          HomologicalComplex.homologyMap (RO) n =
      (nativeOriginalDeRhamCohomologyIso X n).hom ≫
        HomologicalComplex.homologyMap (IO) n := by
  rw [nativeOriginalSmoothRestriction_homology_square, ← Category.assoc]
  change (((V).deRhamBettiIso n).hom ≫ (V).bettiToSmoothSingular n) ≫ _ = _
  rw [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_hom_comp]
  exact (nativeOriginalIntegration_homology_square X n).symm

set_option backward.isDefEq.respectTransparency false in
/-- Actual original-atlas integration is a quasi-isomorphism, by the proved identity transport. -/
instance originalAtlasSimplexIntegration_quasiIso : QuasiIso (IO) := by
  have hN : QuasiIso (IN) := (V).deRhamIntegrationCochain_quasiIso
  exact (AlgebraicTopology.DeRham.Comparison.SmoothSimplexDiffeomorph.quasiIso_smoothSimplexIntegration_diffeomorph_iff
    (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X).symm).mp hN

/-- Equality under the native canonical comparison is exactly equality of original-atlas integrals. -/
theorem nativeOriginalCanonicalComparison_iff (n : ℕ)
    (a : (V).deRhamCohomology n) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M n) :
    (nativeOriginalDeRhamCohomologyIso X n).hom a = b ↔
      HomologicalComplex.homologyMap (RO) n
          ((nativeOriginalOrdinaryCohomologyIso X n).hom (((V).deRhamBettiIso n).hom a)) =
        HomologicalComplex.homologyMap (IO) n b := by
  have he := ConcreteCategory.congr_hom (nativeOriginalCanonicalComparison_square X n) a
  have hi : Function.Injective (HomologicalComplex.homologyMap (IO) n) :=
    (isoOfQuasiIsoAt (IO) n).toLinearEquiv.injective
  constructor
  · intro h
    exact he.trans (congrArg (HomologicalComplex.homologyMap (IO) n) h)
  · intro h
    apply hi
    exact he.symm.trans h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceCanonicalComparison
