import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSupportGerm

/-! # Complex Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions

noncomputable section

/-! Geometric data for compact-support Thom integration. The data consist
only of actual manifolds and an actual closed holomorphic immersion; all
normal coordinates and cohomology classes are constructed from them. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
open scoped _root_.Manifold ContDiff _root_.Topology

structure ComplexManifold where
  complexDimension : ℕ
  analyticSpace : TopCat.{0}
  [chartedSpace : ChartedSpace (Fin complexDimension → ℂ) analyticSpace]
  [manifold : IsManifold 𝓘(ℂ, Fin complexDimension → ℂ) ω analyticSpace]
  [metrizable : MetrizableSpace analyticSpace]

attribute [instance] ComplexManifold.chartedSpace ComplexManifold.manifold ComplexManifold.metrizable

namespace ComplexManifold
abbrev analyticModel (V : ComplexManifold) := Fin V.complexDimension → ℂ
end ComplexManifold

structure ClosedComplexImmersion (V : ComplexManifold) (p : ℕ) where
  regularComplexDimension : ℕ
  regularAnalyticSpace : TopCat.{0}
  [chartedSpace : ChartedSpace (Fin regularComplexDimension → ℂ) regularAnalyticSpace]
  [manifold : IsManifold 𝓘(ℂ, Fin regularComplexDimension → ℂ) ω regularAnalyticSpace]
  regularComplementTopCatMap : regularAnalyticSpace ⟶ V.analyticSpace
  holomorphic : ContMDiff 𝓘(ℂ, Fin regularComplexDimension → ℂ) 𝓘(ℂ, V.analyticModel)
    ω regularComplementTopCatMap
  differential_injective : ∀ x, Function.Injective
    (mfderiv 𝓘(ℂ, Fin regularComplexDimension → ℂ) 𝓘(ℂ, V.analyticModel) regularComplementTopCatMap x)
  closed : Topology.IsClosedEmbedding regularComplementTopCatMap
  regularComplexDimension_add_codimension : regularComplexDimension + p = V.complexDimension

attribute [instance] ClosedComplexImmersion.chartedSpace ClosedComplexImmersion.manifold

namespace ClosedComplexImmersion

variable {V : ComplexManifold} {p : ℕ} (Z : ClosedComplexImmersion V p)

abbrev regularAmbientSpace (_Z : ClosedComplexImmersion V p) := V.analyticSpace
abbrev regularAnalyticModel := Fin Z.regularComplexDimension → ℂ
abbrev regularComplementInclusion : Z.regularAnalyticSpace → Z.regularAmbientSpace := Z.regularComplementTopCatMap

theorem continuous_regularComplementInclusion : Continuous Z.regularComplementInclusion :=
  Z.regularComplementTopCatMap.hom.continuous

theorem isClosedEmbedding_regularComplementInclusion : Topology.IsClosedEmbedding Z.regularComplementInclusion :=
  Z.closed

theorem isProperMap_regularComplementTopCatMap : IsProperMap Z.regularComplementTopCatMap := Z.closed.isProperMap

instance source_metrizable : MetrizableSpace Z.regularAnalyticSpace :=
  Z.closed.isEmbedding.metrizableSpace

theorem contMDiff_regularComplementInclusion (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel) r Z.regularComplementInclusion :=
  Z.holomorphic.of_le le_top

theorem regularComplement_isImmersionAt (x : Z.regularAnalyticSpace) :
    Manifold.IsImmersionAt 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel)
      ω Z.regularComplementInclusion x :=
  ComplexPoints.Analytic.ImmersionNormalForm.isImmersionAt_of_injective_mfderiv Z.regularComplementInclusion x
    (Z.holomorphic x) (Z.differential_injective x)

theorem regularComplement_complexImmersionCodimension :
    Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension Z.regularAnalyticModel V.analyticModel = p := by
  change Module.finrank ℂ V.analyticModel - Module.finrank ℂ Z.regularAnalyticModel = p
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
  have h := Z.regularComplexDimension_add_codimension
  omega

theorem regularFixedComplementImmersion : Manifold.IsImmersionOfComplement (Fin p → ℂ)
    𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel) ω Z.regularComplementInclusion := by
  have h := Geometric.ComplexNormalAtlas.Cycles.complexImmersion_standardComplement Z.regularComplementInclusion Z.holomorphic Z.differential_injective
  rw [Z.regularComplement_complexImmersionCodimension] at h
  exact h

def regularFixedNormalPair (x : Z.regularAnalyticSpace) :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x :=
  ComplexPoints.Analytic.NormalPairRecenter.normalPairOfImmersion (Z.regularFixedComplementImmersion x) Z.closed.isEmbedding

theorem regularFixedNormalPair_ambientChart (x : Z.regularAnalyticSpace) :
    (Z.regularFixedNormalPair x).ambientChart = ComplexPoints.Analytic.NormalPairRecenter.immersionNormalCoordinates (Z.regularFixedComplementImmersion x) := rfl

theorem regularFixedNormalPair_ambientChart_mdifferentiable (x : Z.regularAnalyticSpace) :
    (Z.regularFixedNormalPair x).ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) :=
  ComplexPoints.Analytic.NormalCoordinatesDifferentiable.normalPairOfImmersion_ambientChart_mdifferentiable (Z.regularFixedComplementImmersion x)
    Z.closed.isEmbedding (by simp)

def regularThomComplementOpen : Opens Z.regularAmbientSpace :=
  Geometric.EmbeddedSupportComplement.Cycles.embeddedSupportComplement Z.regularComplementInclusion Z.closed

abbrev regularThomSheafComplex :=
  Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen

def regularThomClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
    (Set.range Z.regularComplementInclusion)ᶜ (2 * p) :=
  Degree.Constructions.ThomClass.complexThomClassInDegree Z.regularComplementInclusion Z.holomorphic
    Z.differential_injective Z.closed p Z.regularComplement_complexImmersionCodimension

theorem regularThomClass_restrict_normalPair (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ))) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (Set.range Z.regularComplementInclusion)ᶜ P.openNeighborhood (2 * p) Z.regularThomClass =
    P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) :=
  (Degree.Constructions.ThomClass.complexThomClassInDegree_restrict Z.regularComplementInclusion Z.holomorphic
    Z.differential_injective Z.closed p Z.regularComplement_complexImmersionCodimension x P hP).trans
    P.rationalClassFin_eq_normalPullback

end ClosedComplexImmersion

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions
