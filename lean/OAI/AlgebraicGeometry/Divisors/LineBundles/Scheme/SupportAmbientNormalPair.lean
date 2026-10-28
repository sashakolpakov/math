import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportRegularImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse

/-! # Support Ambient Normal Pair -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportAmbientNormalPair.BundleCycles

noncomputable section

/-! Every regular point of an integral support has an actual holomorphic
ambient normal chart cutting out the full support on that neighborhood. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic.Constructions.Differentiable
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))

abbrev schemeSupportAmbientPair :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z) (Fin p → ℂ) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z) x :=
  CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair ((SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularFixedNormalPair x)
    Subtype.val (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z).isOpenEmbedding'

theorem schemeSupportAmbientPair_mdifferentiable :
    (schemeSupportAmbientPair X Z p hp x).ambientChart.MDifferentiable
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z × (Fin p → ℂ)) :=
  CycleClass.Thom.Open.NormalPairAnalytic.Constructions.Differentiable.openTransportNormalPair_mdifferentiable (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)
    ((SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularFixedNormalPair x)
    ((SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularFixedNormalPair_ambientChart_mdifferentiable x)

theorem schemeSupportAmbientPair_analytic :
    ContMDiffOn 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z × (Fin p → ℂ)) ω
      (schemeSupportAmbientPair X Z p hp x).ambientChart (schemeSupportAmbientPair X Z p hp x).ambientChart.source :=
  CycleClass.Thom.Open.NormalPairAnalytic.Constructions.openTransportNormalPair_analytic (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)
    ((SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularFixedNormalPair x)
    (CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff (SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp) x)

theorem schemeSupportAmbientPair_symm_analytic :
    ContMDiffOn 𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z × (Fin p → ℂ))
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) ω
      (schemeSupportAmbientPair X Z p hp x).ambientChart.symm (schemeSupportAmbientPair X Z p hp x).ambientChart.target :=
  CycleClass.Thom.Open.NormalPairAnalytic.Constructions.openTransportNormalPair_symm_analytic (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)
    ((SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularFixedNormalPair x)
    (CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_symm_contMDiff (SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp) x)

theorem schemeSupportAmbientPair_avoids_boundary :
    (schemeSupportAmbientPair X Z p hp x).neighborhood ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z := by
  intro y hy
  exact CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.liftedPoint_mem_open
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) ((SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularFixedNormalPair x) ⟨y, hy⟩

theorem schemeSupportAmbientPair_zero_iff (y : (schemeSupportAmbientPair X Z p hp x).neighborhood) :
    (schemeSupportAmbientPair X Z p hp x).normalCoordinate y = 0 ↔ y.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z) := by
  refine ((schemeSupportAmbientPair X Z p hp x).mem_range_iff y).symm.trans ?_
  constructor
  · intro hy
    exact CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion_subset X Z hy
  · intro hy
    by_contra hn
    have hb : y.val ∈ CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary X Z := by
      rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary_eq]
      exact ⟨hy, hn⟩
    exact schemeSupportAmbientPair_avoids_boundary X Z p hp x y.property hb

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportAmbientNormalPair.BundleCycles
