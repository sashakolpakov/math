import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationTopology
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.AbsoluteClass

/-! # Component Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles

noncomputable section

section

/-! The actual graph normal cone over each integral source component
is a smooth integral affine-space bundle, with its genuine inclusion
into the full cone. The original morphism remains arbitrary. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier)

local notation "V" => X.componentVariety C
local notation "i" => X.componentInclusion C
local notation "N" => pullback (OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Chow.BundleCycles.graphNormalProjection f) i
local notation "q" => pullback.snd (OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Chow.BundleCycles.graphNormalProjection f) i

local instance : IsOpenImmersion i := X.componentInclusion_isOpenImmersion C
local instance : IsIntegral (V).toOver.left := inferInstanceAs (IsIntegral (V).carrier)
local instance : Smooth (V).toOver.hom := inferInstanceAs (Smooth (V).structureMap)

def graphNormalComponentOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (q ≫ (V).structureMap)

def graphNormalComponentProjectionOver : graphNormalComponentOver f C ⟶ (V).toOver := Over.homMk q rfl

def graphNormalComponentInclusionOver : graphNormalComponentOver f C ⟶ Graph.Conormal.BundleCycles.graphConeOver f :=
  Over.homMk (pullback.fst (Graph.Chow.BundleCycles.graphNormalProjection f) i) (by
    change pullback.fst (Graph.Chow.BundleCycles.graphNormalProjection f) i ≫ Graph.Chow.BundleCycles.graphConeStructureMap f = q ≫ (V).structureMap
    rw [← Graph.Chow.BundleCycles.graphConeStructureMap_normal, ← Category.assoc, pullback.condition, Category.assoc,
      X.componentInclusion_over C])

instance graphNormalComponentInclusionOver_open : IsOpenImmersion (graphNormalComponentInclusionOver f C).left :=
  inferInstanceAs (IsOpenImmersion (pullback.fst (Graph.Chow.BundleCycles.graphNormalProjection f) i))

instance graphNormalComponentProjectionOver_smooth : Smooth (graphNormalComponentProjectionOver f C).left :=
  inferInstanceAs (Smooth q)

instance graphNormalComponentProjectionOver_geometricallyIntegral :
    GeometricallyIntegral (graphNormalComponentProjectionOver f C).left := inferInstanceAs (GeometricallyIntegral q)

instance graphNormalComponentOver_integral : IsIntegral (graphNormalComponentOver f C).left := by
  exact @GeometricallyIntegral.isIntegral_of_isLocallyNoetherian N (V).carrier q
    (graphNormalComponentProjectionOver_geometricallyIntegral f C) inferInstance inferInstance inferInstance inferInstance

instance graphNormalComponentOver_smooth : Smooth (graphNormalComponentOver f C).hom :=
  smooth_comp q (V).structureMap

instance graphNormalComponentOver_noetherian : AlgebraicGeometry.IsNoetherian (graphNormalComponentOver f C).left := by
  exact @Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian N (Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker) inferInstance
    (pullback.fst (Graph.Chow.BundleCycles.graphNormalProjection f) i) (graphNormalComponentInclusionOver_open f C)

instance graphNormalComponentOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (graphNormalComponentOver f C)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (graphNormalComponentInclusionOver f C)).isEmbedding.metrizableSpace

theorem graphNormalComponentProjectionOver_charts : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts (graphNormalComponentProjectionOver f C).left :=
  (ComponentRank.BundleCycles.graphNormalComponent_hasAffineSpaceChartsOfRank f C).forget

end

/-! On every actual integral source component, normal extension of
an arbitrary integral cycle support agrees with Betti pullback along
the original graph-normal projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier)

local notation "V" => X.componentVariety C
local notation "N" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles.graphNormalComponentOver f C
local notation "q" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles.graphNormalComponentProjectionOver f C
local notation "h" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles.graphNormalComponentProjectionOver_charts f C

local instance : IsIntegral (V).toOver.left := inferInstanceAs (IsIntegral (V).carrier)
local instance : Smooth (V).toOver.hom := inferInstanceAs (Smooth (V).structureMap)
local instance : AlgebraicGeometry.IsNoetherian (V).toOver.left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (V).carrier)
local instance : IsLocallyNoetherian (V).toOver.left :=
  inferInstanceAs (IsLocallyNoetherian (V).carrier)

variable (B : IrreducibleCloseds (X.componentVariety C).carrier) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B (X.componentVariety C).structureMap + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety C).structureMap)

include hp in
theorem graphNormalComponentSupport_codimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Integral.PulledSupport.BundleCycles.integralPulledSupport (q).left B) (N).hom + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (N).hom := AffineBundle.SupportedClass.Cycles.affineBundleSupport_codimension q h B p hp

theorem graphNormalComponentSupportedClass_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map q)
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo q B (Integral.PulledSupport.BundleCycles.integralPulledSupport (q).left B)
        (Integral.PulledSupport.BundleCycles.integralPulledSupport_coe (q).left B)) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass (V).toOver B p hp) =
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (Integral.PulledSupport.BundleCycles.integralPulledSupport (q).left B) p
        (graphNormalComponentSupport_codimension f C B p hp) :=
  AffineBundle.SupportedClass.Cycles.schemeSupportedCycleClass_affineBundle q h B p hp

theorem graphNormalComponentCycleClass_pullback :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) q (Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass (V).toOver B p hp) =
      Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass N (Integral.PulledSupport.BundleCycles.integralPulledSupport (q).left B) p
        (graphNormalComponentSupport_codimension f C B p hp) :=
  AffineBundle.AbsoluteClass.Cycles.schemeCycleClass_affineBundle q h B p hp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles
