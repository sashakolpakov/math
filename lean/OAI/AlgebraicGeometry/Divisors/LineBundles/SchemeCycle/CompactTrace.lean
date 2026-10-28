import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.FundamentalTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.TraceStage
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Projection

/-! # Compact Trace -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CompactTrace.BundleCycles

noncomputable section

/-! Compact integration of a general canonical cycle class is the
relative pushforward of its regular support's independent compact
fundamental class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Projection.Constructions.Construction

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

abbrev schemeCycleTraceDegree := 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z).hom

local notation "D" => OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "n" => OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CompactTrace.BundleCycles.schemeCycleTraceDegree X Z

local instance : T2Space (D).regularAnalyticSpace :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z)).t2Space

def schemeCycleRegularAmbientMap : (D).regularAnalyticSpace ⟶ T :=
  (D).regularComplementTopCatMap ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T)

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycleRegularAmbientMap_eq_schemeMap :
    schemeCycleRegularAmbientMap X Z p hp = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z) := by
  ext x
  rfl

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycleRegularCompactPairMapsTo (K : Compacts G) :
    Set.MapsTo (schemeCycleRegularAmbientMap X Z p hp) ((D).regularComplementTopCatMap ⁻¹' (K : Set G))ᶜ
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ := by
  rintro x hx ⟨y, hy, he⟩
  apply hx
  change (D).regularComplementTopCatMap x ∈ (K : Set G)
  exact (Subtype.ext he) ▸ hy

def schemeCycleRegularCompactProjection (K : Compacts G) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ T (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ n :=
  HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (schemeCycleRegularAmbientMap X Z p hp)
    (schemeCycleRegularCompactPairMapsTo X Z p hp K)) n
    (CycleClass.Thom.ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (D).regularComplexDimension
      ((D).regularComplementTopCatMap ⁻¹' (K : Set G))
      ((D).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact))

theorem schemeCycleClass_compactTrace_openSupport (K : Compacts G)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) n (FundamentalTrace.BundleCycles.schemeCycle_trace_degree X Z p hp)
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hp)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K) n b) =
    CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ n b
      (schemeCycleRegularCompactProjection X Z p hp K) := by
  let i : TopCat.of G ⟶ T := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T)
  have hi : Set.MapsTo i (K : Set G)ᶜ (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ := by
    rintro x hx ⟨y, hy, he⟩
    exact hx ((Subtype.ext he) ▸ hy)
  let bG := (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso (X := T) G K n).hom b
  have he := CycleClass.Thom.Open.CompactPairing.Constructions.evaluation_openStage
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    G K (2 * p) n (FundamentalTrace.BundleCycles.schemeCycle_trace_degree X Z p hp) (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hp) b
  have hr := congrArg
    (fun a => AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := G) (2 * p) n (FundamentalTrace.BundleCycles.schemeCycle_trace_degree X Z p hp) a
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of G) K n bG))
    (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass_regularRestriction X Z p hp)
  have ht := FundamentalTrace.BundleCycles.schemeRegularSupportThomClass_fundamentalTrace X Z p hp
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of G) K n bG)
  have hs := CycleClass.Thom.Immersion.TraceStage.Constructions.Construction.fundamentalTrace_stage_rationalPushforward D K bG
  have hn := CycleClass.Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality (ModuleCat.of ℚ ℚ) i hi n b
    (HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (D).regularComplementTopCatMap
        (A := ((D).regularComplementTopCatMap ⁻¹' (K : Set G))ᶜ) (B := (K : Set G)ᶜ)
        (fun _ hx => hx)) n
      (CycleClass.Thom.ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (D).regularComplexDimension
        ((D).regularComplementTopCatMap ⁻¹' (K : Set G))
        ((D).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact)))
  have hc := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ (D).regularComplementTopCatMap i
      (A := ((D).regularComplementTopCatMap ⁻¹' (K : Set G))ᶜ)
      (B := (K : Set G)ᶜ) (C := (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ)
      (fun _ hx => hx) hi n)
    (CycleClass.Thom.ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (D).regularComplexDimension
      ((D).regularComplementTopCatMap ⁻¹' (K : Set G))
      ((D).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact))
  exact he.trans (hr.trans (ht.trans (hs.trans (hn.trans
    (congrArg (CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ n b) hc)))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CompactTrace.BundleCycles
