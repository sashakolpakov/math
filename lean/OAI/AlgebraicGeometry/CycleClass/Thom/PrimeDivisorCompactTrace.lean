import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.TraceStage
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Projection

/-! # Prime Divisor Compact Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorCompactTrace

noncomputable section

/-! Compact integration of an actual divisor class equals the relative
pushforward of its regular locus's actual compact fundamental class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion.Constructions
  ProperImage.Projection.Constructions.Construction

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (z : {x : X.left // Order.coheight x = 1})

local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X (OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)
local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
abbrev divisorDegree := 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom

local notation "n" => OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorCompactTrace.Constructions.divisorDegree X z

/-- The actual continuous regular-locus inclusion in the whole smooth scheme. -/
def regularAmbientMap : (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticSpace ⟶ T :=
  (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap ≫ Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T)

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem regularAmbientMap_eq_schemeMap :
    regularAmbientMap X z = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (Scheme.RegularSupport.Constructions.regularToAmbient X (SchemeDivisor.Purity.Constructions.primeSupport X z)) := by
  ext x
  rfl

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem regularCompactPairMapsTo (K : Compacts G) :
    Set.MapsTo (regularAmbientMap X z) ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap ⁻¹' (K : Set G))ᶜ
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ := by
  rintro x hx ⟨y, hy, he⟩
  apply hx
  change (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap x ∈ (K : Set G)
  exact (Subtype.ext he) ▸ hy

/-- The independently defined compact fundamental class pushed into the
original ambient scheme at the given actual compact support. -/
def regularCompactProjection (K : Compacts G) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ T (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ n :=
  HomologicalComplex.homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (regularAmbientMap X z)
    (regularCompactPairMapsTo X z K)) n
    (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
      ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap ⁻¹' (K : Set G))
      ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact))

theorem absoluteDivisorClass_compactTrace_openSupport (K : Compacts G)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ n) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 2 n (PrimeDivisorTrace.Constructions.primeDivisor_trace_degree X z)
      (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) T (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K) n b) =
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ n b
      (regularCompactProjection X z K) := by
  let i : TopCat.of G ⟶ T := Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T)
  have hi : Set.MapsTo i (K : Set G)ᶜ (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ := by
    rintro x hx ⟨y, hy, he⟩
    exact hx ((Subtype.ext he) ▸ hy)
  let bG := (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso (X := T) G K n).hom b
  have he := Open.CompactPairing.Constructions.evaluation_openStage
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    G K 2 n (PrimeDivisorTrace.Constructions.primeDivisor_trace_degree X z) (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z) b
  rw [SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass_regularRestriction] at he
  have ht := PrimeDivisorTrace.Constructions.regularDivisorThomClass_fundamentalTrace X z
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of G) K n bG)
  have hs := Immersion.TraceStage.Constructions.Construction.fundamentalTrace_stage_rationalPushforward D K bG
  have hn := Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeHomologyEvaluation_naturality (ModuleCat.of ℚ ℚ) i hi n b
    (HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap
        (A := ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap ⁻¹' (K : Set G))ᶜ) (B := (K : Set G)ᶜ)
        (fun _ hx => hx)) n
      (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
        ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap ⁻¹' (K : Set G))
        ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact)))
  have hc := ConcreteCategory.congr_hom
    (Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap i
      (A := ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap ⁻¹' (K : Set G))ᶜ)
      (B := (K : Set G)ᶜ) (C := (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ)
      (fun _ hx => hx) hi n)
    (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplexDimension
      ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularComplementTopCatMap ⁻¹' (K : Set G))
      ((PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).isProperMap_regularComplementTopCatMap.isCompact_preimage K.isCompact))
  exact he.trans (ht.trans (hs.trans (hn.trans
    (congrArg (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ T
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) G K : Set T)ᶜ n b) hc))))

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorCompactTrace
