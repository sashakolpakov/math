import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportRegularImmersion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteCycleClass
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Trace
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.CompactPairing

/-! # Fundamental Trace -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.FundamentalTrace.BundleCycles

noncomputable section

/-! Canonical cycle classes on general smooth schemes have the
independent fundamental trace of their regular support on every compact
test avoiding the singular boundary. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "d" => OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom
local notation "s" => OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))

def schemeCycleFundamentalTrace :=
  CycleClass.Thom.Immersion.Trace.Constructions.Construction.fundamentalTrace (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp)

include hp in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycle_trace_degree : 2 * p + 2 * s = 2 * d := by
  have hs := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq X Z
  have hd := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom
  omega

local instance : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : QuasiCompact X.hom := inferInstance
  exact ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable X

local instance : SecondCountableTopology (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularAnalyticSpace :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z)).secondCountableTopology

theorem schemeRegularSupportThomClass_fundamentalTrace
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of G) (2 * s)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (M := G) (2 * p) (2 * s) (schemeCycle_trace_degree X Z p hp)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of G)
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z))ᶜ (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass X Z p hp)) b =
      schemeCycleFundamentalTrace X Z p hp b :=
  CycleClass.Thom.Immersion.Trace.Constructions.Construction.regularThomClass_fundamentalTrace
    (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp) b

theorem schemeAbsoluteCycleClass_regularTrace
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of G) (2 * s)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) (2 * s)
      (schemeCycle_trace_degree X Z p hp) (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hp)
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) G (2 * s) b) =
      schemeCycleFundamentalTrace X Z p hp b := by
  have h₁ := CycleClass.Thom.Open.CompactPairing.Constructions.evaluation_openExtension d G
    (2 * p) (2 * s) (schemeCycle_trace_degree X Z p hp) (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X Z p hp) b
  have h₂ := congrArg
    (fun a => AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (M := G) (2 * p) (2 * s) (schemeCycle_trace_degree X Z p hp) a b)
    (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass_regularRestriction X Z p hp)
  exact h₁.trans (h₂.trans (schemeRegularSupportThomClass_fundamentalTrace X Z p hp b))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.FundamentalTrace.BundleCycles
