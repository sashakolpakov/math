import OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Trace

/-! # Prime Divisor Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorTrace.Constructions

noncomputable section

/-! The canonical prime-divisor class on a general smooth scheme has the
actual regular-locus fundamental trace on every compact test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsNoetherian X.left] (z : {x : X.left // Order.coheight x = 1})

/-- Integration of the genuine proper pullback against the regular divisor's
canonical complex fundamental class. -/
def primeDivisorFundamentalTrace := Immersion.Trace.Constructions.Construction.fundamentalTrace (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z)

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsNoetherian X.left] in
theorem primeDivisor_trace_degree :
    2 + 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom =
      2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  have h := SchemeDivisor.Purity.Constructions.primeRegularDimension_add_one X z
  omega

local instance : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : QuasiCompact X.hom := inferInstance
  exact ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable X

local instance : SecondCountableTopology (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z).regularAnalyticSpace :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (Scheme.RegularSupport.Constructions.regularToAmbient X (SchemeDivisor.Purity.Constructions.primeSupport X z))).secondCountableTopology

theorem regularDivisorThomClass_fundamentalTrace
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Scheme.RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
      (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) 2
      (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom)
      (primeDivisor_trace_degree X z)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (Scheme.RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
        (Set.range (Scheme.RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ 2 (SchemeDivisor.Module.Constructions.regularDivisorThomClass X z)) b =
    primeDivisorFundamentalTrace X z b :=
  Immersion.Trace.Constructions.Construction.regularThomClass_fundamentalTrace (PrimeDivisorImmersion.Constructions.primeDivisorImmersion X z) b

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorTrace.Constructions
