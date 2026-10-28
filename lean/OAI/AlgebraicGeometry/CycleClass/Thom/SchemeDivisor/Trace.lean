import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalDivisorComparison
import OAI.AlgebraicGeometry.CycleClass.Thom.PrimeDivisorTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.CompactPairing

/-! # Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace

noncomputable section

/-! Absolute canonical divisor classes and their genuine regular-locus
integration, on arbitrary smooth integral complex schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Class

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions
  Scheme.SectionEvaluation.Constructions Scheme.SupportedPrincipalDivisor.Constructions Scheme.FiniteDivisorDetection.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

/-- Forget only the support of the previously constructed actual prime-divisor class. -/
def absoluteDivisorClass (z : {x : X.left // Order.coheight x = 1}) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (Purity.Constructions.primeSupport X z)))ᶜ 2 (Module.Constructions.supportedDivisorClass X z)

theorem absoluteDivisorClass_regularRestriction (z : {x : X.left // Order.coheight x = 1}) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Scheme.RegularSupport.Constructions.regularAmbientOpen X (Purity.Constructions.primeSupport X z) : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) 2
      (absoluteDivisorClass X z) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
      (TopCat.of (Scheme.RegularSupport.Constructions.regularAmbientOpen X (Purity.Constructions.primeSupport X z)))
      (Set.range (Scheme.RegularSupport.Constructions.regularComplementInclusion X (Purity.Constructions.primeSupport X z)))ᶜ 2
      (Module.Constructions.regularDivisorThomClass X z) := by
  have h := ConcreteCategory.congr_hom
    (Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Scheme.RegularSupport.Constructions.regularAmbientOpen X (Purity.Constructions.primeSupport X z) : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (Open.RestrictionTarget.Constructions.openRestrictionMapsTo _ _ _ _ (Module.Constructions.regularDivisorComplement_eq X z)) 2)
    (Module.Constructions.supportedDivisorClass X z)
  exact h.symm.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
    (TopCat.of (Scheme.RegularSupport.Constructions.regularAmbientOpen X (Purity.Constructions.primeSupport X z)))
    (Set.range (Scheme.RegularSupport.Constructions.regularComplementInclusion X (Purity.Constructions.primeSupport X z)))ᶜ 2)
    (Module.Constructions.supportedDivisorClass_restrict X z))

theorem absoluteDivisorClass_regularTrace (z : {x : X.left // Order.coheight x = 1})
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Scheme.RegularSupport.Constructions.regularAmbientOpen X (Purity.Constructions.primeSupport X z)))
      (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)).hom)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 2
      (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (Purity.Constructions.primeSupport X z)).hom)
      (PrimeDivisorTrace.Constructions.primeDivisor_trace_degree X z) (absoluteDivisorClass X z)
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Scheme.RegularSupport.Constructions.regularAmbientOpen X (Purity.Constructions.primeSupport X z)) _ b) =
    PrimeDivisorTrace.Constructions.primeDivisorFundamentalTrace X z b := by
  rw [Open.CompactPairing.Constructions.evaluation_openExtension, absoluteDivisorClass_regularRestriction]
  exact PrimeDivisorTrace.Constructions.regularDivisorThomClass_fundamentalTrace X z b

theorem complementDivisorSupportedClass_absolute (R : X.left.Opens) (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Scheme.SectionEvaluation.Constructions.analyticOpen X R) 2 (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupportedClass X R z) =
    absoluteDivisorClass X ⟨z.val, z.property.1⟩ := by
  have h := ConcreteCategory.congr_hom
    (Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupport_complement X R z) 2)
    (Module.Constructions.supportedDivisorClass X ⟨z.val, z.property.1⟩)
  simpa only [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, Category.comp_id, ConcreteCategory.comp_apply,
    Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupportedClass, absoluteDivisorClass] using h

local instance (R : X.left.Opens) [Nonempty R] : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R) := Fintype.ofFinite _

/-- The original orders, including poles, sum to zero in actual absolute cohomology. -/
theorem principal_absolute_sum_zero {g : X.left.functionField}
    (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g) (hg : g ≠ 0) :
    ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, (X.left.ord g z.val : ℚ) •
      absoluteDivisorClass X ⟨z.val, z.property.1⟩ = 0 := by
  have h := Scheme.PrincipalDivisorComparison.Constructions.principalDivisorSupportedClass_absolute_zero X D hg
  simp only [Scheme.SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass, map_sum, map_smul] at h
  refine Eq.trans (Finset.sum_congr rfl ?_) h
  intro z _
  exact congrArg (fun a => (X.left.ord g z.val : ℚ) • a)
    (complementDivisorSupportedClass_absolute X D.domain z).symm

end Constructions.Class

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace
