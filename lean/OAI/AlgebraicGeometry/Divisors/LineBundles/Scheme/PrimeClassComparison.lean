import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteCycleClass
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace

/-! # Prime Class Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrimeClassComparison.BundleCycles

noncomputable section

/-! In codimension one the general canonical cycle class agrees with
the already constructed divisor Thom class and its principal boundary. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (z : {x : X.left // Order.coheight x = 1})

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemePrimeSupport_codimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) X.hom + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom :=
  DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one X.hom z.val z.property

theorem schemeSupportedCycleClass_prime :
    SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) 1 (schemePrimeSupport_codimension X z) = CycleClass.Thom.SchemeDivisor.Module.Constructions.supportedDivisorClass X z := by
  apply Eq.symm
  apply SupportedCycleClass.BundleCycles.schemeSupportedCycleClass_unique X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) 1 (schemePrimeSupport_codimension X z)
  exact CycleClass.Thom.SchemeDivisor.Module.Constructions.supportedDivisorClass_restrict X z

theorem schemeAbsoluteCycleClass_prime :
    AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) 1 (schemePrimeSupport_codimension X z) = CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z :=
  congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ 2)
    (schemeSupportedCycleClass_prime X z)

theorem schemeCycleClass_prime :
    AbsoluteCycleClass.BundleCycles.schemeCycleClass X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) 1 (schemePrimeSupport_codimension X z) = CycleClass.Thom.SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass X z := by
  change cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n : Type)) (two_mul 1))
    (AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z) 1 (schemePrimeSupport_codimension X z)) = _
  exact schemeAbsoluteCycleClass_prime X z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrimeClassComparison.BundleCycles
