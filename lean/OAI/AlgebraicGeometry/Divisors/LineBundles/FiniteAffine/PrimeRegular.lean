import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.SupportRange
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange

/-! # Prime Regular -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrimeRegular.BundleCycles

noncomputable section

/-! The full affine source prime divisor is regular over the actual retained finite-image open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (z : {x : X.left // Order.coheight x = 1})

omit [IsIntegral X.left] in
omit [AlgebraicGeometry.IsIntegral S.left] [AlgebraicGeometry.IsIntegral N.left] in
theorem finiteAffinePrime_regular_over_retained (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hx : x ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)))
    (hg : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) ∈
      FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) :
    x ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z)) := by
  have hy := (Set.ext_iff.mp (CycleClass.Thom.Open.PrimeSupport.Constructions.primeSupport_analytic_preimage a z) x).mpr hx
  obtain ⟨l, hl⟩ := FiniteSupport.SupportRange.BundleCycles.finiteSupportFullSupport_point_mem_cover_range k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) hy hg
  apply (Set.ext_iff.mp (CycleClass.Thom.Open.PrimeRegularRange.Constructions.regularInclusion_preimage a z) x).mp
  refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceToRegular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) l, ?_⟩
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (FiniteSupport.Cover.BundleCycles.finiteSupportSourceToRegular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)))
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient (S) (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport (S) (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) l).symm.trans hl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrimeRegular.BundleCycles
