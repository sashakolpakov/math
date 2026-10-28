import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen

/-! # Prime Regular -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeRegular.Constructions

noncomputable section

/-! Every point of the full affine-source prime divisor above the constructed normalization-divisor good open is in its actual regular analytic locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Range.Constructions.BranchRange OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Regular
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (z : {x : X.left // Order.coheight x = 1})

omit [IsIntegral X.left] in
theorem affinePrime_regular_over_goodAmbient (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hx : x ∈ Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
    (hg : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) ∈
      NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a z)) :
    x ∈ Set.range (Scheme.RegularSupport.Constructions.regularInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) := by
  have hy := (Set.ext_iff.mp (Open.PrimeSupport.Constructions.primeSupport_analytic_preimage a z) x).mpr hx
  obtain ⟨l, hl⟩ := NormalizationDivisor.Range.Constructions.BranchRange.fullPrime_point_mem_cover_range V W (Open.PrimeSupport.Constructions.ambientPrime a z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) hy hg
  apply (Set.ext_iff.mp (Open.PrimeRegularRange.Constructions.regularInclusion_preimage a z) x).mp
  refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (NormalizationDivisor.Open.Constructions.Regular.sourceToRegular V W (Open.PrimeSupport.Constructions.ambientPrime a z)) l, ?_⟩
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (NormalizationDivisor.Open.Constructions.Regular.sourceToRegular V W (Open.PrimeSupport.Constructions.ambientPrime a z))
    (Scheme.RegularSupport.Constructions.regularToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (Open.PrimeSupport.Constructions.ambientPrime a z))) l).symm.trans hl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeRegular.Constructions
