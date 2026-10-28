import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalDivisorNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Isolation
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeNeighborhood
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorSmooth

/-! # Principal Divisor Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalDivisorComparison

noncomputable section

/-! The genuine rational-function boundary equals the finite sum of canonical
supported divisor classes, with the actual scheme orders, on arbitrary
metrizable smooth integral complex schemes of finite type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalBoundary.Constructions.Restriction
  RationalBoundary.Constructions.Unit RationalDivisorNeighborhood.Constructions RationalRegularNormal.Constructions
  FiniteDivisorDetection.Constructions SupportedPrincipalDivisor.Constructions SchemeDivisor.Isolation.Constructions
  PrimeNeighborhood.Constructions RegularSupport.Constructions SchemeDivisor.Purity.Constructions HodgeConjecture.DegreeTwo.DivisorSmooth.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g) (hg : g ≠ 0)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "O" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X D.domain

include hg in
theorem principalDivisor_comparison_neighborhood_nonzero
    (z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) (hm : X.left.ord g z.val ≠ 0) :
    ∃ W : X.left.Opens, z.val ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (SectionEvaluation.Constructions.analyticOpen X W) 2
        (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (SectionEvaluation.Constructions.analyticOpen X W) 2
        (SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass X D.domain g) := by
  let z' : {x : X.left // Order.coheight x = 1} := ⟨z.val, z.property.1⟩
  obtain ⟨U, hU, hzU, hUi, p, v, hp, he⟩ :=
    HodgeConjecture.DegreeTwo.DivisorEquations.Constructions.smooth_rationalFunction_local_equation X.hom z.val z.property.1
      (SchemeDivisor.Isolation.Constructions.complementDivisorIsolatingOpen X D.domain z)
      (SchemeDivisor.Isolation.Constructions.complementDivisorPoint_mem_isolatingOpen X D.domain z) g hg
  let : Nonempty U := ⟨⟨z.val, hzU⟩⟩
  obtain ⟨b, hb, hsm⟩ := HodgeConjecture.DegreeTwo.DivisorSmooth.Constructions.smooth_uniformizer_section_neighborhood X.hom U hU z.val hzU z.property.1 p hp
  obtain ⟨c, hc, hsupp⟩ := PrimeNeighborhood.Constructions.section_uniformizer_primeSupport_neighborhood X z' U hU hzU p hp
  have hbc : IsUnit (X.left.presheaf.germ U z.val hzU (b * c)) := by
    rw [map_mul]
    exact hb.mul hc
  obtain ⟨W, hzW, hWU, hW⟩ := PrimeNeighborhood.Constructions.exists_prime_regular_neighborhood X z' U hU hzU (b * c) hbc
  have hgood : ∀ y : SectionEvaluation.Constructions.analyticOpen X W,
      y.val ∈ RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z') ∧
      SectionEvaluation.Constructions.sectionEvaluationOn X U b ⟨y.val, hWU y.property⟩ ≠ 0 ∧
      SectionEvaluation.Constructions.sectionEvaluationOn X U c ⟨y.val, hWU y.property⟩ ≠ 0 := by
    intro y
    have hy := hW y
    refine ⟨hy.1, ?_⟩
    have hn := hy.2
    rw [SectionEvaluation.Constructions.sectionEvaluationOn_mul] at hn
    exact mul_ne_zero_iff.mp hn
  have hp0 : p ≠ 0 := by
    intro h
    apply hp.ne_zero
    rw [h, map_zero]
  have hlocal := RationalDivisorNeighborhood.Constructions.rationalGlobalBoundary_eq_supportedCycle_on_neighborhood D z'
    (SupportedPrincipalDivisor.Constructions.complementDivisorSupport_complement X D.domain z) U hU p b c hp0 v
    (X.left.ord g z.val) hm he hsm hsupp W hWU hgood
  refine ⟨W, hzW, ?_⟩
  rw [SchemeDivisor.Isolation.Constructions.principalDivisorSupportedClass_restrict_isolated X D.domain g z W (hWU.trans hUi)]
  rw [map_zsmul] at hlocal
  exact hlocal.trans (Int.cast_smul_eq_zsmul ℚ (X.left.ord g z.val) _).symm

include hg in
theorem principalDivisor_comparison_neighborhood_zero
    (z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) (hm : X.left.ord g z.val = 0) :
    ∃ W : X.left.Opens, z.val ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (SectionEvaluation.Constructions.analyticOpen X W) 2
        (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (SectionEvaluation.Constructions.analyticOpen X W) 2
        (SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass X D.domain g) := by
  obtain ⟨W, _, hzW, hWi, hzero⟩ := RationalBoundary.Constructions.Unit.rationalGlobalBoundary_local_zero_of_order_zero X D
    z.val z.property.1 (SchemeDivisor.Isolation.Constructions.complementDivisorIsolatingOpen X D.domain z)
    (SchemeDivisor.Isolation.Constructions.complementDivisorPoint_mem_isolatingOpen X D.domain z) hg hm
  refine ⟨W, hzW, ?_⟩
  rw [SchemeDivisor.Isolation.Constructions.principalDivisorSupportedClass_restrict_isolated X D.domain g z W hWi,
    hm, Int.cast_zero, zero_smul]
  exact hzero

include hg in
theorem rationalGlobalBoundary_eq_principalDivisorSupportedClass :
    RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D = SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass X D.domain g := by
  classical
  have h (z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) : ∃ W : X.left.Opens, z.val ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (SectionEvaluation.Constructions.analyticOpen X W) 2
        (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (SectionEvaluation.Constructions.analyticOpen X W) 2
        (SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass X D.domain g) := by
    by_cases hm : X.left.ord g z.val = 0
    · exact principalDivisor_comparison_neighborhood_zero X D hg z hm
    · exact principalDivisor_comparison_neighborhood_nonzero X D hg z hm
  choose W hW he using h
  exact FiniteDivisorDetection.Constructions.relativeClass_eq_of_finite_divisor_restrictions X D.domain W hW _ _ he

include hg in
theorem principalDivisorSupportedClass_absolute_zero :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T (O : Set T) 2
      (SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass X D.domain g) = 0 := by
  rw [← rationalGlobalBoundary_eq_principalDivisorSupportedClass X D hg]
  exact RationalBoundary.Constructions.Restriction.rationalGlobalBoundary_absolute_zero X D

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalDivisorComparison
