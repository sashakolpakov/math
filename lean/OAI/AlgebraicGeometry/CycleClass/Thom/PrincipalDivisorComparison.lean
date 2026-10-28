import OAI.AlgebraicGeometry.CycleClass.Thom.RationalDivisorNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.RationalBoundary
import OAI.AlgebraicGeometry.CycleClass.Thom.DivisorIsolation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrimeRegularNeighborhood
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorSmooth

/-! # Principal Divisor Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDivisorComparison

noncomputable section

/-! The actual supported principal-divisor sum equals the global boundary
of the rational function on its actual unit domain. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.Restriction OAI.AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.Unit
  RationalRegularNormal.Constructions RationalDivisorNeighborhood.Constructions Finite.DivisorDetection.Constructions
  Supported.PrincipalDivisor.Constructions DivisorIsolation.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {g : V.carrier.functionField}
  (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative V.carrier g) (hg : g ≠ 0)

local notation "T" => TopCat.of V.analyticSpace
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain

include hg in
theorem principalDivisor_comparison_neighborhood_nonzero
    (z : Finite.DivisorDetection.Constructions.ComplementDivisorPoint V.presentation D.domain) (hm : V.carrier.ord g z.val ≠ 0) :
    ∃ W : V.carrier.Opens, z.val ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 (Supported.PrincipalDivisor.Constructions.principalDivisorSupportedClass V.presentation D.domain g) := by
  let : Smooth V.structureMap := V.presentation.smooth
  let z' : {w : V.carrier // Order.coheight w = 1} := ⟨z.val, z.property.1⟩
  let Z : Geometric.DimensionCycles.DimensionCycleSupport V 1 := Supported.PrincipalDivisor.Constructions.complementDivisorSupport V.presentation D.domain z
  have heZ : HodgeConjecture.DegreeTwo.PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z' = Z := by
    apply Subtype.ext
    rfl
  obtain ⟨U, hU, hzU, hUi, p, v, hp, he⟩ :=
    HodgeConjecture.DegreeTwo.DivisorEquations.Constructions.smooth_rationalFunction_local_equation V.structureMap z.val z.property.1
      (DivisorIsolation.Constructions.complementDivisorIsolatingOpen V.presentation D.domain z)
      (DivisorIsolation.Constructions.complementDivisorPoint_mem_isolatingOpen V.presentation D.domain z) g hg
  let : Nonempty U := ⟨⟨z.val, hzU⟩⟩
  obtain ⟨b, hb, hsm⟩ := HodgeConjecture.DegreeTwo.DivisorSmooth.Constructions.smooth_uniformizer_section_neighborhood V.structureMap U hU z.val hzU z.property.1 p hp
  obtain ⟨c, hc, hsupp⟩ := HodgeConjecture.DegreeTwo.PrimeDivisorCycleSupport.Constructions.section_uniformizer_primeCycleSupport_neighborhood V U hU z' hzU p hp
  have hbc : IsUnit (V.carrier.presheaf.germ U z.val hzU (b * c)) := by
    rw [map_mul]
    exact hb.mul hc
  obtain ⟨W, hzW, hWU, hW⟩ := HodgeConjecture.DegreeTwo.PrimeRegularNeighborhood.Constructions.exists_prime_regular_neighborhood V z' U hU hzU (b * c) hbc
  have hgood : ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W,
      y.val ∈ Z.regularAmbientOpen ∧
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b ⟨y.val, hWU y.property⟩ ≠ 0 ∧
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c ⟨y.val, hWU y.property⟩ ≠ 0 := by
    intro y
    have hy := hW y
    rw [heZ] at hy
    refine ⟨hy.1, ?_⟩
    have hn := hy.2
    rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul] at hn
    exact mul_ne_zero_iff.mp hn
  have hsupp' : ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U,
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c y ≠ 0 →
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y = 0 ↔ y.val ∈ Set.range Z.analyticInclusion) := by
    intro y hy
    rw [← heZ]
    exact hsupp y hy
  have hp0 : p ≠ 0 := by
    intro h
    apply hp.ne_zero
    rw [h, map_zero]
  have hlocal := RationalDivisorNeighborhood.Constructions.rationalGlobalBoundary_eq_supportedCycle_on_neighborhood D Z
    (Supported.PrincipalDivisor.Constructions.complementDivisorSupport_complement V.presentation D.domain z) U hU p b c hp0 v
    (V.carrier.ord g z.val) hm he hsm hsupp' W hWU hgood
  refine ⟨W, hzW, ?_⟩
  rw [DivisorIsolation.Constructions.principalDivisorSupportedClass_restrict_isolated V.presentation D.domain g z W (hWU.trans hUi)]
  rw [map_zsmul] at hlocal
  exact hlocal.trans (Int.cast_smul_eq_zsmul ℚ (V.carrier.ord g z.val) _).symm

include hg in
theorem principalDivisor_comparison_neighborhood_zero
    (z : Finite.DivisorDetection.Constructions.ComplementDivisorPoint V.presentation D.domain) (hm : V.carrier.ord g z.val = 0) :
    ∃ W : V.carrier.Opens, z.val ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 (Supported.PrincipalDivisor.Constructions.principalDivisorSupportedClass V.presentation D.domain g) := by
  obtain ⟨W, _, hzW, hWi, hzero⟩ := RationalBoundary.Constructions.Unit.rationalGlobalBoundary_local_zero_of_order_zero V.presentation D
    z.val z.property.1 (DivisorIsolation.Constructions.complementDivisorIsolatingOpen V.presentation D.domain z)
    (DivisorIsolation.Constructions.complementDivisorPoint_mem_isolatingOpen V.presentation D.domain z) hg hm
  refine ⟨W, hzW, ?_⟩
  rw [DivisorIsolation.Constructions.principalDivisorSupportedClass_restrict_isolated V.presentation D.domain g z W hWi,
    hm, Int.cast_zero, zero_smul]
  exact hzero

include hg in
theorem rationalGlobalBoundary_eq_principalDivisorSupportedClass :
    RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D = Supported.PrincipalDivisor.Constructions.principalDivisorSupportedClass V.presentation D.domain g := by
  classical
  have h (z : Finite.DivisorDetection.Constructions.ComplementDivisorPoint V.presentation D.domain) : ∃ W : V.carrier.Opens, z.val ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 (Supported.PrincipalDivisor.Constructions.principalDivisorSupportedClass V.presentation D.domain g) := by
    by_cases hm : V.carrier.ord g z.val = 0
    · exact principalDivisor_comparison_neighborhood_zero V D hg z hm
    · exact principalDivisor_comparison_neighborhood_nonzero V D hg z hm
  choose W hW he using h
  exact Finite.DivisorDetection.Constructions.relativeClass_eq_of_finite_divisor_restrictions V.presentation D.domain W hW _ _ he

include hg in
theorem principalDivisorCycle_rationalCycleClass_zero :
    V.rationalCycleClass 1 (Supported.PrincipalDivisor.Constructions.principalDivisorCycle V.presentation D.domain g) = 0 := by
  have h := RationalBoundary.Constructions.Restriction.rationalGlobalBoundary_absolute_zero V.presentation D
  rw [rationalGlobalBoundary_eq_principalDivisorSupportedClass V D hg] at h
  exact (Supported.PrincipalDivisor.Constructions.principalDivisorSupportedClass_absolute V.presentation D.domain g).symm.trans h

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDivisorComparison
