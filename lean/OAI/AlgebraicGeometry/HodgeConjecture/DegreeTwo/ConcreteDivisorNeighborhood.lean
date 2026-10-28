import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorLocalComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrimeRegularNeighborhood
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorSmooth

/-! # Concrete Divisor Neighborhood -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ConcreteDivisorNeighborhood.Constructions

noncomputable section

section

/-!
# DegreeTwo: actual nonzero divisor coefficients compare with the full Thom sum

The finite-divisor isolating open removes the other summands. The smooth
parameter and support neighborhoods are constructed at the actual divisor
point, then the proved neighborhood comparison supplies its exact order.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem rationalSectionChern_divisorThom_comparison_neighborhood_nonzero
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation)
    (z : L.ReferenceDivisorPoint) (hm : L.rationalSectionOrder z.val ≠ 0) :
    ∃ W : V.carrier.Opens, z.val ∈ W ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 L.rationalSectionChernRelativeClass =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2
        ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • L.rationalSectionDivisorThomClass) := by
  let z' : {w : V.carrier // Order.coheight w = 1} := ⟨z.val, z.property.1⟩
  let Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1 := L.referenceDivisorSupport z
  have heZ : PrimeDivisorCycleSupport.Constructions.primeDivisorCycleSupport V z' = Z := by
    apply Subtype.ext
    rfl
  obtain ⟨U, hU, hzU, hUi, p, v, b, hp, hb, hsm, he⟩ :=
    DivisorSmooth.Constructions.rationalSection_smooth_local_equation L z.val z.property.1 z.val (L.mem_trivializingOpen z.val)
  let : Nonempty U := ⟨⟨z.val, hzU⟩⟩
  obtain ⟨c, hc, hsupp⟩ :=
    PrimeDivisorCycleSupport.Constructions.section_uniformizer_primeCycleSupport_neighborhood V U hU z' hzU p hp
  have hbc : IsUnit (V.carrier.presheaf.germ U z.val hzU (b * c)) := by
    rw [map_mul]
    exact hb.mul hc
  obtain ⟨G, hzG, hGU, hG⟩ := PrimeRegularNeighborhood.Constructions.exists_prime_regular_neighborhood V z' U hU hzU (b * c) hbc
  let W := G ⊓ L.referenceDivisorIsolatingOpen z
  have hWU : W ≤ U := inf_le_left.trans hGU
  have hW : ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W,
      y.val ∈ Z.regularAmbientOpen ∧
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b ⟨y.val, hWU y.property⟩ ≠ 0 ∧
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c ⟨y.val, hWU y.property⟩ ≠ 0 := by
    intro y
    have hgood := hG ⟨y.val, y.property.1⟩
    rw [heZ] at hgood
    refine ⟨hgood.1, ?_⟩
    have hn := hgood.2
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
  have hlocal := DivisorLocalComparison.Constructions.rationalSectionChern_eq_supportedCycle_on_neighborhood L Z
    (L.referenceDivisorSupport_complement z) z.val U hU hUi p b c hp0 v
    (L.rationalSectionOrder z.val) hm he hsm hsupp' W hWU hW
  refine ⟨W, ⟨hzG, L.referenceDivisorPoint_mem_isolatingOpen z⟩, ?_⟩
  rw [map_zsmul, map_smul] at hlocal
  rw [map_smul, L.rationalSectionDivisorThomClass_restrict_isolated z W inf_le_right]
  have href : DivisorLocalComparison.Constructions.cycleWithReferenceSupport L Z (L.referenceDivisorSupport_complement z) =
      L.referenceDivisorSupportedClass z := rfl
  rw [href] at hlocal
  refine hlocal.trans ?_
  rw [← Int.cast_smul_eq_zsmul ℚ (L.rationalSectionOrder z.val)]
  exact smul_comm _ _ _

end

/-!
# DegreeTwo: the actual first Chern class is an actual rational Thom cycle class

The actual supported Chern class and the finite divisor Thom sum agree
at every codimension-one point, including zero coefficients. Proved
codimension-two removal and supported-sheaf detection make the comparison
global. This theorem concerns the Thom cycle map; comparison with the
independently defined geometric trace cycle map remains a separate step.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem rationalSectionChern_divisorThom_comparison_neighborhood_zero
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation)
    (z : L.ReferenceDivisorPoint) (hm : L.rationalSectionOrder z.val = 0) :
    ∃ W : V.carrier.Opens, z.val ∈ W ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 L.rationalSectionChernRelativeClass =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2
        ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • L.rationalSectionDivisorThomClass) := by
  obtain ⟨U, _, hzU, hUi, hzero⟩ :=
    DivisorWinding.Constructions.DivisorEvaluation.rationalSection_local_zero_of_order_zero L z.val z.property.1 hm
      z.val (L.mem_trivializingOpen z.val)
  have hUzero := (L.rationalSectionChernRelativeClass_algebraic z.val U hUi).trans hzero
  let W := U ⊓ L.referenceDivisorIsolatingOpen z
  refine ⟨W, ⟨hzU, L.referenceDivisorPoint_mem_isolatingOpen z⟩, ?_⟩
  rw [map_smul, L.rationalSectionDivisorThomClass_restrict_isolated z W inf_le_right,
    hm, Int.cast_zero, zero_smul, smul_zero]
  have hsmall :
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 L.rationalSectionChernRelativeClass =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 0 := by
    apply RelativeLocalDetection.Constructions.relativeClass_restrict_eq_of_local_restrictions (ModuleCat.of ℚ ℚ)
      (TopCat.of V.analyticSpace) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2
    intro y hy _
    exact ⟨DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U, hy.1, hUzero.trans (map_zero _).symm⟩
  exact hsmall.trans (map_zero _)

/-- The actual global relative Chern class is the actual finite divisor
Thom sum, with the proved universal winding normalization. -/
theorem rationalSectionChernRelativeClass_eq_divisorThom
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation) :
    L.rationalSectionChernRelativeClass =
      (-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • L.rationalSectionDivisorThomClass := by
  classical
  have h (z : L.ReferenceDivisorPoint) : ∃ W : V.carrier.Opens, z.val ∈ W ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 L.rationalSectionChernRelativeClass =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2
        ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • L.rationalSectionDivisorThomClass) := by
    by_cases hm : L.rationalSectionOrder z.val = 0
    · exact rationalSectionChern_divisorThom_comparison_neighborhood_zero V L z hm
    · exact rationalSectionChern_divisorThom_comparison_neighborhood_nonzero V L z hm
  choose W hW he using h
  exact L.relativeClass_eq_of_finite_divisor_restrictions W hW _ _ he

/-- Forgetting support identifies the original rational Chern class
with the original divisor's actual Thom cycle class. -/
theorem firstChernClassQ_eq_divisorThom (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation) :
    DivisorClass.Chern.First.firstChernClassQ V.presentation L =
      (-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • V.rationalCycleClass 1 L.rationalSectionDivisorThomCycle := by
  rw [← L.rationalSectionChernRelativeClass_absolute,
    rationalSectionChernRelativeClass_eq_divisorThom V L, map_smul,
    L.rationalSectionDivisorThomClass_absolute]
  rfl

/-- Every actual algebraic line bundle has an actual rational cycle
representing its original rational Chern class under the Thom cycle map. -/
theorem firstChernClassQ_is_Thom_algebraic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1,
      V.rationalCycleClass 1 z = DivisorClass.Chern.First.firstChernClassQ V.presentation L := by
  let z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1 := L.rationalSectionDivisorThomCycle
  refine ⟨(-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • z, ?_⟩
  rw [map_smul]
  exact (firstChernClassQ_eq_divisorThom V L).symm

theorem firstChern_span_is_Thom_algebraic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.rationalCohomology 2)
    (ha : a ∈ Submodule.span ℚ (Set.range (DivisorClass.Chern.First.firstChernClassQ V.presentation))) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1, V.rationalCycleClass 1 z = a := by
  have hspan : Submodule.span ℚ (Set.range (DivisorClass.Chern.First.firstChernClassQ V.presentation)) ≤
      LinearMap.range (V.rationalCycleClass 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨L, rfl⟩
    exact firstChernClassQ_is_Thom_algebraic V L
  exact hspan ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ConcreteDivisorNeighborhood.Constructions
