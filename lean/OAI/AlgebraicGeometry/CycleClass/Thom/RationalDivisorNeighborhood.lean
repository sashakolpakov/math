import OAI.AlgebraicGeometry.CycleClass.Thom.RationalComplementVanishing
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ComplementPurity
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeLocalDetection

/-! # Rational Divisor Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RationalDivisorNeighborhood

noncomputable section

/-! Compare the actual rational-function boundary with the existing divisor
cycle class on algebraic neighborhoods, using native complex normal charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.RationalRegularNormal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalComplementVanishing.Constructions
  RationalBoundary.Constructions.Restriction Open.ComplementPurity.Constructions HodgeConjecture.DegreeTwo.RelativeLocalDetection.Constructions

theorem exists_rational_comparison_on_regular_support
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {g : V.carrier.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative V.carrier g)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V 1)
    (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) ⊆
      (Set.range Z.analyticInclusion)ᶜ)
    (U : V.carrier.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (p b c : Γ(V.carrier, U)) (hp : p ≠ 0)
    (v : Γ(V.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : g =
      V.carrier.germToFunctionField U v * (V.carrier.germToFunctionField U p) ^ m)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra V.structureMap U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (hsupp : ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U,
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c y ≠ 0 →
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y = 0 ↔ y.val ∈ Set.range Z.analyticInclusion))
    (x : Z.regularAnalyticSpace)
    (hxU : Z.regularAnalyticToAmbient x ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U)
    (hxb : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b ⟨Z.regularAnalyticToAmbient x, hxU⟩ ≠ 0)
    (hxc : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c ⟨Z.regularAnalyticToAmbient x, hxU⟩ ≠ 0) :
    ∃ W : Opens V.analyticSpace, Z.regularAnalyticToAmbient x ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) W 2
        (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) W 2
        (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement D Z hO)) := by
  obtain ⟨P, hPU, hmd, hcoord, _⟩ :=
    HodgeConjecture.DegreeTwo.RegularSectionFixedPair.Constructions.exists_regular_section_fixedNormalPair V Z U hU p b c hp hsm hsupp x hxU hxb hxc
  let k := HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P
  have hg : Topology.IsOpenEmbedding k :=
    Z.regularAmbientOpen.isOpenEmbedding'.comp P.openNeighborhood.isOpenEmbedding'
  let O : Set V.analyticSpace := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain
  have hclass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k
      (A := k ⁻¹' O) (fun _ hy => hy) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k
        (A := k ⁻¹' O) (fun _ hy => hy) 2
        (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement D Z hO)) := by
    rw [map_zsmul]
    exact RationalRegularNormal.Constructions.rationalGlobalBoundary_regularNormal D Z U x P hPU hO p hp v m hm he hmd hcoord
  obtain ⟨W, hW, hcompare⟩ := HodgeConjecture.DegreeTwo.RelativeLocalDetection.Constructions.relativeClass_eq_on_openEmbedding_range
    (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) O 2 k hg
    (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D)
    (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement D Z hO)) hclass
  refine ⟨W, ?_, hcompare⟩
  rw [← SetLike.mem_coe, hW]
  exact ⟨⟨Z.regularComplementInclusion x, P.point_mem_neighborhood⟩, rfl⟩

section OffSupport
variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {g : V.carrier.functionField}
  (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative V.carrier g) (Z : Geometric.DimensionCycles.DimensionCycleSupport V 1)
  (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) ⊆
    (Set.range Z.analyticInclusion)ᶜ)
  (U : V.carrier.Opens) [Nonempty U]
  (p : Γ(V.carrier, U)) (hp : p ≠ 0) (v : Γ(V.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
  (he : g = V.carrier.germToFunctionField U v * (V.carrier.germToFunctionField U p) ^ m)
include hp hm he
/-- Both actual global classes agree on an ambient neighborhood of each
point where the local parameter and the support are absent. -/
theorem exists_rational_comparison_off_support
    (y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) (hyp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y ≠ 0)
    (hyZ : y.val ∉ Set.range Z.analyticInclusion) :
    ∃ W : Opens V.analyticSpace, y.val ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) W 2
        (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) W 2
        (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement D Z hO)) := by
  let N : Opens V.analyticSpace :=
    ⟨Subtype.val '' {w : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U | DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p w ≠ 0},
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U).isOpenEmbedding'.isOpenMap _
        (isOpen_ne.preimage (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p).continuous)⟩
  let K : Opens V.analyticSpace :=
    ⟨(Set.range Z.analyticInclusion)ᶜ, Z.isClosedEmbedding_analyticInclusion.isClosed_range.isOpen_compl⟩
  let W := N ⊓ K
  have hWU : W ≤ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U := by
    rintro w ⟨⟨t, _, rfl⟩, _⟩
    exact t.property
  have hWp : ∀ w : W, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p ⟨w.val, hWU w.property⟩ ≠ 0 := by
    intro w
    obtain ⟨t, ht, htw⟩ := w.property.1
    have ht' : t = ⟨w.val, hWU w.property⟩ := Subtype.ext htw
    exact ht' ▸ ht
  refine ⟨W, ⟨⟨y, hyp, rfl⟩, hyZ⟩, ?_⟩
  rw [RationalComplementVanishing.Constructions.rationalGlobalBoundary_restrict_zero_of_parameter_nonzero V.presentation D U p hp v m hm he W hWU hWp,
    map_zsmul, RationalComplementVanishing.Constructions.cycleWithUnitComplement_restrict_away D Z hO W
      (fun _ hw => hw.2), smul_zero]

end OffSupport

theorem rationalGlobalBoundary_eq_supportedCycle_on_neighborhood
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {g : V.carrier.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative V.carrier g)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V 1)
    (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) ⊆
      (Set.range Z.analyticInclusion)ᶜ)
    (U : V.carrier.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (p b c : Γ(V.carrier, U)) (hp : p ≠ 0)
    (v : Γ(V.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : g =
      V.carrier.germToFunctionField U v * (V.carrier.germToFunctionField U p) ^ m)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra V.structureMap U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (hsupp : ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U,
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c y ≠ 0 →
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y = 0 ↔ y.val ∈ Set.range Z.analyticInclusion))
    (W : V.carrier.Opens) (hWU : W ≤ U)
    (hW : ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W,
      y.val ∈ Z.regularAmbientOpen ∧
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U b ⟨y.val, hWU y.property⟩ ≠ 0 ∧
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U c ⟨y.val, hWU y.property⟩ ≠ 0) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2
      (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement D Z hO)) := by
  apply HodgeConjecture.DegreeTwo.RelativeLocalDetection.Constructions.relativeClass_restrict_eq_of_local_restrictions (ModuleCat.of ℚ ℚ)
    (TopCat.of V.analyticSpace) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain)
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2
  intro y hy _
  have hgood := hW ⟨y, hy⟩
  by_cases hyZ : y ∈ Set.range Z.analyticInclusion
  · have hyr : (⟨y, hgood.1⟩ : Z.regularAmbientSpace) ∈ Set.range Z.regularComplementInclusion := by
      rw [Z.range_regularComplementInclusion]
      exact hyZ
    obtain ⟨x, hx⟩ := hyr
    have hxy : Z.regularAnalyticToAmbient x = y := congrArg Subtype.val hx
    subst y
    exact exists_rational_comparison_on_regular_support D Z hO U hU p b c hp
      v m hm he hsm hsupp x (hWU hy) hgood.2.1 hgood.2.2
  · let yU : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U := ⟨y, hWU hy⟩
    have hyp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p yU ≠ 0 :=
      fun h => hyZ ((hsupp yU hgood.2.2).mp h)
    exact exists_rational_comparison_off_support D Z hO U p hp v m hm he yU hyp hyZ

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RationalDivisorNeighborhood
