import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ReferenceSupportedComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeLocalDetection
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterComplementVanishing
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

/-! # Divisor Local Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorLocalComparison.Constructions

noncomputable section

section

/-!
# DegreeTwo: local comparison of global supported divisor classes

The normal-chart equality and the complement vanishing are expressed on
actual ambient analytic opens. These are the local comparisons needed to
glue over an algebraic neighborhood of each divisor point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum.AlgebraicLineBundle

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation)
  (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
  (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) ⊆
    (Set.range Z.analyticInclusion)ᶜ)

/-- The existing supported cycle class, enlarged to the reference support. -/
def cycleWithReferenceSupport :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of V.analyticSpace)) hO 2
    Z.rationalSupportedCycleClass

theorem cycleWithReferenceSupport_restrict_away
    (W : Opens V.analyticSpace) (hW : (W : Set V.analyticSpace) ⊆ (Set.range Z.analyticInclusion)ᶜ) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) W 2
      (cycleWithReferenceSupport L Z hO) = 0 := by
  let Q := ModuleCat.of ℚ ℚ
  let f := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (W : Set V.analyticSpace)
  have hf : Set.MapsTo f (L.analyticReferenceLocus W)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) := fun _ hx => hx
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q f (𝟙 (TopCat.of V.analyticSpace)) hf hO 2
  have hv := ConcreteCategory.congr_hom hc Z.rationalSupportedCycleClass
  have hz := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset Q f (L.analyticReferenceLocus W)
    (Set.range Z.analyticInclusion)ᶜ (fun _ hx => hO (hf hx)) (fun y => hW y.property) 2
  exact hv.trans (by change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q f _ 2 _ = 0; rw [hz]; rfl)

variable (i : V.carrier) (U : V.carrier.Opens) [Nonempty U] (hi : U ≤ L.trivializingOpen i)
  (p : Γ(V.carrier, U)) (hp : p ≠ 0) (v : Γ(V.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
  (he : (L.rationalSectionCoordinate i : V.carrier.functionField) =
    V.carrier.germToFunctionField U v * (V.carrier.germToFunctionField U p) ^ m)

include hi hp hm he

/-- Both actual global classes agree on an ambient neighborhood of each
point where the local parameter and the support are absent. -/
theorem exists_local_divisor_comparison_off_support
    (y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) (hyp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p y ≠ 0)
    (hyZ : y.val ∉ Set.range Z.analyticInclusion) :
    ∃ W : Opens V.analyticSpace, y.val ∈ W ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) W 2
        L.rationalSectionChernRelativeClass =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) W 2
        (m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • cycleWithReferenceSupport L Z hO)) := by
  let N : Opens V.analyticSpace :=
    ⟨Subtype.val '' {w : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U | DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p w ≠ 0},
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U).isOpenEmbedding'.isOpenMap _
        (isOpen_ne.preimage (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p).continuous)⟩
  let D : Opens V.analyticSpace :=
    ⟨(Set.range Z.analyticInclusion)ᶜ, Z.isClosedEmbedding_analyticInclusion.isClosed_range.isOpen_compl⟩
  let W := N ⊓ D
  have hWU : W ≤ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U := by
    rintro w ⟨⟨t, _, rfl⟩, _⟩
    exact t.property
  have hWp : ∀ w : W, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p ⟨w.val, hWU w.property⟩ ≠ 0 := by
    intro w
    obtain ⟨t, ht, htw⟩ := w.property.1
    have ht' : t = ⟨w.val, hWU w.property⟩ := Subtype.ext htw
    exact ht' ▸ ht
  refine ⟨W, ⟨⟨y, hyp, rfl⟩, hyZ⟩, ?_⟩
  rw [ParameterComplementVanishing.Constructions.rationalSectionChern_restrict_zero_of_parameter_nonzero L i U hi p hp v m hm he W hWU hWp,
    map_zsmul, map_smul, cycleWithReferenceSupport_restrict_away L Z hO W
      (fun _ hw => hw.2), smul_zero, smul_zero]

end

section

/-!
# DegreeTwo: the regular-divisor comparison on actual ambient opens

The genuine native normal pair is an open embedding into the original
scheme point space. Its relative-class equality therefore holds on an
actual ambient neighborhood, with both sides still global restrictions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum.AlgebraicLineBundle

theorem exists_local_divisor_comparison_on_regular_support
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
    (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) ⊆
      (Set.range Z.analyticInclusion)ᶜ)
    (i : V.carrier) (U : V.carrier.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (hi : U ≤ L.trivializingOpen i) (p b c : Γ(V.carrier, U)) (hp : p ≠ 0)
    (v : Γ(V.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : V.carrier.functionField) =
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
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) W 2
        L.rationalSectionChernRelativeClass =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) W 2
        (m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • cycleWithReferenceSupport L Z hO)) := by
  obtain ⟨P, hPU, hmd, hcoord, _⟩ :=
    RegularSectionFixedPair.Constructions.exists_regular_section_fixedNormalPair V Z U hU p b c hp hsm hsupp x hxU hxb hxc
  let g := SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P
  have hg : Topology.IsOpenEmbedding g :=
    Z.regularAmbientOpen.isOpenEmbedding'.comp P.openNeighborhood.isOpenEmbedding'
  let O : Set V.analyticSpace := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen
  have hclass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g
      (A := g ⁻¹' O) (fun _ hy => hy) 2 L.rationalSectionChernRelativeClass =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g
        (A := g ⁻¹' O) (fun _ hy => hy) 2
        (m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • cycleWithReferenceSupport L Z hO)) := by
    rw [map_zsmul, map_smul]
    exact ReferenceSupportedComparison.Constructions.rationalSectionChern_eq_supportedCycle_on_normalPair L Z U x P hPU hO
      i hi p hp v m hm he hmd hcoord
  obtain ⟨W, hW, hcompare⟩ := RelativeLocalDetection.Constructions.relativeClass_eq_on_openEmbedding_range
    (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) O 2 g hg
    L.rationalSectionChernRelativeClass
    (m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • cycleWithReferenceSupport L Z hO)) hclass
  refine ⟨W, ?_, hcompare⟩
  rw [← SetLike.mem_coe, hW]
  exact ⟨⟨Z.regularComplementInclusion x, P.point_mem_neighborhood⟩, rfl⟩

end

/-!
# DegreeTwo: compare the actual supported classes on an algebraic neighborhood

At support points the native normal-coordinate theorem gives the local
comparison; off the support both actual classes vanish. The proved
supported-sheaf detection then glues those equalities on the whole open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum.AlgebraicLineBundle

theorem rationalSectionChern_eq_supportedCycle_on_neighborhood
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
    (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) ⊆
      (Set.range Z.analyticInclusion)ᶜ)
    (i : V.carrier) (U : V.carrier.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (hi : U ≤ L.trivializingOpen i) (p b c : Γ(V.carrier, U)) (hp : p ≠ 0)
    (v : Γ(V.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : V.carrier.functionField) =
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
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2 L.rationalSectionChernRelativeClass =
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W) 2
      (m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • cycleWithReferenceSupport L Z hO)) := by
  apply RelativeLocalDetection.Constructions.relativeClass_restrict_eq_of_local_restrictions (ModuleCat.of ℚ ℚ)
    (TopCat.of V.analyticSpace) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen)
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
    exact exists_local_divisor_comparison_on_regular_support L Z hO i U hU hi p b c hp
      v m hm he hsm hsupp x (hWU hy) hgood.2.1 hgood.2.2
  · let yU : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U := ⟨y, hWU hy⟩
    have hyp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p yU ≠ 0 :=
      fun h => hyZ ((hsupp yU hgood.2.2).mp h)
    exact exists_local_divisor_comparison_off_support L Z hO i U hi p hp v m hm he yU hyp hyZ

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorLocalComparison.Constructions
