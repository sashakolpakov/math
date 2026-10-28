import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeSectionPair
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalComplementVanishing
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenComplementPurity
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeLocalDetection

/-! # Rational Divisor Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalDivisorNeighborhood

noncomputable section

/-! Compare the actual rational-function boundary with the existing divisor
cycle class on algebraic neighborhoods, using native complex normal charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions
  SupportedNormalRestriction.Constructions PrimeSectionPair.Constructions RationalRegularNormal.Constructions RationalComplementVanishing.Constructions
  RationalBoundary.Constructions.Restriction OpenComplementPurity.Constructions HodgeConjecture.DegreeTwo.RelativeLocalDetection.Constructions

theorem exists_rational_comparison_on_regular_support
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)
    (z : {x : X.left // Order.coheight x = 1})
    (hO : (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆
      (Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ)
    (U : X.left.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (p b c : Γ(X.left, U)) (hp : p ≠ 0)
    (v : Γ(X.left, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : g =
      X.left.germToFunctionField U v * (X.left.germToFunctionField U p) ^ m)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (hsupp : ∀ y : SectionEvaluation.Constructions.analyticOpen X U,
      SectionEvaluation.Constructions.sectionEvaluationOn X U c y ≠ 0 →
        (SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0 ↔ y.val ∈ Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z))))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
    (hxU : (RegularSupport.Constructions.regularInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x ∈ SectionEvaluation.Constructions.analyticOpen X U)
    (hxb : SectionEvaluation.Constructions.sectionEvaluationOn X U b ⟨(RegularSupport.Constructions.regularInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x, hxU⟩ ≠ 0)
    (hxc : SectionEvaluation.Constructions.sectionEvaluationOn X U c ⟨(RegularSupport.Constructions.regularInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x, hxU⟩ ≠ 0) :
    ∃ W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X), (RegularSupport.Constructions.regularInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) W 2
        (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) W 2
        (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement X z D hO)) := by
  obtain ⟨P, hPU, hmd, _, _, hcoord, _⟩ :=
    PrimeSectionPair.Constructions.exists_prime_section_fixedNormalPair X z U hU p b c hp hsm hsupp x hxU hxb hxc
  let k := SupportedNormalRestriction.Constructions.regularPairAmbientMap X z x P
  have hg : Topology.IsOpenEmbedding k :=
    (RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z)).isOpenEmbedding'.comp P.openNeighborhood.isOpenEmbedding'
  let O : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := SectionEvaluation.Constructions.analyticOpen X D.domain
  have hclass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k
      (A := k ⁻¹' O) (fun _ hy => hy) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k
        (A := k ⁻¹' O) (fun _ hy => hy) 2
        (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement X z D hO)) := by
    rw [map_zsmul]
    exact RationalRegularNormal.Constructions.rationalGlobalBoundary_regularNormal X z D U x P hPU hO p hp v m hm he hmd hcoord
  obtain ⟨W, hW, hcompare⟩ := HodgeConjecture.DegreeTwo.RelativeLocalDetection.Constructions.relativeClass_eq_on_openEmbedding_range
    (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) O 2 k hg
    (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D)
    (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement X z D hO)) hclass
  refine ⟨W, ?_, hcompare⟩
  rw [← SetLike.mem_coe, hW]
  exact ⟨⟨(RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x, P.point_mem_neighborhood⟩, rfl⟩

section OffSupport
variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    {g : X.left.functionField}
  (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g) (z : {x : X.left // Order.coheight x = 1})
  (hO : (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆
    (Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ)
  (U : X.left.Opens) [Nonempty U]
  (p : Γ(X.left, U)) (hp : p ≠ 0) (v : Γ(X.left, U)ˣ) (m : ℤ) (hm : m ≠ 0)
  (he : g = X.left.germToFunctionField U v * (X.left.germToFunctionField U p) ^ m)
include hp hm he
/-- Both actual global classes agree on an ambient neighborhood of each
point where the local parameter and the support are absent. -/
theorem exists_rational_comparison_off_support
    (y : SectionEvaluation.Constructions.analyticOpen X U) (hyp : SectionEvaluation.Constructions.sectionEvaluationOn X U p y ≠ 0)
    (hyZ : y.val ∉ Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z))) :
    ∃ W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X), y.val ∈ W ∧
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) W 2
        (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) W 2
        (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement X z D hO)) := by
  let N : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
    ⟨Subtype.val '' {w : SectionEvaluation.Constructions.analyticOpen X U | SectionEvaluation.Constructions.sectionEvaluationOn X U p w ≠ 0},
      (SectionEvaluation.Constructions.analyticOpen X U).isOpenEmbedding'.isOpenMap _
        (isOpen_ne.preimage (SectionEvaluation.Constructions.sectionEvaluationOn X U p).continuous)⟩
  let K : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
    ⟨(Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ, (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (RegularSupport.Constructions.supportToAmbient X (SchemeDivisor.Purity.Constructions.primeSupport X z))).isClosed_range.isOpen_compl⟩
  let W := N ⊓ K
  have hWU : W ≤ SectionEvaluation.Constructions.analyticOpen X U := by
    rintro w ⟨⟨t, _, rfl⟩, _⟩
    exact t.property
  have hWp : ∀ w : W, SectionEvaluation.Constructions.sectionEvaluationOn X U p ⟨w.val, hWU w.property⟩ ≠ 0 := by
    intro w
    obtain ⟨t, ht, htw⟩ := w.property.1
    have ht' : t = ⟨w.val, hWU w.property⟩ := Subtype.ext htw
    exact ht' ▸ ht
  refine ⟨W, ⟨⟨y, hyp, rfl⟩, hyZ⟩, ?_⟩
  rw [RationalComplementVanishing.Constructions.rationalGlobalBoundary_restrict_zero_of_parameter_nonzero X D U p hp v m hm he W hWU hWp,
    map_zsmul, RationalComplementVanishing.Constructions.cycleWithUnitComplement_restrict_away X z D hO W
      (fun _ hw => hw.2), smul_zero]

end OffSupport

theorem rationalGlobalBoundary_eq_supportedCycle_on_neighborhood
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)
    (z : {x : X.left // Order.coheight x = 1})
    (hO : (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆
      (Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ)
    (U : X.left.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (p b c : Γ(X.left, U)) (hp : p ≠ 0)
    (v : Γ(X.left, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : g =
      X.left.germToFunctionField U v * (X.left.germToFunctionField U p) ^ m)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (hsupp : ∀ y : SectionEvaluation.Constructions.analyticOpen X U,
      SectionEvaluation.Constructions.sectionEvaluationOn X U c y ≠ 0 →
        (SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0 ↔ y.val ∈ Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z))))
    (W : X.left.Opens) (hWU : W ≤ U)
    (hW : ∀ y : SectionEvaluation.Constructions.analyticOpen X W,
      y.val ∈ (RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z)) ∧
      SectionEvaluation.Constructions.sectionEvaluationOn X U b ⟨y.val, hWU y.property⟩ ≠ 0 ∧
      SectionEvaluation.Constructions.sectionEvaluationOn X U c ⟨y.val, hWU y.property⟩ ≠ 0) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (SectionEvaluation.Constructions.analyticOpen X W) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (SectionEvaluation.Constructions.analyticOpen X W) 2
      (m • (RationalRegularNormal.Constructions.cycleWithUnitComplement X z D hO)) := by
  apply HodgeConjecture.DegreeTwo.RelativeLocalDetection.Constructions.relativeClass_restrict_eq_of_local_restrictions (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (SectionEvaluation.Constructions.analyticOpen X D.domain)
    (SectionEvaluation.Constructions.analyticOpen X W) 2
  intro y hy _
  have hgood := hW ⟨y, hy⟩
  by_cases hyZ : y ∈ Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z))
  · have hyr : (⟨y, hgood.1⟩ : (RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z))) ∈ Set.range (RegularSupport.Constructions.regularComplementInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) := by
      rw [RegularSupport.Constructions.regularComplementInclusion_range X (SchemeDivisor.Purity.Constructions.primeSupport X z)]
      exact hyZ
    obtain ⟨x, hx⟩ := hyr
    have hxy : (RegularSupport.Constructions.regularInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) x = y := congrArg Subtype.val hx
    subst y
    exact exists_rational_comparison_on_regular_support D z hO U hU p b c hp
      v m hm he hsm hsupp x (hWU hy) hgood.2.1 hgood.2.2
  · let yU : SectionEvaluation.Constructions.analyticOpen X U := ⟨y, hWU hy⟩
    have hyp : SectionEvaluation.Constructions.sectionEvaluationOn X U p yU ≠ 0 :=
      fun h => hyZ ((hsupp yU hgood.2.2).mp h)
    exact exists_rational_comparison_off_support D z hO U p hp v m hm he yU hyp hyZ

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalDivisorNeighborhood
