import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass

/-! # Section Step Coefficients -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepCoefficients.Constructions

noncomputable section

/-! Exact coefficients of the finite section step, summed over the
original finite cycle support with the original principal-divisor orders. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped BigOperators

open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem linearCombination_nonzeroSubtype_eq_sum {ι M : Type} [AddCommGroup M] [Module ℚ M]
    (c : ι →₀ ℚ) (f : {i : ι // c i ≠ 0} → M) :
    Finsupp.linearCombination ℚ f (c.subtypeDomain (fun i => c i ≠ 0)) =
      ∑ i : c.support, c i.val • f ⟨i.val, Finsupp.mem_support_iff.mp i.property⟩ := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_bij (fun a _ => (⟨a.val, Finsupp.mem_support_iff.mpr a.property⟩ : c.support))
  · intro a _
    exact Finset.mem_univ _
  · intro a _ b _ h
    exact Subtype.ext (congrArg (fun z : c.support => z.val) h)
  · intro b _
    refine ⟨⟨b.val, Finsupp.mem_support_iff.mp b.property⟩, ?_, rfl⟩
    apply Finsupp.mem_support_iff.mpr
    change c b.val ≠ 0
    exact Finsupp.mem_support_iff.mp b.property
  · intro a _
    rfl

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens)
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (U : Opens V.analyticSpace)
  {L : Type} (u : L → U) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hs : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

theorem cycleSectionStep_coefficient (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) :
    CycleSectionClass.Constructions.cycleSectionStep V p B s U u c hc hne hs C =
      ∑ D : c.support, letI := hne D.val (Finsupp.mem_support_iff.mp D.property)
        c D.val * IntersectionGeometry.principalDivisorCoefficient V.presentation D.val.val (Affine.SectionFunction.Constructions.parentSectionFunction D.val B s) C.val := by
  classical
  rw [CycleSectionClass.Constructions.cycleSectionStep, Section.Step.Constructions.stepCycleMap, Section.AdmissibleLift.Constructions.admissibleCycle, Finsupp.linearCombination_mapDomain,
    linearCombination_nonzeroSubtype_eq_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro D _
  let := hne D.val (Finsupp.mem_support_iff.mp D.property)
  change c D.val * Section.CupPrincipalGeneral.Constructions.Step.principalStep D.val B s (hs D.val (Finsupp.mem_support_iff.mp D.property)) C = _
  rw [Section.CupPrincipalGeneral.Constructions.Step.principalStep_coefficient]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepCoefficients.Constructions
