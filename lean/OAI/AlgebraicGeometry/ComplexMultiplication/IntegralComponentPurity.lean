import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Integral Component Purity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntegralComponentPurity

noncomputable section

/-! # Componentwise Hodge purity on an integral variety -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

/-- The genuine component inclusion of an integral variety is an isomorphism. -/
theorem integral_componentInclusion_isIso
    (C : irreducibleComponents V.presentation.carrier) :
    IsIso (V.presentation.componentInclusionOver C) := by
  have hC : C.val = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.property
  let : Surjective (V.presentation.componentInclusion C) := ⟨by
    rw [← Set.range_eq_univ, V.presentation.componentInclusion_range, hC]⟩
  let : IsIso (V.presentation.componentInclusion C) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  let : IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map (V.presentation.componentInclusionOver C)) := by
    change IsIso (V.presentation.componentInclusion C)
    infer_instance
  exact isIso_of_reflects_iso (V.presentation.componentInclusionOver C)
    (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase)

/-- Componentwise genuine Hodge type reflects the whole-variety genuine Hodge type. -/
theorem integral_presentationPure_implies_pure (p q : ℕ)
    (a : V.complexCohomology (p + q))
    (ha : a ∈ V.presentation.pureBettiSubspace p q) :
    a ∈ V.pureBettiSubspace p q := by
  let x : V.carrier := Classical.arbitrary V.carrier
  let C : irreducibleComponents V.presentation.carrier :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let := integral_componentInclusion_isIso V C
  have hc := (V.presentation.mem_pureBettiSubspace_iff p q a).mp ha C
  rw [V.presentation.componentBettiEquiv_apply] at hc
  exact (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace_iff
    (asIso (V.presentation.componentInclusionOver C)) p q a).mp hc

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntegralComponentPurity
