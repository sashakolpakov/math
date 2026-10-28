import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.MultisetEnumeration

/-! # Three Parameter Counts -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ThreeParameterCounts

noncomputable section

/-! Count exactly three original finite parameter sets using their
proved subspace bijections. Repeated target values retain multiplicity. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.MultisetEnumeration

variable {F V X : Type} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Fintype V]
  (A : Fin 3 → Type) [∀ i, Fintype (A i)]
  (e : ∀ i : Fin 3, A i ≃ {J : Submodule F (V × F) // Module.finrank F J = i.val + 1})
  (target : Fin 3 → Submodule F V → Bool → X)

local instance : Fintype (Submodule F V) := Fintype.ofFinite _
local instance : Fintype (Submodule F (V × F)) := Fintype.ofFinite _

open Classical in
def originalLabeledParameters (i : Fin 3) : Multiset X :=
  Finset.univ.val.map (fun a : A i => target i ((e i a).val.map (LinearMap.fst F V F))
    (decide (SubspaceCounts.Construction.identityLine ≤ (e i a).val)))

theorem originalLabeledParameters_eq (i : Fin 3) :
    originalLabeledParameters A e target i =
      SubspaceCounts.Construction.labeledReduction (i.val + 1) (fun U flag => ({target i U flag} : Multiset X)) := by
  classical
  rw [originalLabeledParameters, Parameter.MultisetEnumeration.parameter_multiset_subtype _ (e i)]
  unfold SubspaceCounts.Construction.labeledReduction
  apply Finset.sum_congr rfl
  intro J _
  by_cases h : Module.finrank F J = i.val + 1
  · rw [dite_eq_left h, ite_eq_left h, (e i).apply_symm_apply]
  · rw [dite_eq_right h, ite_eq_right h]

theorem original_three_parameter_counts (hV : Module.finrank F V = 2) :
    originalLabeledParameters A e target 0 = {target 0 ⊥ true} +
      Nat.card F • (∑ U : Submodule F V, if Module.finrank F U = 1 then {target 0 U false} else 0) ∧
    originalLabeledParameters A e target 1 =
      (∑ U : Submodule F V, if Module.finrank F U = 1 then {target 1 U true} else 0) +
        Nat.card F ^ 2 • {target 1 ⊤ false} ∧
    originalLabeledParameters A e target 2 = {target 2 ⊤ true} := by
  classical
  rw [originalLabeledParameters_eq, originalLabeledParameters_eq, originalLabeledParameters_eq]
  exact ⟨SubspaceCounts.Construction.labeledReduction_one _, SubspaceCounts.Construction.labeledReduction_two hV _, SubspaceCounts.Construction.labeledReduction_three hV _⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ThreeParameterCounts
