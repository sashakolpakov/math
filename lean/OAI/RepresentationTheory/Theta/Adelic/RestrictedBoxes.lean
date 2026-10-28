import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-! # Restricted Boxes -/

namespace OAI.RepresentationTheory.Theta.Adelic.RestrictedBoxes

noncomputable section

/-! Compact boxes in the actual restricted-product topology. -/

open Filter Set
open scoped RestrictedProduct _root_.Topology

variable {I : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)]
    (A B : ∀ i, Set (X i))

theorem isCompact_box (hB : ∀ i, IsCompact (B i))
    (hBA : ∀ᶠ i in cofinite, B i ⊆ A i) :
    IsCompact {x : Πʳ i, [X i, A i] | ∀ i, x i ∈ B i} := by
  let S : Set I := {i | B i ⊆ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hBA
  let lift : (∀ i, B i) → Πʳ i, [X i, A i]_[𝓟 S] := fun x =>
    ⟨fun i => (x i).val, eventually_principal.mpr fun i hi => hi (x i).property⟩
  have hc : Continuous lift := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    exact continuous_pi fun i => (continuous_apply i).subtype_val
  let toRestricted := RestrictedProduct.inclusion X A hS ∘ lift
  have ht : Continuous toRestricted := (RestrictedProduct.continuous_inclusion hS).comp hc
  let : ∀ i, CompactSpace (B i) := fun i => isCompact_iff_compactSpace.mp (hB i)
  have he : toRestricted '' Set.univ = {x : Πʳ i, [X i, A i] | ∀ i, x i ∈ B i} := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩ i
      exact (y i).property
    · intro hx
      refine ⟨fun i => ⟨x i, hx i⟩, Set.mem_univ _, ?_⟩
      apply RestrictedProduct.ext
      intro i
      rfl
  rw [← he]
  exact isCompact_univ.image ht

end

end OAI.RepresentationTheory.Theta.Adelic.RestrictedBoxes
