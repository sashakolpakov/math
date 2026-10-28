import OAI.NumberTheory.Quaternion.Arithmetic.FiniteSpecialLinearCorrection

/-! # Compact Restricted Boxes -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CompactRestrictedBoxes

noncomputable section

/-! Compact coordinate boxes in a restricted product. The coordinate
boxes lie in the distinguished subsets outside a finite set. -/

open scoped Classical RestrictedProduct
open Set Filter _root_.Topology

theorem isCompact_restricted_product_box {ι : Type*} (R : ι → Type*)
    [∀ i, TopologicalSpace (R i)] (A K : (i : ι) → Set (R i))
    (hK : ∀ i, IsCompact (K i)) (hKA : ∀ᶠ i in cofinite, K i ⊆ A i) :
    IsCompact {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ K i} := by
  let S : Set ι := {i | K i ⊆ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hKA
  let f : ((i : ι) → K i) → Πʳ i, [R i, A i]_[𝓟 S] :=
    fun x => ⟨fun i => (x i).val, fun i hi => hi (x i).property⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i)))
  let j := RestrictedProduct.inclusion R A hS
  have hj : Continuous j := RestrictedProduct.continuous_inclusion hS
  let : ∀ i, CompactSpace (K i) := fun i => isCompact_iff_compactSpace.mp (hK i)
  have hc := isCompact_univ.image (hj.comp hf)
  have he : (j ∘ f) '' Set.univ = {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ K i} := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩ i
      exact (y i).property
    · intro hx
      exact ⟨fun i => ⟨x i, hx i⟩, trivial, rfl⟩
  rw [he] at hc
  exact hc

end

end OAI.NumberTheory.Quaternion.Arithmetic.CompactRestrictedBoxes
