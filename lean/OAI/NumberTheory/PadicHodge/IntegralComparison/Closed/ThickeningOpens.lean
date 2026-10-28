import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentOpenRestriction

/-! # Thickening Opens -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ThickeningOpens

noncomputable section

/-! Open subsets and actual restricted reductions along a surjective
closed immersion. This supplies the literal overlap schemes for
nilpotent etale gluing. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i]

def homeomorph : X₀ ≃ₜ X :=
  (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩).homeomorph

@[simp] theorem homeomorph_apply (x : X₀) : ThickeningOpens.homeomorph i x = i x := rfl

def liftOpen (U : X₀.Opens) : X.Opens :=
  ⟨(ThickeningOpens.homeomorph i).symm ⁻¹' U, U.isOpen.preimage (ThickeningOpens.homeomorph i).symm.continuous⟩

@[simp] theorem mem_liftOpen (U : X₀.Opens) (x : X) :
    x ∈ liftOpen i U ↔ (ThickeningOpens.homeomorph i).symm x ∈ U := Iff.rfl

@[simp] theorem preimage_liftOpen (U : X₀.Opens) : i ⁻¹ᵁ liftOpen i U = U := by
  ext x
  change (ThickeningOpens.homeomorph i).symm (ThickeningOpens.homeomorph i x) ∈ U ↔ x ∈ U
  rw [(ThickeningOpens.homeomorph i).symm_apply_apply]

@[simp] theorem liftOpen_preimage (U : X.Opens) : liftOpen i (i ⁻¹ᵁ U) = U := by
  ext x
  change ThickeningOpens.homeomorph i ((ThickeningOpens.homeomorph i).symm x) ∈ U ↔ x ∈ U
  rw [(ThickeningOpens.homeomorph i).apply_symm_apply]

theorem liftOpen_mono {U V : X₀.Opens} (h : U ≤ V) : liftOpen i U ≤ liftOpen i V :=
  fun _ hx => h hx

theorem liftOpen_top : liftOpen i ⊤ = ⊤ := by ext; rfl

theorem liftOpen_inf (U V : X₀.Opens) : liftOpen i (U ⊓ V) = liftOpen i U ⊓ liftOpen i V := by
  ext; rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ThickeningOpens
