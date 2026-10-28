import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Self Annihilator Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.SelfAnnihilatorType

noncomputable section

/-! A finite commutative group modulo a self-annihilating subgroup
has the same abstract group type as that subgroup. The character
equivalence is constructed from the actual nondegenerate pairing. -/

variable {G k : Type*} [CommGroup G] [Finite G] [Field k] [CharZero k] [IsAlgClosed k]

def finiteCharacterPairingEquiv (e : G →* (G →* kˣ))
    (h : ∀ x, (∀ y, e x y = 1) → x = 1) : G ≃* (G →* kˣ) := by
  have hi : Function.Injective e := by
    apply (MonoidHom.ker_eq_bot_iff e).mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 1
    apply h x
    intro y
    exact congrArg (fun f : G →* kˣ => f y) hx
  apply MulEquiv.ofBijective e
  apply (Nat.bijective_iff_injective_and_card e).mpr
  exact ⟨hi, by rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]⟩

theorem finite_self_annihilator_quotient_type
    (e : G →* (G →* kˣ)) (he : ∀ x, (∀ y, e x y = 1) → x = 1)
    (H : Subgroup G) (hH : ∀ x, (∀ y ∈ H, e x y = 1) ↔ x ∈ H) :
    Nonempty ((G ⧸ H) ≃* H) := by
  let b := finiteCharacterPairingEquiv e he
  let r : G →* (H →* kˣ) := (MonoidHom.domRestrictHom H kˣ).comp b.toMonoidHom
  have hr : Function.Surjective r :=
    (MonoidHom.domRestrict_surjective k H).comp b.surjective
  have hker : r.ker = H := by
    ext x
    constructor
    · intro hx
      apply (hH x).mp
      intro y hy
      exact congrArg (fun f : H →* kˣ => f ⟨y, hy⟩) hx
    · intro hx
      apply MonoidHom.ext
      intro y
      exact (hH x).mpr hx y y.property
  obtain ⟨hd⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity H k
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective r hr).trans hd)⟩

theorem finite_complementary_kernel_type
    {B : Type*} [CommGroup B] (q : G →* B) (v : B →* G)
    (e : G →* (G →* kˣ)) (he : ∀ x, (∀ y, e x y = 1) → x = 1)
    (hker : ∀ x, (∀ y ∈ q.ker, e x y = 1) ↔ x ∈ q.ker)
    (himage : q.range = v.ker) : Nonempty (q.ker ≃* v.ker) := by
  obtain ⟨h⟩ := finite_self_annihilator_quotient_type e he q.ker hker
  exact ⟨h.symm.trans ((QuotientGroup.quotientKerEquivRange q).trans
    (MulEquiv.subgroupCongr himage))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.SelfAnnihilatorType
