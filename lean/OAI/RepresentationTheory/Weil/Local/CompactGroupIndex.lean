import Mathlib.GroupTheory.Index

/-! # Compact Group Index -/

namespace OAI.RepresentationTheory.Weil.Local.CompactGroupIndex.Construction

noncomputable section

/-! Index bookkeeping for a compact group's power map after choosing a small torsion-free subgroup. -/

theorem endomorphism_index_of_finite_index_subgroup
    {G : Type*} [CommGroup G] (f : G →* G) (H : Subgroup G)
    (hH : H.index ≠ 0) (hfH : H.map f ≤ H) (hker : H ⊓ f.ker = ⊥) :
    f.range.index = Nat.card f.ker * (H.map f).relIndex H := by
  have hrel : H.relIndex (H ⊔ f.ker) = Nat.card f.ker := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right H f.ker, hker,
      Subgroup.relIndex_bot_left]
  have hprod := Subgroup.relIndex_mul_index (H := H) (K := H ⊔ f.ker) le_sup_left
  rw [hrel] at hprod
  have hK : (H ⊔ f.ker).index ≠ 0 := by
    intro he
    rw [he, mul_zero] at hprod
    exact hH hprod.symm
  have hmap := Subgroup.relIndex_mul_index hfH
  rw [H.index_map f, ← hprod] at hmap
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hK)
  calc
    (H ⊔ f.ker).index * f.range.index =
        (H.map f).relIndex H * (Nat.card f.ker * (H ⊔ f.ker).index) := hmap.symm
    _ = (H ⊔ f.ker).index * (Nat.card f.ker * (H.map f).relIndex H) := by ac_rfl

theorem square_index_of_finite_index_subgroup
    {G : Type*} [CommGroup G] (H : Subgroup G) (hH : H.index ≠ 0)
    (hker : ∀ x : G, x ∈ H → x ^ 2 = 1 → x = 1) :
    (powMonoidHom 2 : G →* G).range.index =
      Nat.card (powMonoidHom 2 : G →* G).ker *
        (H.map (powMonoidHom 2 : G →* G)).relIndex H := by
  apply endomorphism_index_of_finite_index_subgroup _ H hH
  · rintro x ⟨y, hy, rfl⟩
    exact H.pow_mem hy 2
  · apply le_antisymm _ bot_le
    intro x hx
    exact (Subgroup.mem_bot).mpr (hker x hx.1 hx.2)

end

end OAI.RepresentationTheory.Weil.Local.CompactGroupIndex.Construction
