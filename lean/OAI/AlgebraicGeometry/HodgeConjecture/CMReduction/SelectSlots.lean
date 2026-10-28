import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EvenAppend
import Mathlib.GroupTheory.Perm.Basic

/-! # Select Slots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.SelectSlots.CM.Construction

noncomputable section

/-! Move two selected endpoint slots to the last two positions. The same
permutation leaves an identical residual tuple whenever only those two
slots changed. -/

theorem exists_perm_pair {α : Type*} [DecidableEq α]
    (i j a b : α) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm α, σ i = a ∧ σ j = b := by
  let τ := Equiv.swap j b
  have haj : τ a ≠ j := by
    intro h
    have he := congrArg τ h
    have hae : a = b := by simpa [τ] using he
    exact hab hae
  refine ⟨(Equiv.swap i (τ a)).trans τ, ?_, ?_⟩
  · simp [τ]
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hij.symm haj.symm]
    exact Equiv.swap_apply_left j b

def tailSlot (r : ℕ) (j : Fin 2) : Fin ((r + 1) + (r + 1)) :=
  Fin.cast (add_add_add_comm r r 1 1) (Fin.natAdd (r + r) j)

def prefixSlot (r : ℕ) (i : Fin (r + r)) : Fin ((r + 1) + (r + 1)) :=
  Fin.cast (add_add_add_comm r r 1 1) (Fin.castAdd 2 i)

theorem tailSlot_ne (r : ℕ) : tailSlot r 0 ≠ tailSlot r 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [tailSlot, Fin.val_cast, Fin.val_natAdd, Fin.val_zero, Fin.val_one] at hv
  omega

theorem prefixSlot_ne_tailSlot (r : ℕ) (i : Fin (r + r)) (j : Fin 2) :
    prefixSlot r i ≠ tailSlot r j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [prefixSlot, tailSlot, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem tuple_prefix_tail {α : Type*} (r : ℕ)
    (v : Fin ((r + 1) + (r + 1)) → α) :
    v = EvenAppend.CM.Construction.evenAppend r 1 (fun i => v (prefixSlot r i)) ![v (tailSlot r 0), v (tailSlot r 1)] := by
  funext i
  let e := finCongr (add_add_add_comm r r 1 1)
  obtain ⟨k, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin (r + r) ⊕ Fin 2 ≃ Fin ((r + r) + 2)).surjective k
  cases j with
  | inl j =>
    simp only [EvenAppend.CM.Construction.evenAppend, Function.comp_apply, finSumFinEquiv_apply_left,
      prefixSlot, e, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq, Fin.append_left]
  | inr j =>
    fin_cases j <;>
      simp only [EvenAppend.CM.Construction.evenAppend, Function.comp_apply, finSumFinEquiv_apply_right,
        tailSlot, e, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq, Fin.append_right] <;> rfl

theorem select_two_slots {α : Type*} (r : ℕ)
    (a b : Fin ((r + 1) + (r + 1))) (hab : a ≠ b)
    (x y : Fin ((r + 1) + (r + 1)) → α)
    (hrest : ∀ i, i ≠ a → i ≠ b → x i = y i) :
    ∃ (σ : Equiv.Perm (Fin ((r + 1) + (r + 1)))) (u : Fin (r + r) → α),
      x ∘ σ = EvenAppend.CM.Construction.evenAppend r 1 u ![x a, x b] ∧
      y ∘ σ = EvenAppend.CM.Construction.evenAppend r 1 u ![y a, y b] := by
  obtain ⟨σ, hσa, hσb⟩ := exists_perm_pair (tailSlot r 0) (tailSlot r 1) a b (tailSlot_ne r) hab
  let u := fun i => x (σ (prefixSlot r i))
  refine ⟨σ, u, ?_, ?_⟩
  · simpa only [Function.comp_apply, hσa, hσb] using tuple_prefix_tail r (x ∘ σ)
  · have hu (i : Fin (r + r)) : y (σ (prefixSlot r i)) = u i := by
      apply (hrest _ ?_ ?_).symm
      · intro h
        exact prefixSlot_ne_tailSlot r i 0 (σ.injective (h.trans hσa.symm))
      · intro h
        exact prefixSlot_ne_tailSlot r i 1 (σ.injective (h.trans hσb.symm))
    simpa only [Function.comp_apply, hσa, hσb, hu] using tuple_prefix_tail r (y ∘ σ)

/-- Select a common residual tuple before applying a pullback. -/
theorem select_two_slots_map {α β : Type*} (F : α → β) (r : ℕ)
    (a b : Fin ((r + 1) + (r + 1))) (hab : a ≠ b)
    (x : Fin ((r + 1) + (r + 1)) → β) (y : Fin ((r + 1) + (r + 1)) → α)
    (hrest : ∀ i, i ≠ a → i ≠ b → x i = F (y i)) :
    ∃ (σ : Equiv.Perm (Fin ((r + 1) + (r + 1)))) (u : Fin (r + r) → α),
      x ∘ σ = EvenAppend.CM.Construction.evenAppend r 1 (F ∘ u) ![x a, x b] ∧
      y ∘ σ = EvenAppend.CM.Construction.evenAppend r 1 u ![y a, y b] := by
  obtain ⟨σ, hσa, hσb⟩ := exists_perm_pair (tailSlot r 0) (tailSlot r 1) a b (tailSlot_ne r) hab
  let u := fun i => y (σ (prefixSlot r i))
  refine ⟨σ, u, ?_, ?_⟩
  · have hu (i : Fin (r + r)) : x (σ (prefixSlot r i)) = F (u i) := by
      apply hrest
      · intro h
        exact prefixSlot_ne_tailSlot r i 0 (σ.injective (h.trans hσa.symm))
      · intro h
        exact prefixSlot_ne_tailSlot r i 1 (σ.injective (h.trans hσb.symm))
    simpa only [Function.comp_def, hσa, hσb, hu] using tuple_prefix_tail r (x ∘ σ)
  · simpa only [Function.comp_def, hσa, hσb] using tuple_prefix_tail r (y ∘ σ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.SelectSlots.CM.Construction
