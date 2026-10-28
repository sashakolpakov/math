import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeExistence

namespace OAI.Algorithms

/-! Elementary low-weight counting by successive single-coordinate updates. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

def lowWords (D h : ℕ) : Finset (Fin D → F3) :=
  Finset.univ.filter fun w => weight w ≤ h

@[simp] theorem mem_lowWords {D h : ℕ} (w : Fin D → F3) :
    w ∈ lowWords D h ↔ weight w ≤ h := by simp [lowWords]

@[simp] theorem zero_mem_lowWords (D h : ℕ) : (0 : Fin D → F3) ∈ lowWords D h := by
  simp

theorem support_update_zero {D : ℕ} (w : Fin D → F3) (c : Fin D) :
    support (Function.update w c 0) = (support w).erase c := by
  ext i
  by_cases hi : i = c
  · subst i; simp
  · simp [hi ]

theorem weight_update_zero {D : ℕ} (w : Fin D → F3) (c : Fin D)
    (hc : w c ≠ 0) : weight (Function.update w c 0) + 1 = weight w := by
  rw [weight, support_update_zero]
  exact Finset.card_erase_add_one ((mem_support w c).mpr hc)

abbrev UpdateSymbol (D : ℕ) := Option (Fin D × F3)

def applySymbol {D : ℕ} : UpdateSymbol D → (Fin D → F3) → (Fin D → F3)
  | none, w => w
  | some (c, a), w => Function.update w c a

theorem lowWords_succ_cover (D h : ℕ) :
    lowWords D (h + 1) ⊆
      ((Finset.univ : Finset (UpdateSymbol D)) ×ˢ lowWords D h).image
        (fun p => applySymbol p.1 p.2) := by
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    exact Finset.mem_image.mpr ⟨(none, 0), by simp, rfl⟩
  · have hex : ∃ c, w c ≠ 0 := by
      by_contra! hn
      exact hw0 (funext hn)
    obtain ⟨c, hc⟩ := hex
    have hlow : Function.update w c 0 ∈ lowWords D h := by
      rw [mem_lowWords]
      have hweight := weight_update_zero w c hc
      have hw' := (mem_lowWords w).mp hw
      omega
    refine Finset.mem_image.mpr
      ⟨(some (c, w c), Function.update w c 0), by simp [hlow], ?_⟩
    simp [applySymbol]

theorem lowWords_card_le (D h : ℕ) :
    (lowWords D h).card ≤ (1 + 3 * D) ^ h := by
  induction h with
  | zero =>
      have heq : lowWords D 0 = {0} := by
        ext w
        simp
      simp [heq]
  | succ h ih =>
      calc
        (lowWords D (h + 1)).card ≤
            (((Finset.univ : Finset (UpdateSymbol D)) ×ˢ lowWords D h).image
              (fun p => applySymbol p.1 p.2)).card :=
          Finset.card_le_card (lowWords_succ_cover D h)
        _ ≤ ((Finset.univ : Finset (UpdateSymbol D)) ×ˢ lowWords D h).card :=
          Finset.card_image_le
        _ = (1 + 3 * D) * (lowWords D h).card := by
          simp [UpdateSymbol, Fintype.card_option, Fintype.card_prod,
            ZMod.card, Nat.mul_comm, Nat.add_comm]
        _ ≤ (1 + 3 * D) * (1 + 3 * D) ^ h := Nat.mul_le_mul_left _ ih
        _ = (1 + 3 * D) ^ (h + 1) := by rw [pow_succ, Nat.mul_comm]

theorem lowWords_card_le_four (D h : ℕ) (hD : 0 < D) :
    (lowWords D h).card ≤ (4 * D) ^ h := by
  exact (lowWords_card_le D h).trans
    (Nat.pow_le_pow_left (by omega : 1 + 3 * D ≤ 4 * D) h)

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
