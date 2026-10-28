import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates
import Mathlib.Order.WithBot

/-! # Indices -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices

noncomputable section

/-! Deleting the distinguished chart from the ordered indices of a
relative Čech cover. -/

open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates

universe u
variable {ι : Type u} [LinearOrder ι] {n : ℕ}

theorem succ_ne_bot (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1))
    (h : a.val 0 = ⊥) (j : Fin n) : a.val j.succ ≠ ⊥ := by
  intro hj
  have ht := a.property (Fin.succ_pos j)
  rw [h, hj] at ht
  exact (lt_irrefl _ ht)

def tail (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1)) (h : a.val 0 = ⊥) : AugmentedOrdered.Cech.Index ι n :=
  ⟨fun j => (a.val j.succ).unbot (succ_ne_bot a h j), by
    intro i j hij
    exact (WithBot.unbot_lt_unbot_iff _ _).mpr
      (a.property (Fin.succ_lt_succ_iff.mpr hij))⟩

theorem coe_tail (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1)) (h : a.val 0 = ⊥) (j : Fin n) :
    ((tail a h).val j : WithBot ι) = a.val j.succ :=
  WithBot.coe_unbot _ _

theorem all_ne_bot (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 1))
    (h : a.val 0 ≠ ⊥) (j : Fin (n + 1)) : a.val j ≠ ⊥ := by
  intro hj
  apply h
  apply le_antisymm
  · exact hj ▸ a.property.monotone (Fin.zero_le j)
  · exact bot_le

theorem delete_zero_ne_bot (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2))
    (h : a.val 0 = ⊥) : (a.delete 0).val 0 ≠ ⊥ := by
  exact succ_ne_bot a h 0

theorem delete_succ_bot (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2))
    (h : a.val 0 = ⊥) (j : Fin (n + 1)) : (a.delete j.succ).val 0 = ⊥ := by
  simpa only [AugmentedOrdered.Cech.Index.delete, Function.comp_apply, Fin.succ_succAbove_zero] using h

theorem delete_ne_bot (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2))
    (h : a.val 0 ≠ ⊥) (j : Fin (n + 2)) : (a.delete j).val 0 ≠ ⊥ :=
  all_ne_bot a h (j.succAbove 0)

theorem tail_delete_succ (a : AugmentedOrdered.Cech.Index (WithBot ι) (n + 2))
    (h : a.val 0 = ⊥) (j : Fin (n + 1)) :
    tail (a.delete j.succ) (delete_succ_bot a h j) = (tail a h).delete j := by
  apply Subtype.ext
  funext i
  apply WithBot.coe_injective
  rw [coe_tail]
  change a.val (j.succ.succAbove i.succ) = ((tail a h).val (j.succAbove i) : WithBot ι)
  rw [Fin.succ_succAbove_succ, coe_tail]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Indices
