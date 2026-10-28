import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke

/-! # Reverse Active Weight -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReverseActiveWeight

noncomputable section

/-! Reversal preserves the exact predicate used by the original chosen
clearing exponent. Consequently the original choices agree. -/

def reverseActiveWeight (a : Intrinsic.Hecke.ActiveWeight) : Intrinsic.Hecke.ActiveWeight :=
  ⟨fun i => -a.val (Fin.rev i), by
    constructor
    · intro i j hij
      apply neg_le_neg
      exact a.property.1 (Fin.rev_le_rev.mpr hij)
    · rw [Finset.sum_neg_distrib]
      have h := Equiv.sum_comp Fin.revPerm a.val
      simpa only [Fin.revPerm_apply, h, a.property.2, neg_zero] using congrArg Neg.neg h⟩

theorem reverse_active_integral {s : ℕ} (v : Fin s) (a : Intrinsic.Hecke.ActiveWeight) (n : ℕ) :
    ((Intrinsic.Hecke.activeType v (reverseActiveWeight a)).shift n).IsIntegral ↔
      ((Intrinsic.Hecke.activeType v a).shift n).IsIntegral := by
  constructor <;> rintro ⟨hm, he⟩ <;> refine ⟨hm, ?_⟩ <;> intro w i
  · have h := he w (Fin.rev i)
    by_cases hw : w = v
    · simp only [AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.shift, Intrinsic.Hecke.activeType, reverseActiveWeight, hw, ite_true, Fin.rev_rev] at h ⊢
      omega
    · simp only [AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.shift, Intrinsic.Hecke.activeType, hw, ite_false] at h ⊢
      exact h
  · have h := he w (Fin.rev i)
    by_cases hw : w = v
    · simp only [AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.shift, Intrinsic.Hecke.activeType, reverseActiveWeight, hw, ite_true] at h ⊢
      omega
    · simp only [AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.shift, Intrinsic.Hecke.activeType, hw, ite_false] at h ⊢
      exact h

theorem choose_congr_predicate {α : Sort*} {p r : α → Prop}
    (h : p = r) (hp : ∃ x, p x) (hr : ∃ x, r x) : hp.choose = hr.choose := by
  subst r
  rfl

theorem reverse_clearingExponent {s : ℕ} (v : Fin s) (a : Intrinsic.Hecke.ActiveWeight) :
    Intrinsic.Hecke.clearingExponent v (reverseActiveWeight a) = Intrinsic.Hecke.clearingExponent v a := by
  apply choose_congr_predicate
  funext n
  exact propext (reverse_active_integral v a n)

theorem reverse_cleared_exponent {s : ℕ} (v w : Fin s) (a : Intrinsic.Hecke.ActiveWeight) (i : Fin 3) :
    (Intrinsic.Hecke.clearedActiveType v (reverseActiveWeight a)).val.exponent w i =
      2 * (Intrinsic.Hecke.clearingExponent v a : ℤ) - (Intrinsic.Hecke.clearedActiveType v a).val.exponent w (Fin.rev i) := by
  change (Intrinsic.Hecke.activeType v (reverseActiveWeight a)).exponent w i +
    Intrinsic.Hecke.clearingExponent v (reverseActiveWeight a) = _
  rw [reverse_clearingExponent]
  simp only [Intrinsic.Hecke.clearedActiveType, AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.shift, Intrinsic.Hecke.activeType, reverseActiveWeight]
  split_ifs <;> omega

end

end OAI.RepresentationTheory.Theta.Geometric.ReverseActiveWeight
