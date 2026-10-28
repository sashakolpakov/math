/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PermutedTupleSigns

/-! # Repeated Tuple Partners -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.RepeatedTuplePartners

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem exists_eq_ne_of_not_injective
    {α β : Type*} (f : α → β) (hf : ¬ Function.Injective f) :
    ∃ a b, f a = f b ∧ a ≠ b := by
  by_contra h
  apply hf
  intro a b hab
  by_contra hne
  exact h ⟨a, b, hab, hne⟩

theorem exists_partner_of_delete_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (hi : ¬ Function.Injective i)
    (k : Fin (n + 2)) (hk : Function.Injective (i ∘ k.succAbove)) :
    ∃ l, l ≠ k ∧ i l = i k := by
  obtain ⟨a, b, hab, hne⟩ := exists_eq_ne_of_not_injective i hi
  by_cases ha : a = k
  · subst a
    exact ⟨b, hne.symm, hab.symm⟩
  by_cases hb : b = k
  · subst b
    exact ⟨a, ha, hab⟩
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq ha
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hb
  exfalso
  apply hne
  rw [← ha', ← hb']
  exact congrArg k.succAbove (hk (by simpa [ha', hb'] using hab))

theorem eq_partner_of_delete_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l x : Fin (n + 2))
    (hk : Function.Injective (i ∘ k.succAbove))
    (hlk : l ≠ k) (hxk : x ≠ k) (hil : i l = i k) (hix : i x = i k) :
    x = l := by
  obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq hxk
  obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq hlk
  rw [← hx', ← hl']
  apply congrArg k.succAbove
  apply hk
  simp [hx', hl', hix, hil]

theorem delete_partner_injective {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hk : Function.Injective (i ∘ k.succAbove))
    (hlk : l ≠ k) (hil : i l = i k) :
    Function.Injective (i ∘ l.succAbove) := by
  intro a b hab
  apply Fin.succAbove_right_injective
  let x := l.succAbove a
  let y := l.succAbove b
  change x = y
  by_cases hxk : x = k
  · by_cases hyk : y = k
    · exact hxk.trans hyk.symm
    · have hyl : y = l := eq_partner_of_delete_injective
        i k l y hk hlk hyk hil (by simpa [x, y, hxk] using hab.symm)
      exact (l.succAbove_ne b hyl).elim
  · by_cases hyk : y = k
    · have hxl : x = l := eq_partner_of_delete_injective
        i k l x hk hlk hxk hil (by simpa [x, y, hyk] using hab)
      exact (l.succAbove_ne a hxl).elim
    · obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hxk
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hyk
      rw [← ha', ← hb']
      exact congrArg k.succAbove (hk (by simpa [x, y, ha', hb'] using hab))

theorem delete_not_injective_of_ne {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l m : Fin (n + 2))
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) (hil : i l = i k) :
    ¬ Function.Injective (i ∘ m.succAbove) := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hkm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hlm
  intro hm
  apply hkl
  rw [← ha, ← hb]
  exact congrArg m.succAbove (hm (by simpa [ha, hb] using hil.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.RepeatedTuplePartners
