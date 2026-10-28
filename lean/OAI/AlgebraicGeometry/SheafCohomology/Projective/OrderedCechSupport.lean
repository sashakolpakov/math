import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupportContraction

/-! # Ordered Cech Support -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport

noncomputable section

/-! Cochains requiring every vertex have zero differential. -/

open _root_.AlgebraicGeometry.Scheme.Modules
universe u v
variable (R : Type u) [CommRing R] {ι : Type v} [LinearOrder ι]

theorem orderedCechIndex_delete_missing {n : ℕ} (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι (n + 1))
    (k : Fin (n + 2)) : a.val k ∉ Set.range (a.delete k).val := by
  rintro ⟨l, hl⟩
  have he : k.succAbove l = k := a.property.injective hl
  exact Fin.succAbove_ne k l he

theorem orderedCechSupportDifferential_univ (n : ℕ) :
    OrderedCechSupportContraction.orderedCechSupportDifferential R (Set.univ : Set ι) n = 0 := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext a
  change (∑ k : Fin (n + 2), (-1 : R) ^ (k : ℕ) * s.val (a.delete k)) = 0
  apply Finset.sum_eq_zero
  intro k _
  have hmiss : ¬ Set.univ ⊆ Set.range (a.delete k).val :=
    fun h => orderedCechIndex_delete_missing a k (h (Set.mem_univ (a.val k)))
  rw [s.property _ hmiss, mul_zero]

theorem orderedCechFullSupport_eq_zero_of_card_ne [Fintype ι] (n : ℕ)
    (hn : n + 1 ≠ Fintype.card ι)
    (s : OrderedCechSupportContraction.OrderedCechSupportCochain R (Set.univ : Set ι) n) : s = 0 := by
  apply Subtype.ext
  funext a
  apply s.property
  intro h
  have hs : Function.Surjective a.val := fun x => h (Set.mem_univ x)
  have he := Fintype.card_congr (Equiv.ofBijective a.val ⟨a.property.injective, hs⟩)
  exact hn (by simpa using he)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport
