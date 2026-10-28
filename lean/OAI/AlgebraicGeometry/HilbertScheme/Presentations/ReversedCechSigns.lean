import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Signs

/-! # Reversed Cech Signs -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReversedCechSigns.ProjectiveCech

/-! Reversing the variable order changes Čech signs by a factor depending only on face cardinality. -/

universe u v

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]

theorem strict_sides_card (s : Finset σ) (i : σ) (hi : i ∈ s) :
    (s.filter (· < i)).card + (s.filter (i < ·)).card = s.card - 1 := by
  have hu : s.filter (· < i) ∪ s.filter (i < ·) = s.erase i := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hj, hji⟩ | ⟨hj, hij⟩)
      · exact ⟨ne_of_lt hji, hj⟩
      · exact ⟨ne_of_gt hij, hj⟩
    · rintro ⟨hji, hj⟩
      obtain h | h := lt_or_gt_of_ne hji
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, h⟩
  have hd : Disjoint (s.filter (· < i)) (s.filter (i < ·)) := by
    apply Finset.disjoint_left.mpr
    intro j hj₁ hj₂
    exact lt_asymm (Finset.mem_filter.mp hj₁).2 (Finset.mem_filter.mp hj₂).2
  have h := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_erase_of_mem hi] at h
  exact h.symm

theorem alternatingSign_orderDual (s : Finset σ) (i : σ) (hi : i ∈ s) :
    Cech.Signs.ProjectiveCech.alternatingSign (σ := σᵒᵈ) R s i = (-1 : R) ^ (s.card - 1) * Cech.Signs.ProjectiveCech.alternatingSign R s i := by
  have hs := strict_sides_card s i hi
  have hsq := Cech.Signs.ProjectiveCech.alternatingSign_square R s i
  change (-1 : R) ^ (s.filter (· < i)).card * (-1 : R) ^ (s.filter (· < i)).card = 1 at hsq
  change (-1 : R) ^ (s.filter (i < ·)).card =
    (-1 : R) ^ (s.card - 1) * (-1 : R) ^ (s.filter (· < i)).card
  rw [← hs, pow_add, mul_right_comm, hsq, one_mul]

theorem neg_one_power_square (k : ℕ) : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReversedCechSigns.ProjectiveCech
