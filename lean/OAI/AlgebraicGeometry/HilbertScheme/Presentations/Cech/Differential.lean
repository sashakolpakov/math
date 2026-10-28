import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Contraction

/-! # Differential -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Differential.ProjectiveCech

/-! The subset Čech differential squares to zero and respects its supports. -/

universe u v

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]

theorem cechDifferential_square (f : Finset σ → R) :
    Contraction.ProjectiveCech.cechDifferential R (Contraction.ProjectiveCech.cechDifferential R f) = 0 := by
  funext s
  let F : σ × σ → R := fun p => if p.1 = p.2 then 0 else
    Signs.ProjectiveCech.alternatingSign R s p.1 * Signs.ProjectiveCech.alternatingSign R (s.erase p.1) p.2 *
      f ((s.erase p.1).erase p.2)
  have hsum : Contraction.ProjectiveCech.cechDifferential R (Contraction.ProjectiveCech.cechDifferential R f) s = ∑ p ∈ s ×ˢ s, F p := by
    rw [Contraction.ProjectiveCech.cechDifferential, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Contraction.ProjectiveCech.cechDifferential, Finset.mul_sum]
    calc
      _ = ∑ j ∈ s.erase i, F (i, j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hij := (Finset.mem_erase.mp hj).1.symm
        simp only [F, ite_eq_right hij, mul_assoc]
      _ = ∑ j ∈ s, F (i, j) := by
        apply Finset.sum_subset (Finset.erase_subset i s)
        intro j hj hji
        have hij : i = j := by
          by_contra h
          exact hji (Finset.mem_erase.mpr ⟨Ne.symm h, hj⟩)
        simp only [F, ite_eq_left hij]
  rw [hsum]
  apply Finset.sum_involution (s := s ×ˢ s) (f := F) (fun p _ => p.swap)
  · intro p hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
    by_cases hij : p.1 = p.2
    · simp only [F, ite_eq_left hij, Prod.fst_swap, Prod.snd_swap, ite_eq_left hij.symm, add_zero]
    · have he : (s.erase p.1).erase p.2 = (s.erase p.2).erase p.1 := by
        ext i
        simp only [Finset.mem_erase]
        tauto
      simp only [F, ite_eq_right hij, Prod.fst_swap, Prod.snd_swap, ite_eq_right (Ne.symm hij)]
      rw [Signs.ProjectiveCech.alternatingSign_erase_anticommute R hi hj hij, he]
      ring
  · intro p _ hp hswap
    have hij : p.1 = p.2 := (congrArg Prod.fst hswap).symm
    exact hp (by simp only [F, ite_eq_left hij])
  · intro p hp
    rw [Finset.mem_product]
    exact (Finset.mem_product.mp hp).symm
  · intro p _
    exact Prod.swap_swap p

theorem cechDifferential_preserves_support (N : Finset σ) (f : Finset σ → R)
    (hf : ∀ s, ¬N ⊆ s → f s = 0) :
    ∀ s, ¬N ⊆ s → Contraction.ProjectiveCech.cechDifferential R f s = 0 := by
  intro s hs
  apply Finset.sum_eq_zero
  intro i _
  have hNi : ¬N ⊆ s.erase i := fun h => hs (h.trans (Finset.erase_subset i s))
  rw [hf _ hNi, mul_zero]

theorem cechDifferential_card_support (q : ℕ) (f : Finset σ → R)
    (hf : ∀ s, s.card ≠ q → f s = 0) :
    ∀ s, s.card ≠ q + 1 → Contraction.ProjectiveCech.cechDifferential R f s = 0 := by
  intro s hs
  apply Finset.sum_eq_zero
  intro i hi
  have hcard : (s.erase i).card ≠ q := by
    intro h
    exact hs ((Finset.card_erase_add_one hi).symm.trans (congrArg (· + 1) h))
  rw [hf _ hcard, mul_zero]

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Differential.ProjectiveCech
