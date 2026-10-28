import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperDiagonalConjugation

/-! # Triangular Conjugates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.TriangularConjugates.Construction

noncomputable section

/-! Compact upper-unitriangular families have compact containers for
all diagonal conjugates with uniformly bounded coordinate ratios. -/

open Set _root_.Matrix
open scoped Classical _root_.Matrix.Norms.Elementwise

theorem compact_matrix_unit_entries_bound {n : ℕ}
    (C : Set (Matrix (Fin n) (Fin n) ℝ)ˣ) (hC : IsCompact C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ g ∈ C, ∀ i j, |g.val i j| ≤ c := by
  have hv : Continuous (fun g : (Matrix (Fin n) (Fin n) ℝ)ˣ => g.val) := Units.continuous_val
  have hc : Continuous (fun g : (Matrix (Fin n) (Fin n) ℝ)ˣ => ‖g.val‖) :=
    continuous_norm.comp hv
  obtain ⟨c, hc⟩ := hC.bddAbove_image hc.continuousOn
  refine ⟨max 0 c, le_max_left _ _, fun g hg i j => ?_⟩
  exact ((norm_le_pi_norm (g.val i) j).trans (norm_le_pi_norm g.val i)).trans
    ((hc ⟨g, hg, rfl⟩).trans (le_max_right _ _))

theorem diagonal_matrix_unit_inverse {n : ℕ} (a : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (ha : a.val = diagonal d) :
    (a⁻¹).val = diagonal (fun i => (d i)⁻¹) := by
  have he : a.val * diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [ha, Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (hd _), Matrix.diagonal_one]
  apply (a.isUnit.mul_right_injective)
  exact a.val_inv.trans he.symm

theorem compact_upper_diagonal_conjugates {n : ℕ}
    (C : Set (Matrix (Fin n) (Fin n) ℝ)ˣ) (hC : IsCompact C)
    (htri : ∀ u ∈ C, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular u.val) (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : Set (Matrix (Fin n) (Fin n) ℝ)ˣ, IsCompact D ∧
      ∀ (d : Fin n → ℝ), (∀ i, 0 < d i) →
        (∀ i j, i ≤ j → d i / d j ≤ R) →
        ∀ a : (Matrix (Fin n) (Fin n) ℝ)ˣ, a.val = diagonal d →
          ∀ u ∈ C, a * u * a⁻¹ ∈ D := by
  obtain ⟨c, hc, hbound⟩ := compact_matrix_unit_entries_bound C hC
  refine ⟨{g | UpperUnitriangularMatrices.Construction.IsUpperUnitriangular g.val ∧ ∀ i j, |g.val i j| ≤ R * c},
    UpperUnitriangularMatrices.Construction.bounded_upper_unitriangular_isCompact n (R * c), fun d hd hratio a ha u hu => ?_⟩
  change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (a.val * u.val * (a⁻¹).val) ∧
    ∀ i j, |(a.val * u.val * (a⁻¹).val) i j| ≤ R * c
  rw [diagonal_matrix_unit_inverse a d (fun i => (hd i).ne') ha, ha]
  exact ⟨(htri u hu).diagonal_conjugation d (fun i => (hd i).ne'),
    UpperDiagonalConjugation.Construction.diagonal_conjugation_entry_bound d hd u.val (htri u hu).1 c R hc hR (hbound u hu) hratio⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.TriangularConjugates.Construction
