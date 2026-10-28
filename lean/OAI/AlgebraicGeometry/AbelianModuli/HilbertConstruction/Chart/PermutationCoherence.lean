import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.CoordinatePermutations

/-! # Permutation Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.PermutationCoherence

noncomputable section

/-! Identity, inverse, and composition laws for ambient coordinate permutations. -/

universe u

variable (R : Type u) [CommRing R] {k l : ℕ}

theorem chartCoordinatePermutation_symm (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    (CoordinatePermutations.chartCoordinatePermutation R τ).symm = CoordinatePermutations.chartCoordinatePermutation R τ.symm := by
  ext x i <;> rfl

theorem chartCoordinatePermutation_one :
    CoordinatePermutations.chartCoordinatePermutation R (1 : Equiv.Perm (Fin k ⊕ Fin l)) = LinearEquiv.refl R _ := by
  ext x i <;> rfl

theorem chartCoordinatePermutation_mul (τ σ : Equiv.Perm (Fin k ⊕ Fin l)) :
    (CoordinatePermutations.chartCoordinatePermutation R (τ * σ)).toLinearMap =
      (CoordinatePermutations.chartCoordinatePermutation R τ).toLinearMap.comp (CoordinatePermutations.chartCoordinatePermutation R σ).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext i
    change Sum.elim x.1 x.2 (σ.symm (τ.symm (Sum.inl i))) =
      Sum.elim (CoordinatePermutations.chartCoordinatePermutation R σ x).1 (CoordinatePermutations.chartCoordinatePermutation R σ x).2
        (τ.symm (Sum.inl i))
    cases τ.symm (Sum.inl i) <;> rfl
  · funext i
    change Sum.elim x.1 x.2 (σ.symm (τ.symm (Sum.inr i))) =
      Sum.elim (CoordinatePermutations.chartCoordinatePermutation R σ x).1 (CoordinatePermutations.chartCoordinatePermutation R σ x).2
        (τ.symm (Sum.inr i))
    cases τ.symm (Sum.inr i) <;> rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.PermutationCoherence
