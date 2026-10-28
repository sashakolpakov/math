import OAI.RepresentationTheory.Weil.UnitarySplitting.Oscillator

/-! # Heisenberg -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg.Construction

noncomputable section

/-! Weyl commutation relations for the actual Schrödinger operators.
These identities are independent of any metaplectic lift or splitting. -/

open scoped BigOperators

variable {F : Type} [NormedField F] [CharZero F] {d : ℕ}

omit [CharZero F] in
theorem standardSymplecticPairing_neg_right (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    Oscillator.Construction.standardSymplecticPairing d v (-v) = 0 := by
  unfold Oscillator.Construction.standardSymplecticPairing
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Pi.neg_apply]
  ring

omit [CharZero F] in
theorem standardSymplecticPairing_neg_left (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    Oscillator.Construction.standardSymplecticPairing d (-v) v = 0 := by
  unfold Oscillator.Construction.standardSymplecticPairing
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Pi.neg_apply]
  ring

omit [CharZero F] in
theorem heisenbergFunction_zero (ψ : AddChar F ℂ) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (0 : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) f = f := by
  funext x
  simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction]

theorem heisenbergFunction_composition (ψ : AddChar F ℂ)
    (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ w f) =
      ψ (Oscillator.Construction.standardSymplecticPairing d v w / 2) • Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (v + w) f := by
  funext x
  have hphase :
      (∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)) +
          (∑ i, w (Sum.inr i) * (x i - v (Sum.inl i) - w (Sum.inl i) / 2)) =
        Oscillator.Construction.standardSymplecticPairing d v w / 2 +
          ∑ i, (v (Sum.inr i) + w (Sum.inr i)) *
            (x i - (v (Sum.inl i) + w (Sum.inl i)) / 2) := by
    unfold Oscillator.Construction.standardSymplecticPairing
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
    ring
  have harg : (fun i => x i - v (Sum.inl i) - w (Sum.inl i)) =
      (fun i => x i - (v (Sum.inl i) + w (Sum.inl i))) := by
    funext i
    ring
  change ψ _ * (ψ _ * f _) = ψ _ * (ψ _ * f _)
  rw [← mul_assoc, ← ψ.map_add_eq_mul, ← mul_assoc, ← ψ.map_add_eq_mul,
    hphase, harg]
  simp only [Pi.add_apply]

theorem heisenbergFunction_neg_left_cancel (ψ : AddChar F ℂ)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v) (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) = f := by
  rw [heisenbergFunction_composition, standardSymplecticPairing_neg_left]
  simp [heisenbergFunction_zero]

theorem heisenbergFunction_neg_right_cancel (ψ : AddChar F ℂ)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v) f) = f := by
  rw [heisenbergFunction_composition, standardSymplecticPairing_neg_right]
  simp [heisenbergFunction_zero]

/-- Weyl operators are genuine complex-linear automorphisms on functions.
Restriction to the Bruhat space is a separate analytic assertion. -/
def heisenbergLinearEquiv (ψ : AddChar F ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    (Local.FunctionsMetaplectic.Construction.Position F d → ℂ) ≃ₗ[ℂ] (Local.FunctionsMetaplectic.Construction.Position F d → ℂ) where
  toFun := Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v
  invFun := Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v)
  left_inv := heisenbergFunction_neg_left_cancel ψ v
  right_inv := heisenbergFunction_neg_right_cancel ψ v
  map_add' f g := by
    funext x
    exact mul_add _ _ _
  map_smul' a f := by
    exact Oscillator.Construction.heisenbergFunction_smul d ψ v a f

theorem heisenbergFunction_ne_zero (ψ : AddChar F ℂ)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (hf : f ≠ 0) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f ≠ 0 := by
  intro h
  apply hf
  apply (heisenbergLinearEquiv ψ v).injective
  rw [map_zero]
  exact h

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg.Construction
