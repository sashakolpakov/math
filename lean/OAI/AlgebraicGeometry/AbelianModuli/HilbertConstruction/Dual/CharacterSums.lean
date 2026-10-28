import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterOrthogonality

/-! # Character Sums -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.CharacterSums

noncomputable section

/-! Summing all finite abelian characters detects the group identity, including inverse character values. -/
universe u v
variable (K : Type u) [Field K] (G : Type v) [CommGroup G] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] [Fintype (G →* Kˣ)]

theorem finiteCharacters_sum_apply [DecidableEq G] (a : G) :
    ∑ χ : G →* Kˣ, (χ a : K) = if a = 1 then (Fintype.card G : K) else 0 := by
  classical
  by_cases ha : a = 1
  · subst a
    have hc : Fintype.card (G →* Kˣ) = Fintype.card G := by
      simpa only [Nat.card_eq_fintype_card] using
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G K
    simp [hc]
  · rw [ite_eq_right ha]
    let e : (G →* Kˣ) →* Kˣ :=
      { toFun := fun χ => χ a
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have he : e ≠ 1 := by
      obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G K ha
      intro h
      exact hχ (congrArg (fun f : (G →* Kˣ) →* Kˣ => f χ) h)
    exact CharacterOrthogonality.finiteCharacter_sum_eq_zero e he

theorem finiteCharacters_sum_inv_apply [DecidableEq G] (a : G) :
    ∑ χ : G →* Kˣ, (χ a : K)⁻¹ = if a = 1 then (Fintype.card G : K) else 0 := by
  simpa using finiteCharacters_sum_apply K G a⁻¹

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.CharacterSums
