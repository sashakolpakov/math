import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalCompletion

/-! # Character Separation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual split completion separates its integral characters.
This detects orthogonality of the distinct Tate eigenblocks. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)

include hg in
theorem Data.SphericalPELAlbaneseData.localCharacter_injective : Function.Injective D.localCharacter := by
  intro v w hvw
  have he (z : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) :
      D.localCompletionMap z v = D.localCompletionMap z w := by
    induction z using TensorProduct.inductionOn with
    | tmul c a => rw [Data.SphericalPELAlbaneseData.localCompletionMap_tmul, Data.SphericalPELAlbaneseData.localCompletionMap_tmul, hvw]
    | add z z' hz hz' => simp only [map_add, Pi.add_apply, hz, hz']
  classical
  by_contra hne
  obtain ⟨z, hz⟩ := hg.1.2 (Pi.single v 1)
  have hh := he z
  rw [hz] at hh
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne), one_ne_zero] at hh

include hg in
theorem Data.SphericalPELAlbaneseData.rationalCharacter_separates {v w : Fin s × Bool} (hvw : v ≠ w) :
    ∃ a : NumberField.RingOfIntegers E,
      (D.localCharacter v a : ℚ_[q]) ≠ (D.localCharacter w a : ℚ_[q]) := by
  classical
  by_contra hn
  push Not at hn
  apply hvw
  apply D.localCharacter_injective hg
  apply RingHom.ext
  intro a
  exact Subtype.val_injective (hn a)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
