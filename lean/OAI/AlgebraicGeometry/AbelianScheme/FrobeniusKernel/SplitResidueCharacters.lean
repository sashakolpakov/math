import OAI.RepresentationTheory.Hecke.BlockCharacters

/-! # Split Residue Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitResidueCharacters.Construction

noncomputable section

/-! Every actual residue character selects one of the complete split
coefficient components. No alignment of arithmetic and q-adic labels is assumed. -/

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (χ : NumberField.RingOfIntegers E →+* k)

include hsplit in
theorem residueCharacter_eq_of_coordinates (a b : NumberField.RingOfIntegers E)
    (h : j.residueCoordinates iota 1 a = j.residueCoordinates iota 1 b) : χ a = χ b := by
  have hk : a - b ∈ Ideal.span ({(q ^ 1 : NumberField.RingOfIntegers E)} :
      Set (NumberField.RingOfIntegers E)) := by
    rw [← (hsplit 1).2]
    change j.residueCoordinates iota 1 (a - b) = 0
    rw [map_sub, h, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hk
  apply sub_eq_zero.mp
  rw [← map_sub, hc, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow one_ne_zero,
    zero_mul]

include hsplit in
theorem exists_split_residueCharacter :
    ∃ τ : Gal(E/ℚ), χ = RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ := by
  classical
  have hs : (∑ τ : Gal(E/ℚ), χ (j.projector iota hsplit 1 τ)) = 1 := by
    rw [← map_sum]
    apply (residueCharacter_eq_of_coordinates j iota hsplit χ _ 1 ?_).trans (map_one χ)
    simp only [map_sum, j.projector_coordinates, map_one]
    ext υ
    simp [Finset.sum_apply, Pi.single_apply]
  have hn : ∃ τ : Gal(E/ℚ), χ (j.projector iota hsplit 1 τ) ≠ 0 := by
    by_contra! h
    simp only [h, Finset.sum_const_zero] at hs
    exact zero_ne_one hs
  obtain ⟨τ, hτ⟩ := hn
  refine ⟨τ, ?_⟩
  ext a
  let e := j.projector iota hsplit 1 τ
  let n := (j.residueCharacter iota τ 1 a).val
  have hc : j.residueCoordinates iota 1 (a * e) =
      j.residueCoordinates iota 1 ((n : NumberField.RingOfIntegers E) * e) := by
    rw [map_mul, map_mul, map_natCast, j.projector_coordinates]
    ext υ
    change j.residueCharacter iota υ 1 a * (Pi.single τ 1 : Gal(E/ℚ) → ZMod (q ^ 1)) υ =
      (n : ZMod (q ^ 1)) * (Pi.single τ 1 : Gal(E/ℚ) → ZMod (q ^ 1)) υ
    by_cases hv : υ = τ
    · subst υ
      simp only [Pi.single_eq_same, mul_one]
      exact (ZMod.natCast_zmod_val (j.residueCharacter iota τ 1 a)).symm
    · simp [hv]
  have he := residueCharacter_eq_of_coordinates j iota hsplit χ _ _ hc
  rw [map_mul, map_mul, map_natCast] at he
  rw [RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter_nat]
  exact mul_right_cancel₀ hτ he

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitResidueCharacters.Construction
