import OAI.RepresentationTheory.Weil.UnitarySplitting.TracePairing

/-! # Norm One Parameters -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormOneParameters.Construction

noncomputable section

/-! An explicit infinite family of norm-one scalars in a quadratic field.
These scalars supply generic translates in the unitary Cayley domain. -/

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
variable (σ : E ≃ₐ[F] E)

omit [CharZero F] in
theorem exists_nonzero_antifixed (hσ : Function.Involutive σ)
    (hne : ∃ z : E, σ z ≠ z) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨z, hz⟩ := hne
  refine ⟨z - σ z, sub_ne_zero.mpr hz.symm, ?_⟩
  rw [map_sub, hσ]
  abel

theorem antifixed_not_scalar (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (a : F) :
    algebraMap F E a ≠ δ := by
  let : CharZero E := Algebra.charZero_of_charZero F E
  intro ha
  have hh := congrArg σ ha
  rw [σ.commutes, ha, hσδ] at hh
  have : δ = 0 := by linear_combination (1 / 2 : E) * hh
  exact hδ this

def normOneParameter (δ : E) (a : F) : E :=
  (algebraMap F E a + δ) / (algebraMap F E a - δ)

theorem normOneParameter_mem (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (a : F) :
    σ (normOneParameter δ a) * normOneParameter δ a = 1 := by
  have hm : algebraMap F E a - δ ≠ 0 :=
    sub_ne_zero.mpr (antifixed_not_scalar σ δ hδ hσδ a)
  have hp : algebraMap F E a + δ ≠ 0 := by
    intro h
    have he : algebraMap F E (-a) = δ := by rw [map_neg]; linear_combination -h
    exact antifixed_not_scalar σ δ hδ hσδ (-a) he
  simp only [normOneParameter, map_div₀, map_add, map_sub, σ.commutes, hσδ]
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  field_simp [hm, hp]

theorem normOneParameter_injective (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ) :
    Function.Injective (normOneParameter (F := F) δ) := by
  let : CharZero E := Algebra.charZero_of_charZero F E
  intro a b hab
  have ha := sub_ne_zero.mpr (antifixed_not_scalar σ δ hδ hσδ a)
  have hb := sub_ne_zero.mpr (antifixed_not_scalar σ δ hδ hσδ b)
  have hh := (div_eq_div_iff ha hb).mp hab
  apply (algebraMap F E).injective
  apply mul_right_cancel₀ hδ
  linear_combination -(1 / 2 : E) * hh

theorem infinite_normOne (hσ : Function.Involutive σ) (hne : ∃ z : E, σ z ≠ z) :
    Set.Infinite {z : E | σ z * z = 1} := by
  obtain ⟨δ, hδ, hσδ⟩ := exists_nonzero_antifixed σ hσ hne
  apply (Set.infinite_range_of_injective (normOneParameter_injective σ δ hδ hσδ)).mono
  rintro z ⟨a, rfl⟩
  exact normOneParameter_mem σ δ hδ hσδ a

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormOneParameters.Construction
