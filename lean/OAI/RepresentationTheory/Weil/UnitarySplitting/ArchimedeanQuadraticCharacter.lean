import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanNormCoordinates
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormAdditiveMeasure

/-! # Archimedean Quadratic Character -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanQuadraticCharacter.Construction

noncomputable section

/-! In real coordinates the norm subgroup is the positive real numbers,
so the given quadratic character is the sign character. -/

theorem norm_range_in_complex_coordinates
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (e : ℝ ≃+* F) (k : E ≃+* ℂ)
    (hN : ∀ x : E, e.symm (Algebra.norm F x) = Complex.normSq (k x)) (a : F) :
    a ∈ Set.range (Algebra.norm F : E → F) ↔ 0 ≤ e.symm a := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [hN]
    exact Complex.normSq_nonneg _
  · intro ha
    refine ⟨k.symm (Real.sqrt (e.symm a) : ℂ), ?_⟩
    apply e.symm.injective
    rw [hN, k.apply_symm_apply, Complex.normSq_ofReal, Real.mul_self_sqrt ha]

theorem quadraticCharacter_real_positive_iff
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] [FiniteDimensional F E]
    (e : ℝ ≃+* F) (k : E ≃+* ℂ)
    (hN : ∀ x : E, e.symm (Algebra.norm F x) = Complex.normSq (k x))
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω) (a : Fˣ) :
    ω a = 1 ↔ 0 < e.symm (a : F) := by
  have hrange := Set.ext_iff.mp (NormAdditiveMeasure.Construction.unitsVal_preimage_norm_range ω hω) a
  change (a : F) ∈ Set.range (Algebra.norm F : E → F) ↔ ω a = 1 at hrange
  rw [← hrange, norm_range_in_complex_coordinates e k hN]
  have ha : e.symm (a : F) ≠ 0 := (map_ne_zero e.symm).mpr a.ne_zero
  exact ⟨fun h => lt_of_le_of_ne h ha.symm, le_of_lt⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanQuadraticCharacter.Construction
