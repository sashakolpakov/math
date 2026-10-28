import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadialSatake
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange
import OAI.RepresentationTheory.Hecke.GaloisValuationCm

/-! # Satake Conjugate Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeConjugateNormalization.Iwasawa

noncomputable section

/-! Normalize the actual conjugated algebraic Satake character. Its
parameter is the conjugated inverse root up to the sign of sqrt(q). -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

def normalizedTorusPoint {k : Type*} [CommRing k] (s e : kˣ) : Fin 3 → kˣ := ![s, s⁻¹, e]

theorem normalize_conjugate_torus (s e : ParameterChoices.Qbarˣ) (hs : (s : ParameterChoices.Qbar) ^ 2 = (q : ParameterChoices.Qbar))
    (σ : Gal(ParameterChoices.Qbar/ℚ)) :
    ∃ eσ : ParameterChoices.Qbarˣ,
      ((eσ : ParameterChoices.Qbar) = σ (e : ParameterChoices.Qbar) ∨ (eσ : ParameterChoices.Qbar) = -(σ (e : ParameterChoices.Qbar))) ∧
      σ.toAlgHom.comp (SatakeBaseChange.Iwasawa.torusSatakeOver q (normalizedTorusPoint s e)) =
        SatakeBaseChange.Iwasawa.torusSatakeOver q (normalizedTorusPoint s eσ) ∧
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (s : ParameterChoices.Qbar) (e : ParameterChoices.Qbar) i))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (s : ParameterChoices.Qbar) (eσ : ParameterChoices.Qbar)) := by
  have hsσ : (σ (s : ParameterChoices.Qbar)) ^ 2 = (s : ParameterChoices.Qbar) ^ 2 := by rw [← map_pow, hs, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsσ with h | h
  · let eσ := Units.map σ.toMonoidHom e
    have ht : (fun i => Units.map σ.toMonoidHom (normalizedTorusPoint s e i)) =
        normalizedTorusPoint s eσ := by
      funext i
      apply Units.ext
      fin_cases i <;> simp [normalizedTorusPoint, h, eσ]
    refine ⟨eσ, Or.inl rfl, ?_, ?_⟩
    · apply AlgHom.ext
      intro T
      change σ.toAlgHom (SatakeBaseChange.Iwasawa.torusSatakeOver q (normalizedTorusPoint s e) T) = _
      rw [SatakeBaseChange.Iwasawa.torusSatakeOver_map]
      change SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map σ.toMonoidHom (normalizedTorusPoint s e i)) T = _
      rw [ht]
    · refine ⟨1, one_ne_zero, Equiv.refl _, ?_⟩
      intro i
      fin_cases i <;> simp [RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple, h, eσ]
  · let eσ := -(Units.map σ.toMonoidHom e)
    have ht : (fun i => Units.map σ.toMonoidHom (normalizedTorusPoint s e i)) =
        (fun i => (-1 : ParameterChoices.Qbarˣ) * normalizedTorusPoint s eσ i) := by
      funext i
      apply Units.ext
      fin_cases i <;> simp [normalizedTorusPoint, h, eσ]
    refine ⟨eσ, Or.inr rfl, ?_, ?_⟩
    · apply AlgHom.ext
      intro T
      change σ.toAlgHom (SatakeBaseChange.Iwasawa.torusSatakeOver q (normalizedTorusPoint s e) T) = _
      rw [SatakeBaseChange.Iwasawa.torusSatakeOver_map]
      change SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map σ.toMonoidHom (normalizedTorusPoint s e i)) T = _
      rw [ht, SatakeBaseChange.Iwasawa.torusSatakeOver_scale]
    · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, Equiv.refl _, ?_⟩
      intro i
      fin_cases i <;> simp [RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple, h, eσ]

theorem algebraicDualSatakeCharacter_normalized_conjugate (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ)
    (σ : Gal(ParameterChoices.Qbar/ℚ)) :
    ∃ eσ : ParameterChoices.Qbarˣ,
      ((eσ : ParameterChoices.Qbar) = σ ((a : ParameterChoices.Qbar)⁻¹) ∨ (eσ : ParameterChoices.Qbar) = -(σ ((a : ParameterChoices.Qbar)⁻¹))) ∧
      σ.toAlgHom.comp (DualRadialSatake.Iwasawa.algebraicDualSatakeCharacter q j a) =
        SatakeBaseChange.Iwasawa.torusSatakeOver q (normalizedTorusPoint (DualRadialSatake.Iwasawa.algebraicSqrtUnit q j) eσ) ∧
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual
        (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) ((a : ParameterChoices.Qbar)⁻¹) i))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) (eσ : ParameterChoices.Qbar)) := by
  simpa only [Units.val_inv_eq_inv_val, DualRadialSatake.Iwasawa.algebraicDualSatakeCharacter, DualRadialSatake.Iwasawa.algebraicDualTorusPoint,
    normalizedTorusPoint, DualRadialSatake.Iwasawa.algebraicSqrtUnit, Units.val_mk0] using
    normalize_conjugate_torus q (DualRadialSatake.Iwasawa.algebraicSqrtUnit q j) a⁻¹ (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) σ

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeConjugateNormalization.Iwasawa
