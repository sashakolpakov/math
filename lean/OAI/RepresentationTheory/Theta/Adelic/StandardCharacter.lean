import OAI.RepresentationTheory.Theta.Adelic.CharacterUniqueness
import OAI.RepresentationTheory.Theta.Adelic.TotallyRealData
import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization

/-! # Standard Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.StandardCharacter

noncomputable section

/-! The requested archimedean normalization uniquely identifies the
supplied principal-trivial global character with the canonical trace
character. This permits reuse of its exact native Gaussian formulas. -/

open scoped Classical _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.TotallyRealData OAI.RepresentationTheory.Theta.Adelic.CharacterUniqueness

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)

theorem standardArchCharacter_unique (hS : DataTheta.Descent.StandardArchCharacter (A := A) C.ψ) :
    C.ψ = AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter.CM.fieldAdelicCharacter F := by
  let : NumberField.IsTotallyReal F := TotallyRealData.arithmetic_totally_real A
  apply CharacterUniqueness.adelic_characters_eq_of_archimedean F C.ψ (AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter.CM.fieldAdelicCharacter F)
    C.ψ_continuous (AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter.CM.field_adelic_character_continuous F)
    (fun a => norm_ne_zero_iff.mp (by rw [C.ψ_unitary]; exact one_ne_zero))
    C.ψ_principal (AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter.CM.field_adelic_character_principal F)
  intro v t
  obtain ⟨i, rfl⟩ := A.enumerate.surjective v
  have h := hS i (A.real i t)
  rw [RingEquiv.symm_apply_apply] at h
  have hc := AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization.CM.field_adelic_character_standard_real_coordinate F (A.enumerate i) (A.real i) (A.real i t)
  rw [RingEquiv.symm_apply_apply] at hc
  exact h.trans hc.symm

end

end OAI.RepresentationTheory.Theta.Adelic.StandardCharacter
