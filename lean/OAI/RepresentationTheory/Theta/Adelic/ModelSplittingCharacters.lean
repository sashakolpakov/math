import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter

/-! # Model Splitting Characters -/

namespace OAI.RepresentationTheory.Theta.Adelic.ModelSplittingCharacters

noncomputable section

/-! The inverse prescribed characters in the actual field model have
exactly the norm-character restrictions required by UnitarySplitting. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

theorem normSign_inv_self {k : Type} [Field k] (d : k) (a : kˣ) :
    (QuadraticNormCharacter.normSign d a)⁻¹ = QuadraticNormCharacter.normSign d a := by
  unfold QuadraticNormCharacter.normSign
  split <;> simp

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [LocallyCompactSpace k]
variable [IsUltrametricDist k] [CharZero k]
variable (d : k) (hd : d ≠ 0) (hns : ¬ IsSquare d) (hnd : ¬ DiscreteTopology k)

def nativeUnits : (QuadraticLocalField.FieldModel k d hns)ˣ →ₜ* (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ :=
  { Units.map (QuadraticLocalField.algebraEquiv k d hns).toMonoidHom with
    continuous_toFun := (QuadraticLocalField.coefficientHomeomorph k d hns).continuous.units_map _ }

omit [LocallyCompactSpace k] [CharZero k] in
theorem nativeUnits_scalar (a : kˣ) :
    nativeUnits d hns (Units.map (algebraMap k (QuadraticLocalField.FieldModel k d hns)).toMonoidHom a) =
      QuadraticNormSquareQuotient.scalarUnits d a := by
  apply Units.ext
  exact (QuadraticLocalField.algebraEquiv k d hns).commutes a.val

def modelSplittingCharacters (n m : ℕ) (χV χW : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle)
    (hV : ∀ a : kˣ, χV (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ n)
    (hW : ∀ a : kˣ, χW (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ m) :
    Weil.UnitarySplitting.Characters.Construction.SplittingCharacters k (QuadraticLocalField.FieldModel k d hns) n m where
  quadratic := QuadraticNormCharacter.nonarchimedeanNormCharacter d hd hnd
  quadratic_kernel := QuadraticLocalCharacter.model_quadratic_character d hd hns hnd
  hermitian := (χV.comp (nativeUnits d hns))⁻¹
  skewHermitian := (χW.comp (nativeUnits d hns))⁻¹
  hermitian_restriction := by
    intro a
    change (χV (nativeUnits d hns (Units.map (algebraMap k (QuadraticLocalField.FieldModel k d hns)).toMonoidHom a)))⁻¹ =
      QuadraticNormCharacter.normSign d a ^ n
    rw [nativeUnits_scalar, hV, ← inv_pow, normSign_inv_self]
  skewHermitian_restriction := by
    intro a
    change (χW (nativeUnits d hns (Units.map (algebraMap k (QuadraticLocalField.FieldModel k d hns)).toMonoidHom a)))⁻¹ =
      QuadraticNormCharacter.normSign d a ^ m
    rw [nativeUnits_scalar, hW, ← inv_pow, normSign_inv_self]

end

end OAI.RepresentationTheory.Theta.Adelic.ModelSplittingCharacters
