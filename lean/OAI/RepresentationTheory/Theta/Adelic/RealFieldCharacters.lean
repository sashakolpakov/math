import OAI.RepresentationTheory.Theta.Adelic.RealFieldCoordinates
import OAI.RepresentationTheory.Theta.Adelic.LocalNormCharacter
import OAI.RepresentationTheory.Theta.Adelic.ModelSplittingCharacters
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourierUnitary

/-! # Real Field Characters -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters

noncomputable section

/-! The native prescribed characters in the real quadratic field model
have the exact norm-character restrictions used by the weighted splitting. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourierUnitary.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.RealFieldCoordinates OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.ModelSplittingCharacters

variable (d : ℝ) (hd : d ≠ 0) (hns : ¬ IsSquare d)

def realNormCharacter : ℝˣ →ₜ* Circle :=
  LocalNormCharacter.localNormCharacter Weil.UnitarySplitting.RealFourierUnitary.Construction.real_nondiscrete d hd

theorem real_model_quadratic_character :
    Weil.UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := QuadraticLocalField.FieldModel ℝ d hns) (realNormCharacter d hd) := by
  intro a
  change QuadraticNormCharacter.normSign d a = 1 ↔ _
  rw [QuadraticNormCharacter.normSign_eq_one_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨Units.map (QuadraticLocalField.algebraEquiv ℝ d hns).symm.toMonoidHom b, ?_⟩
    change Algebra.norm ℝ ((QuadraticLocalField.algebraEquiv ℝ d hns).symm b.val) = a.val
    rw [QuadraticLocalField.model_norm, AlgEquiv.apply_symm_apply]
    exact congrArg Units.val hb
  · rintro ⟨b, hb⟩
    refine ⟨Units.map (QuadraticLocalField.algebraEquiv ℝ d hns).toMonoidHom b, ?_⟩
    apply Units.ext
    change QuadraticAlgebra.norm (QuadraticLocalField.algebraEquiv ℝ d hns b.val) = a.val
    rw [← QuadraticLocalField.model_norm]
    exact hb

def realNativeUnits : (QuadraticLocalField.FieldModel ℝ d hns)ˣ →ₜ* (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d)ˣ :=
  { Units.map (QuadraticLocalField.algebraEquiv ℝ d hns).toMonoidHom with
    continuous_toFun := (RealFieldCoordinates.realHomeomorph d hns).continuous.units_map _ }

theorem realNativeUnits_scalar (a : ℝˣ) :
    realNativeUnits d hns (Units.map (algebraMap ℝ (QuadraticLocalField.FieldModel ℝ d hns)).toMonoidHom a) =
      QuadraticNormSquareQuotient.scalarUnits d a := by
  apply Units.ext
  exact (QuadraticLocalField.algebraEquiv ℝ d hns).commutes a.val

def realSplittingCharacters (n m : ℕ) (χV χW : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic ℝ d)ˣ →ₜ* Circle)
    (hV : ∀ a : ℝˣ, χV (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ n)
    (hW : ∀ a : ℝˣ, χW (QuadraticNormSquareQuotient.scalarUnits d a) = QuadraticNormCharacter.normSign d a ^ m) :
    Weil.UnitarySplitting.Characters.Construction.SplittingCharacters ℝ (QuadraticLocalField.FieldModel ℝ d hns) n m where
  quadratic := realNormCharacter d hd
  quadratic_kernel := real_model_quadratic_character d hd hns
  hermitian := (χV.comp (realNativeUnits d hns))⁻¹
  skewHermitian := (χW.comp (realNativeUnits d hns))⁻¹
  hermitian_restriction := by
    intro a
    change (χV (realNativeUnits d hns (Units.map (algebraMap ℝ (QuadraticLocalField.FieldModel ℝ d hns)).toMonoidHom a)))⁻¹ =
      QuadraticNormCharacter.normSign d a ^ n
    rw [realNativeUnits_scalar, hV, ← inv_pow, ModelSplittingCharacters.normSign_inv_self]
  skewHermitian_restriction := by
    intro a
    change (χW (realNativeUnits d hns (Units.map (algebraMap ℝ (QuadraticLocalField.FieldModel ℝ d hns)).toMonoidHom a)))⁻¹ =
      QuadraticNormCharacter.normSign d a ^ m
    rw [realNativeUnits_scalar, hW, ← inv_pow, ModelSplittingCharacters.normSign_inv_self]

end

end OAI.RepresentationTheory.Theta.Adelic.RealFieldCharacters
