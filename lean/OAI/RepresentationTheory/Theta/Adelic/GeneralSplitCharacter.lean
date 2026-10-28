import OAI.RepresentationTheory.Theta.Adelic.SplitNorm
import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitDeterminant

/-! # General Split Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeneralSplitCharacter

noncomputable section

/-! The prescribed split quadratic characters give genuine determinant
characters of both full unitary factors. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitNorm OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitDeterminant

variable {k : Type} [Field k] [CharZero k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)

def splitSection : kˣ →* (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ where
  toFun := SplitNorm.normPreimage r hr hr0
  map_one' := by
    apply Units.ext
    change (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (1, 1) = 1
    exact map_one _
  map_mul' a b := by
    apply Units.ext
    change (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (a.val * b.val, 1) =
      (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (a.val, 1) * (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (b.val, 1)
    rw [← map_mul]
    simp only [Prod.mk_mul_mk, one_mul]

theorem splitSection_plus (a : kˣ) : SpecialUnitary.SplitAlgebra.plus r hr hr0 (splitSection r hr hr0 a).val = a.val :=
  congrArg Prod.fst ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).apply_symm_apply (a.val, 1))

theorem splitSection_minus (a : kˣ) : SpecialUnitary.SplitAlgebra.minus r hr hr0 (splitSection r hr hr0 a).val = 1 :=
  congrArg Prod.snd ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).apply_symm_apply (a.val, 1))

theorem unit_factorization (a : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (t : kˣ)
    (ha : SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val * t.val = SpecialUnitary.SplitAlgebra.plus r hr hr0 a.val) :
    a = Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom
        (Units.map (SpecialUnitary.SplitAlgebra.minus r hr hr0).toMonoidHom a) * splitSection r hr hr0 t := by
  apply Units.ext
  apply SpecialUnitary.SplitAlgebra.ext_components r hr hr0
  · change SpecialUnitary.SplitAlgebra.plus r hr hr0 a.val = SpecialUnitary.SplitAlgebra.plus r hr hr0
      (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) (SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val) * (splitSection r hr hr0 t).val)
    rw [map_mul, splitSection_plus]
    change SpecialUnitary.SplitAlgebra.plus r hr hr0 a.val = (SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val + r * 0) * t.val
    simpa only [mul_zero, add_zero] using ha.symm
  · change SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val = SpecialUnitary.SplitAlgebra.minus r hr hr0
      (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) (SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val) * (splitSection r hr hr0 t).val)
    rw [map_mul, splitSection_minus]
    change SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val = (SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val - r * 0) * 1
    simp only [mul_zero, sub_zero, mul_one]

theorem character_of_components (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →* Circle)
    (hχ : ∀ a : kˣ, χ (Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom a) = 1)
    (a : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (t : kˣ)
    (ha : SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val * t.val = SpecialUnitary.SplitAlgebra.plus r hr hr0 a.val) :
    χ a = χ (splitSection r hr hr0 t) := by
  rw [unit_factorization r hr hr0 a t ha, map_mul, hχ, one_mul]

variable {I : Type} [Fintype I] [DecidableEq I]

def unitaryCharacter (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →* Circle) : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary Q.val →* Circle :=
  χ.comp ((splitSection r hr hr0).comp
    ((Matrix.GeneralLinearGroup.det).comp (SplitUnitary.plusUnitary r hr hr0 Q)))

theorem first_argument_character (hd : d ≠ 0)
    (H : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hH : H.val.conjTranspose = H.val)
    (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →* Circle)
    (hχ : ∀ a : kˣ, χ (Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom a) = 1)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hu : u.val = g.val.val - 1) :
    χ ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ Fintype.card I * Matrix.GeneralLinearGroup.det H *
        Matrix.GeneralLinearGroup.det u) = unitaryCharacter r hr hr0 H χ g := by
  apply character_of_components r hr hr0 χ hχ
  have ht : (Matrix.GeneralLinearGroup.det (SplitUnitary.plusUnitary r hr hr0 H g)).val =
      SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det g.val).val := by
    change (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val).det = SpecialUnitary.SplitAlgebra.plus r hr hr0 g.val.val.det
    exact ((SpecialUnitary.SplitAlgebra.plus r hr hr0).map_det _).symm
  rw [MonoidHom.comp_apply, ht]
  exact GeneralSplitDeterminant.first_argument_components r hr hr0 hd H hH g u hu

theorem second_argument_character
    (K : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hK : K.val.conjTranspose = -K.val)
    (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →* Circle)
    (hχ : ∀ a : kˣ, χ (Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom a) = 1)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hu : u.val = g.val.val - 1) :
    χ (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) =
      unitaryCharacter r hr hr0 K χ g := by
  apply character_of_components r hr hr0 χ hχ
  have ht : (Matrix.GeneralLinearGroup.det (SplitUnitary.plusUnitary r hr hr0 K g)).val =
      SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det g.val).val := by
    change (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val).det = SpecialUnitary.SplitAlgebra.plus r hr hr0 g.val.val.det
    exact ((SpecialUnitary.SplitAlgebra.plus r hr hr0).map_det _).symm
  rw [MonoidHom.comp_apply, ht]
  exact GeneralSplitDeterminant.second_argument_components r hr hr0 K hK g u hu

end

end OAI.RepresentationTheory.Theta.Adelic.GeneralSplitCharacter
