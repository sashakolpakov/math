import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction
import OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization

/-! # General Split Determinant -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeneralSplitDeterminant

noncomputable section

/-! Exact determinant identities on both open cells of a split unitary
pair. These identities retain the determinant character for full GL rank. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization.Construction OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction.Coordinates OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction

variable {k : Type} [Field k] [CharZero k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
variable {I : Type} [Fintype I] [DecidableEq I]

theorem det_sub_one_components (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary Q.val) :
    (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 g.val.val - 1).det * (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val).det =
      (-1 : k) ^ Fintype.card I * (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val - 1).det := by
  let A := SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val
  let B := SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 g.val.val
  let P := SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q.val
  have hP : P.det ≠ 0 := (Matrix.GeneralLinearGroup.det (SplitUnitary.plusUnits r hr hr0 Q)).ne_zero
  have hg : B.transpose * P * A = P := GeneralSplitAction.first_equation r hr hr0 Q.val g
  have he : (B - 1).transpose * P * A = -(P * (A - 1)) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, sub_mul, sub_mul, one_mul,
      hg, mul_sub, mul_one]
    abel
  have hdet := congrArg Matrix.det he
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_neg] at hdet
  change (B - 1).det * A.det = (-1) ^ Fintype.card I * (A - 1).det
  apply mul_left_cancel₀ hP
  calc
    _ = (B - 1).det * P.det * A.det := by ring
    _ = (-1) ^ Fintype.card I * (P.det * (A - 1).det) := hdet
    _ = _ := by ring

theorem open_cell_det_components (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary Q.val)
    (u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hu : u.val = g.val.val - 1) :
    SpecialUnitary.SplitAlgebra.minus r hr hr0 (Matrix.GeneralLinearGroup.det u).val *
      SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det g.val).val =
        (-1 : k) ^ Fintype.card I * SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det u).val := by
  change SpecialUnitary.SplitAlgebra.minus r hr hr0 u.val.det * SpecialUnitary.SplitAlgebra.plus r hr hr0 g.val.val.det =
    (-1 : k) ^ Fintype.card I * SpecialUnitary.SplitAlgebra.plus r hr hr0 u.val.det
  rw [(SpecialUnitary.SplitAlgebra.minus r hr hr0).map_det, (SpecialUnitary.SplitAlgebra.plus r hr hr0).map_det, (SpecialUnitary.SplitAlgebra.plus r hr hr0).map_det, hu]
  change (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 (g.val.val - 1)).det * (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val).det =
    (-1 : k) ^ Fintype.card I * (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 (g.val.val - 1)).det
  rw [map_sub, map_one, map_sub, map_one]
  exact det_sub_one_components r hr hr0 Q g

theorem first_argument_components (hd : d ≠ 0)
    (H : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hH : H.val.conjTranspose = H.val)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hu : u.val = g.val.val - 1) :
    SpecialUnitary.SplitAlgebra.minus r hr hr0 ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ Fintype.card I * Matrix.GeneralLinearGroup.det H *
        Matrix.GeneralLinearGroup.det u).val *
      SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det g.val).val =
    SpecialUnitary.SplitAlgebra.plus r hr hr0 ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ Fintype.card I * Matrix.GeneralLinearGroup.det H *
        Matrix.GeneralLinearGroup.det u).val := by
  have hHd : SpecialUnitary.SplitAlgebra.minus r hr hr0 (Matrix.GeneralLinearGroup.det H).val =
      SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det H).val := by
    change SpecialUnitary.SplitAlgebra.minus r hr hr0 H.val.det = SpecialUnitary.SplitAlgebra.plus r hr hr0 H.val.det
    rw [(SpecialUnitary.SplitAlgebra.minus r hr hr0).map_det, (SpecialUnitary.SplitAlgebra.plus r hr hr0).map_det]
    change (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 H.val).det = (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H.val).det
    rw [SplitUnitary.hermitian_minus r hr hr0 H hH, Matrix.det_transpose]
  have hp : SpecialUnitary.SplitAlgebra.plus r hr hr0 (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).val = r := by change 0 + r * 1 = r; ring
  have hm : SpecialUnitary.SplitAlgebra.minus r hr hr0 (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd).val = -r := by change 0 - r * 1 = -r; ring
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hHd, hp, hm]
  rw [mul_assoc, open_cell_det_components r hr hr0 H g u hu]
  have hs : (-1 : k) ^ Fintype.card I * (-1 : k) ^ Fintype.card I = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [neg_eq_neg_one_mul, mul_pow]
  calc
    _ = ((-1 : k) ^ Fintype.card I * (-1 : k) ^ Fintype.card I) *
        (r ^ Fintype.card I * SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det H).val *
          SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det u).val) := by ring
    _ = _ := by rw [hs, one_mul]

theorem second_argument_components
    (K : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hK : K.val.conjTranspose = -K.val)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (u : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hu : u.val = g.val.val - 1) :
    SpecialUnitary.SplitAlgebra.minus r hr hr0 (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u).val *
      SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det g.val).val =
    SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u).val := by
  have hKd : SpecialUnitary.SplitAlgebra.minus r hr hr0 (Matrix.GeneralLinearGroup.det K).val =
      (-1 : k) ^ Fintype.card I * SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det K).val := by
    change SpecialUnitary.SplitAlgebra.minus r hr hr0 K.val.det = (-1 : k) ^ Fintype.card I * SpecialUnitary.SplitAlgebra.plus r hr hr0 K.val.det
    rw [(SpecialUnitary.SplitAlgebra.minus r hr hr0).map_det, (SpecialUnitary.SplitAlgebra.plus r hr hr0).map_det]
    change (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 K.val).det = (-1 : k) ^ Fintype.card I *
      (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 K.val).det
    rw [GeneralSplitAction.Coordinates.skew_minus_matrix r hr hr0 I K.val hK, Matrix.det_neg, Matrix.det_transpose]
  simp only [Units.val_mul, map_mul, hKd]
  rw [mul_assoc, open_cell_det_components r hr hr0 K g u hu]
  have hs : (-1 : k) ^ Fintype.card I * (-1 : k) ^ Fintype.card I = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc
    _ = ((-1 : k) ^ Fintype.card I * (-1 : k) ^ Fintype.card I) *
        (SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det K).val *
          SpecialUnitary.SplitAlgebra.plus r hr hr0 (Matrix.GeneralLinearGroup.det u).val) := by ring
    _ = _ := by rw [hs, one_mul]

end

end OAI.RepresentationTheory.Theta.Adelic.GeneralSplitDeterminant
