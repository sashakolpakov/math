import OAI.RepresentationTheory.Theta.Adelic.SplitTensor

/-! # General Split Action -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.GeneralSplitAction.Coordinates

/-! Root coordinates and the trace pairing for an arbitrary split
quadratic skew-Hermitian space. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.SplitTensor

variable {k : Type} [Field k] [CharZero k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0) (I : Type)

def rootCoordinates : (I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) ≃ₗ[k] (I → k) × (I → k) where
  toFun x := (fun i => SpecialUnitary.SplitAlgebra.plus r hr hr0 (x i), fun i => SpecialUnitary.SplitAlgebra.minus r hr hr0 (x i))
  invFun p := fun i => (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (p.1 i, p.2 i)
  left_inv x := by
    funext i
    exact (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm_apply_apply (x i)
  right_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).apply_symm_apply (p.1 i, p.2 i))
    · funext i
      exact congrArg Prod.snd ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).apply_symm_apply (p.1 i, p.2 i))
  map_add' x y := by
    apply Prod.ext <;> funext i <;> exact map_add _ _ _
  map_smul' c x := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst (map_smul (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).toLinearEquiv c (x i))
    · funext i
      exact congrArg Prod.snd (map_smul (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).toLinearEquiv c (x i))

variable [Fintype I] [DecidableEq I]

theorem skew_minus_matrix (Q : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (hQ : Q.conjTranspose = -Q) :
    SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 Q = -(SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q).transpose := by
  have h := congrArg (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0) hQ
  rw [SplitUnitary.minusMatrix_conjTranspose, map_neg] at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

theorem split_skew_trace (Q : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (hQ : Q.conjTranspose = -Q)
    (x y : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    QuadraticAlgebra.trace (Weil.AdelicSplitting.TensorSpace.Construction.formValue Q x y) / 2 =
      (dotProduct (rootCoordinates r hr hr0 I x).2
          ((SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q).mulVec (rootCoordinates r hr hr0 I y).1) -
        dotProduct (rootCoordinates r hr hr0 I x).1
          ((SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q).transpose.mulVec (rootCoordinates r hr hr0 I y).2)) / 2 := by
  rw [SplitTensor.trace_eq_components r hr hr0, SplitTensor.plus_formValue, SplitTensor.minus_formValue,
    skew_minus_matrix r hr hr0 I Q hQ, Matrix.neg_mulVec, dotProduct_neg, ← sub_eq_add_neg]
  rfl

def negativeHalf : kˣ := Units.mk0 (-1 / 2 : k) (div_ne_zero (neg_ne_zero.mpr one_ne_zero) two_ne_zero)

def momentumUnit (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) : (Matrix I I k)ˣ :=
  Units.map (algebraMap k (Matrix I I k)).toMonoidHom (negativeHalf (k := k)) *
    SplitUnitary.transposeUnit (SplitUnitary.plusUnits r hr hr0 Q)

theorem momentumUnit_mulVec (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (x : I → k) :
    (momentumUnit r hr hr0 I Q).val.mulVec x =
      (-1 / 2 : k) • (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q.val).transpose.mulVec x := by
  change (algebraMap k (Matrix I I k) (-1 / 2) * (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q.val).transpose).mulVec x = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec]

def polarizedCoordinates (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    (I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) ≃ₗ[k] (I → k) × (I → k) :=
  (rootCoordinates r hr hr0 I).trans
    ((LinearEquiv.refl k (I → k)).prodCongr
      (Matrix.GeneralLinearGroup.toLin (momentumUnit r hr hr0 I Q)).toLinearEquiv)

theorem polarizedCoordinates_preserves (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hQ : Q.val.conjTranspose = -Q.val) (x y : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    dotProduct (polarizedCoordinates r hr hr0 I Q x).1 (polarizedCoordinates r hr hr0 I Q y).2 -
      dotProduct (polarizedCoordinates r hr hr0 I Q x).2 (polarizedCoordinates r hr hr0 I Q y).1 =
        QuadraticAlgebra.trace (Weil.AdelicSplitting.TensorSpace.Construction.formValue Q.val x y) / 2 := by
  change dotProduct (rootCoordinates r hr hr0 I x).1
      ((momentumUnit r hr hr0 I Q).val.mulVec (rootCoordinates r hr hr0 I y).2) -
    dotProduct ((momentumUnit r hr hr0 I Q).val.mulVec (rootCoordinates r hr hr0 I x).2)
      (rootCoordinates r hr hr0 I y).1 = _
  rw [momentumUnit_mulVec, momentumUnit_mulVec, split_skew_trace r hr hr0 I Q.val hQ,
    dotProduct_smul, smul_dotProduct, Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  simp only [smul_eq_mul]
  ring

end RepresentationTheory.Theta.Adelic.GeneralSplitAction.Coordinates

namespace RepresentationTheory.Theta.Adelic.GeneralSplitAction

/-! The full unitary group of a split skew-Hermitian space acts by a
linear map and its inverse transpose in the explicit polarization. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction.Coordinates

variable {k : Type} [Field k] [CharZero k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
variable {I : Type} [Fintype I] [DecidableEq I]

theorem first_equation (Q : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary Q) :
    (SplitUnitary.minusUnits r hr hr0 g.val).val.transpose * SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q *
      (SplitUnitary.plusUnits r hr hr0 g.val).val = SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q := by
  change (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 g.val.val).transpose * SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 Q *
    SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val = _
  have h := congrArg (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0) g.property
  simpa only [map_mul, SplitUnitary.plusMatrix_conjTranspose] using h

theorem dual_matrix_relation (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary Q.val) :
    (SplitUnitary.plusUnits r hr hr0 Q).val.transpose * (SplitUnitary.minusUnits r hr hr0 g.val).val =
      ((SplitUnitary.plusUnits r hr hr0 g.val)⁻¹).val.transpose * (SplitUnitary.plusUnits r hr hr0 Q).val.transpose := by
  let A := SplitUnitary.plusUnits r hr hr0 g.val
  let B := SplitUnitary.minusUnits r hr hr0 g.val
  let P := SplitUnitary.plusUnits r hr hr0 Q
  have hfirst : B.val.transpose * P.val * A.val = P.val :=
    first_equation r hr hr0 Q.val g
  have ht : A.val.transpose * P.val.transpose * B.val = P.val.transpose := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, mul_assoc] using
      congrArg Matrix.transpose hfirst
  have hAi : (A⁻¹).val.transpose * A.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  change P.val.transpose * B.val = (A⁻¹).val.transpose * P.val.transpose
  calc
    _ = ((A⁻¹).val.transpose * A.val.transpose) * (P.val.transpose * B.val) := by rw [hAi, one_mul]
    _ = (A⁻¹).val.transpose * (A.val.transpose * P.val.transpose * B.val) := by simp only [mul_assoc]
    _ = _ := by rw [ht]

theorem rootCoordinates_mulVec (A : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (x : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    Coordinates.rootCoordinates r hr hr0 I (A.mulVec x) =
      ((SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 A).mulVec (Coordinates.rootCoordinates r hr hr0 I x).1,
        (SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 A).mulVec (Coordinates.rootCoordinates r hr hr0 I x).2) := by
  apply Prod.ext <;> funext i
  · change SpecialUnitary.SplitAlgebra.plus r hr hr0 (A.mulVec x i) = _
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, SpecialUnitary.SplitAlgebra.plusMatrix, Coordinates.rootCoordinates]
  · change SpecialUnitary.SplitAlgebra.minus r hr hr0 (A.mulVec x i) = _
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, SpecialUnitary.SplitAlgebra.minusMatrix, Coordinates.rootCoordinates]

theorem momentum_intertwines (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary Q.val) (x : I → k) :
    (Coordinates.momentumUnit r hr hr0 I Q).val.mulVec ((SplitUnitary.minusUnits r hr hr0 g.val).val.mulVec x) =
      ((SplitUnitary.plusUnits r hr hr0 g.val)⁻¹).val.transpose.mulVec
        ((Coordinates.momentumUnit r hr hr0 I Q).val.mulVec x) := by
  rw [Coordinates.momentumUnit_mulVec, Coordinates.momentumUnit_mulVec, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun A : Matrix I I k => (-1 / 2 : k) • A.mulVec x)
    (dual_matrix_relation r hr hr0 Q g)

theorem polarizedCoordinates_intertwines (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary Q.val) (x : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    Coordinates.polarizedCoordinates r hr hr0 I Q (g.val.val.mulVec x) =
      ((SplitUnitary.plusUnits r hr hr0 g.val).val.mulVec (Coordinates.polarizedCoordinates r hr hr0 I Q x).1,
        ((SplitUnitary.plusUnits r hr hr0 g.val)⁻¹).val.transpose.mulVec
          (Coordinates.polarizedCoordinates r hr hr0 I Q x).2) := by
  change ((Coordinates.rootCoordinates r hr hr0 I (g.val.val.mulVec x)).1,
      (Coordinates.momentumUnit r hr hr0 I Q).val.mulVec
        (Coordinates.rootCoordinates r hr hr0 I (g.val.val.mulVec x)).2) = _
  rw [rootCoordinates_mulVec]
  apply Prod.ext
  · rfl
  · exact momentum_intertwines r hr hr0 Q g (Coordinates.rootCoordinates r hr hr0 I x).2

end RepresentationTheory.Theta.Adelic.GeneralSplitAction

end

end OAI
