import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace
import OAI.RepresentationTheory.Weil.Local.Generators

/-! # Split Tensor -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.SplitTensor

/-! The two root components of the actual trace tensor space at a split
place. These coordinates expose the standard representation and its dual. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
open _root_.Matrix
open scoped Kronecker

variable {k : Type*} [Field k] [CharZero k] {d : k}
    (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)

def rootTensorCoordinates : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1 ≃ₗ[k]
    (Fin 3 → k) × (Fin 3 → k) where
  toFun x := (fun i => SpecialUnitary.SplitAlgebra.plus r hr hr0 (x (i, 0)), fun i => SpecialUnitary.SplitAlgebra.minus r hr hr0 (x (i, 0)))
  invFun p := fun ij => (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (p.1 ij.1, p.2 ij.1)
  left_inv x := by
    funext ⟨i, j⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm_apply_apply (x (i, 0))
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
      exact congrArg Prod.fst (map_smul (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).toLinearEquiv c (x (i, 0)))
    · funext i
      exact congrArg Prod.snd (map_smul (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).toLinearEquiv c (x (i, 0)))

theorem trace_eq_components (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    QuadraticAlgebra.trace z = SpecialUnitary.SplitAlgebra.plus r hr hr0 z + SpecialUnitary.SplitAlgebra.minus r hr hr0 z := by
  change 2 * z.re + 0 * z.im = (z.re + r * z.im) + (z.re - r * z.im)
  ring

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem plus_formValue (H : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (x y : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    SpecialUnitary.SplitAlgebra.plus r hr hr0 (Weil.AdelicSplitting.TensorSpace.Construction.formValue H x y) =
      dotProduct (fun i => SpecialUnitary.SplitAlgebra.minus r hr hr0 (x i))
        ((SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H).mulVec (fun i => SpecialUnitary.SplitAlgebra.plus r hr hr0 (y i))) := by
  simp only [Weil.AdelicSplitting.TensorSpace.Construction.formValue, dotProduct, Matrix.mulVec, map_sum, map_mul, SpecialUnitary.SplitAlgebra.plus_star]
  rfl

theorem minus_formValue (H : Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (x y : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    SpecialUnitary.SplitAlgebra.minus r hr hr0 (Weil.AdelicSplitting.TensorSpace.Construction.formValue H x y) =
      dotProduct (fun i => SpecialUnitary.SplitAlgebra.plus r hr hr0 (x i))
        ((SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 H).mulVec (fun i => SpecialUnitary.SplitAlgebra.minus r hr hr0 (y i))) := by
  simp only [Weil.AdelicSplitting.TensorSpace.Construction.formValue, dotProduct, Matrix.mulVec, map_sum, map_mul, SpecialUnitary.SplitAlgebra.minus_star]
  rfl

variable (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (K : Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

theorem traceTensor_pairing (x y : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) :
    Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d 3 1 H K x y =
      (SpecialUnitary.SplitAlgebra.plus r hr hr0 (K 0 0) * dotProduct (rootTensorCoordinates r hr hr0 x).2
          ((SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H).mulVec (rootTensorCoordinates r hr hr0 y).1) +
        SpecialUnitary.SplitAlgebra.minus r hr hr0 (K 0 0) * dotProduct (rootTensorCoordinates r hr hr0 x).1
          ((SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 H).mulVec (rootTensorCoordinates r hr hr0 y).2)) / 2 := by
  rw [Weil.AdelicSplitting.TensorSpace.Construction.tracePairing, trace_eq_components r hr hr0, plus_formValue, minus_formValue]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_one,
    SpecialUnitary.SplitAlgebra.plusMatrix, SpecialUnitary.SplitAlgebra.minusMatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.kronecker_apply, map_mul, rootTensorCoordinates, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals apply Finset.sum_congr rfl; intro j _; ring

end RepresentationTheory.Theta.Adelic.SplitTensor

namespace RepresentationTheory.Theta.Adelic.SplitTensor.Frame

/-! An explicit symplectic frame for a rank-three Hermitian space with one
skew-Hermitian multiplicity line at a split place. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction OAI.RepresentationTheory.Weil.Local.Generators.Construction
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.SplitTensor
open _root_.Matrix

variable {k : Type*} [Field k] [CharZero k] {d : k}
    (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)

def momentumScale : kˣ :=
  -(Matrix.GeneralLinearGroup.det (SplitUnitary.plusUnits r hr hr0 K)) / Units.mk0 (2 : k) (by norm_num)

theorem momentumScale_val :
    (momentumScale r hr hr0 K).val = -(SpecialUnitary.SplitAlgebra.plus r hr hr0 (K.val 0 0)) / 2 := by
  simp only [momentumScale, Units.val_div_eq_div_val, Units.val_neg, Units.val_mk0]
  change -(SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 K.val).det / 2 = _
  rw [Matrix.det_fin_one]
  rfl

def momentumUnit : (Matrix (Fin 3) (Fin 3) k)ˣ :=
  Units.map (algebraMap k (Matrix (Fin 3) (Fin 3) k)).toMonoidHom (momentumScale r hr hr0 K) *
    SplitUnitary.transposeUnit (SplitUnitary.plusUnits r hr hr0 H)

theorem momentumUnit_mulVec (x : Fin 3 → k) :
    (momentumUnit r hr hr0 H K).val.mulVec x =
      (momentumScale r hr hr0 K).val • (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H.val).transpose.mulVec x := by
  change (algebraMap k (Matrix (Fin 3) (Fin 3) k) (momentumScale r hr hr0 K).val *
    (SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 H.val).transpose).mulVec x = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec]

def phaseCoordinates : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1 ≃ₗ[k] Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 1 :=
  (rootTensorCoordinates r hr hr0).trans
    (((LinearEquiv.refl k (Fin 3 → k)).prodCongr
      (Matrix.GeneralLinearGroup.toLin (momentumUnit r hr hr0 H K)).toLinearEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 3) k k).symm)

theorem phaseCoordinates_apply (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) :
    phaseCoordinates r hr hr0 H K x =
      Sum.elim (rootTensorCoordinates r hr hr0 x).1
        ((momentumUnit r hr hr0 H K).val.mulVec (rootTensorCoordinates r hr hr0 x).2) := rfl

omit [CharZero k] in
theorem coordinatePairing_sumElim (q p q' p' : Fin 3 → k) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1 (Sum.elim q p) (Sum.elim q' p') = dotProduct q p' - dotProduct p q' := by
  simp [Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing, Matrix.J, Matrix.toBilin'_apply, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
  ring

theorem skew_line_minus (hK : K.val.conjTranspose = -K.val) :
    SpecialUnitary.SplitAlgebra.minus r hr hr0 (K.val 0 0) = -SpecialUnitary.SplitAlgebra.plus r hr hr0 (K.val 0 0) := by
  have h := congrArg (fun A => SpecialUnitary.SplitAlgebra.minusMatrix r hr hr0 A 0 0) hK
  rw [SplitUnitary.minusMatrix_conjTranspose, map_neg] at h
  change SpecialUnitary.SplitAlgebra.plus r hr hr0 (K.val 0 0) = -SpecialUnitary.SplitAlgebra.minus r hr hr0 (K.val 0 0) at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

theorem phaseCoordinates_preserves
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (x y : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1 (phaseCoordinates r hr hr0 H K x) (phaseCoordinates r hr hr0 H K y) =
      Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d 3 1 H.val K.val x y := by
  rw [phaseCoordinates_apply, phaseCoordinates_apply, coordinatePairing_sumElim,
    momentumUnit_mulVec, momentumUnit_mulVec, traceTensor_pairing r hr hr0,
    SplitUnitary.hermitian_minus r hr hr0 H hH, skew_line_minus r hr hr0 K hK,
    dotProduct_smul, smul_dotProduct, Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    momentumScale_val]
  simp only [smul_eq_mul]
  ring

def splitFrame (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d 3 1 H.val K.val where
  coordinates := phaseCoordinates r hr hr0 H K
  preserves := phaseCoordinates_preserves r hr hr0 H K hH hK

end RepresentationTheory.Theta.Adelic.SplitTensor.Frame

namespace RepresentationTheory.Theta.Adelic.SplitTensor.Action

/-! The explicit split symplectic frame sends the unitary first-factor
action to the standard/dual Levi action. -/

open scoped Kronecker

open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction OAI.RepresentationTheory.Weil.Local.Generators.Construction
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
open OAI.RepresentationTheory.Theta.Adelic.SplitTensor OAI.RepresentationTheory.Theta.Adelic.SplitTensor.Frame
open _root_.Matrix

variable {k : Type} [NormedField k] [CharZero k] {d : k}
    (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)

omit [CharZero k] in
theorem tensor_firstFactor_apply (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) (i : Fin 3) :
    Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H.val K.val (g, 1) x (i, 0) = ∑ j, g.val.val i j * x (j, 0) := by
  change (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits g.val (1 : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)).val.mulVec x (i, 0) = _
  simp [Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem rootTensor_firstFactor (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) :
    rootTensorCoordinates r hr hr0 (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H.val K.val (g, 1) x) =
      ((SplitUnitary.plusUnits r hr hr0 g.val).val.mulVec (rootTensorCoordinates r hr hr0 x).1,
        (SplitUnitary.minusUnits r hr hr0 g.val).val.mulVec (rootTensorCoordinates r hr hr0 x).2) := by
  apply Prod.ext
  · funext i
    change SpecialUnitary.SplitAlgebra.plus r hr hr0 (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H.val K.val (g, 1) x (i, 0)) = _
    rw [tensor_firstFactor_apply, map_sum]
    simp [SplitUnitary.plusUnits, SpecialUnitary.SplitAlgebra.plusMatrix, Matrix.mulVec, dotProduct, rootTensorCoordinates, map_mul]
  · funext i
    change SpecialUnitary.SplitAlgebra.minus r hr hr0 (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H.val K.val (g, 1) x (i, 0)) = _
    rw [tensor_firstFactor_apply, map_sum]
    simp [SplitUnitary.minusUnits, SpecialUnitary.SplitAlgebra.minusMatrix, Matrix.mulVec, dotProduct, rootTensorCoordinates, map_mul]

theorem dual_matrix_relation (hH : H.val.conjTranspose = H.val) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) :
    (SplitUnitary.plusUnits r hr hr0 H).val.transpose * (SplitUnitary.minusUnits r hr hr0 g.val).val =
      ((SplitUnitary.plusUnits r hr hr0 g.val)⁻¹).val.transpose * (SplitUnitary.plusUnits r hr hr0 H).val.transpose := by
  let A := SplitUnitary.plusUnits r hr hr0 g.val
  let B := SplitUnitary.minusUnits r hr hr0 g.val
  let P := SplitUnitary.plusUnits r hr hr0 H
  have hfirst : B.val.transpose * P.val * A.val = P.val :=
    (SplitUnitary.unitary_iff_first_equation r hr hr0 H hH g.val).mp g.property
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

theorem momentum_intertwines (hH : H.val.conjTranspose = H.val)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (x : Fin 3 → k) :
    (Frame.momentumUnit r hr hr0 H K).val.mulVec ((SplitUnitary.minusUnits r hr hr0 g.val).val.mulVec x) =
      ((SplitUnitary.plusUnits r hr hr0 g.val)⁻¹).val.transpose.mulVec ((Frame.momentumUnit r hr hr0 H K).val.mulVec x) := by
  rw [Frame.momentumUnit_mulVec, Frame.momentumUnit_mulVec, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun A : Matrix (Fin 3) (Fin 3) k =>
    (Frame.momentumScale r hr hr0 K).val • A.mulVec x) (dual_matrix_relation r hr hr0 H hH g)

omit [CharZero k] in
theorem levi_sumElim (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k 3) (q p : Fin 3 → k) :
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic A) (Sum.elim q p) =
      Sum.elim (A.val.mulVec q) ((A⁻¹).val.transpose.mulVec p) := by
  funext i
  cases i <;> simp [Weil.Local.FunctionsMetaplectic.Construction.symplecticAction, Weil.Local.Generators.Construction.leviSymplectic, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks]

theorem phaseCoordinates_intertwines (hH : H.val.conjTranspose = H.val)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) :
    Frame.phaseCoordinates r hr hr0 H K (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H.val K.val (g, 1) x) =
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic (SplitUnitary.plusUnitary r hr hr0 H g)) (Frame.phaseCoordinates r hr hr0 H K x) := by
  rw [Frame.phaseCoordinates_apply, rootTensor_firstFactor, Frame.phaseCoordinates_apply,
    momentum_intertwines r hr hr0 H K hH, levi_sumElim]
  rfl

theorem splitFrame_action (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) :
    Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val (Frame.splitFrame r hr hr0 H K hH hK) (g, 1) =
      Weil.Local.Generators.Construction.leviSymplectic (SplitUnitary.plusUnitary r hr hr0 H g) := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change Matrix.toLin' (LinearMap.toMatrix'
    (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H.val K.val (Frame.splitFrame r hr hr0 H K hH hK) (g, 1)).toLinearMap) x = _
  rw [Matrix.toLin'_toMatrix']
  change Frame.phaseCoordinates r hr hr0 H K
      (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H.val K.val (g, 1) ((Frame.phaseCoordinates r hr hr0 H K).symm x)) = _
  rw [phaseCoordinates_intertwines r hr hr0 H K hH, LinearEquiv.apply_symm_apply]
  rfl

end RepresentationTheory.Theta.Adelic.SplitTensor.Action

end

end OAI
