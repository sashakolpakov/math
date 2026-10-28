import OAI.RepresentationTheory.Theta.Adelic.MomentumCoordinates

/-! # Intrinsic Place Matrices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPlaceMatrices.CM

noncomputable section

section

/-! Square matrices for the actual real position and momentum coordinate
maps. The trace pairing proves that the momentum matrix is inverse transpose. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.MomentumCoordinates OAI.RepresentationTheory.Theta.Adelic.MomentumCoordinates.PositionPairing

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

def nativePositionUnflatten : (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℝ) ≃ₗ[ℝ] RepresentationTheory.Theta.Adelic.BallGeometryData.RealPositions A where
  toFun x v j := x (v, finProdFinEquiv.symm j)
  invFun x i := x i.1 (finProdFinEquiv i.2)
  left_inv x := by funext i; simp
  right_inv x := by
    funext v j
    exact congrArg (x v) (finProdFinEquiv.apply_symm_apply j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem native_position_unflatten_pairing (x y : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℝ) :
    (∑ v, ∑ j, nativePositionUnflatten A x v j * nativePositionUnflatten A y v j) =
      ∑ i, x i * y i := by
  calc
    _ = ∑ p : Fin A.places × Fin (3 * m),
        x (p.1, finProdFinEquiv.symm p.2) * y (p.1, finProdFinEquiv.symm p.2) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := Equiv.sum_comp ((Equiv.refl (Fin A.places)).prodCongr finProdFinEquiv.symm)
      (fun i => x i * y i)

def nativePositionMatrix : (Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℝ)ˣ :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((nativePositionUnflatten A).trans (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.realPositionCoordinates A).toLinearEquiv))

def nativeMomentumMatrix : (Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℝ)ˣ :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((nativePositionUnflatten A).trans (RepresentationTheory.Theta.Adelic.MomentumCoordinates.realMomentumCoordinates A).toLinearEquiv))

theorem native_position_matrix_apply (x : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℝ) :
    (nativePositionMatrix A).val.mulVec x = RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.realPositionCoordinates A (nativePositionUnflatten A x) :=
  LinearMap.toMatrix'_mulVec _ x

theorem native_momentum_matrix_apply (x : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℝ) :
    (nativeMomentumMatrix A).val.mulVec x = RepresentationTheory.Theta.Adelic.MomentumCoordinates.realMomentumCoordinates A (nativePositionUnflatten A x) :=
  LinearMap.toMatrix'_mulVec _ x

theorem native_position_momentum_matrix_dual :
    (nativePositionMatrix A).val.transpose * (nativeMomentumMatrix A).val = 1 := by
  apply Matrix.ext
  intro i j
  change (∑ k,
    RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.realPositionCoordinates A (nativePositionUnflatten A (Pi.single i 1)) k *
      RepresentationTheory.Theta.Adelic.MomentumCoordinates.realMomentumCoordinates A (nativePositionUnflatten A (Pi.single j 1)) k) = _
  rw [RepresentationTheory.Theta.Adelic.MomentumCoordinates.PositionPairing.real_position_momentum_pairing, native_position_unflatten_pairing]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem native_momentum_matrix_inverse_transpose :
    (nativeMomentumMatrix A).val = (nativePositionMatrix A).inv.transpose := by
  have hi : (nativePositionMatrix A).inv.transpose * (nativePositionMatrix A).val.transpose = 1 := by
    rw [← Matrix.transpose_mul, (nativePositionMatrix A).val_inv, Matrix.transpose_one]
  exact (left_inv_eq_right_inv hi (native_position_momentum_matrix_dual A)).symm

end

/-! Matrices acting independently at the real places, with the exact
frame-index order and determinant product. -/

open scoped Classical _root_.NumberField
open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

def nativePlaceIndexEquiv : (Fin (3 * m) × Fin A.places) ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A :=
  (Equiv.prodComm _ _).trans ((Equiv.refl (Fin A.places)).prodCongr finProdFinEquiv.symm)

def nativePlaceMatrix {R : Type*} [CommRing R]
    (M : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R) : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) R :=
  Matrix.reindexRingEquiv R (nativePlaceIndexEquiv A) (Matrix.blockDiagonal M)

theorem native_place_matrix_entry {R : Type*} [CommRing R]
    (M : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R)
    (v w : Fin A.places) (a b : Fin 3 × Fin m) :
    nativePlaceMatrix A M (v, a) (w, b) =
      if v = w then M v (finProdFinEquiv a) (finProdFinEquiv b) else 0 := rfl

theorem native_place_matrix_mulVec {R : Type*} [CommRing R]
    (M : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R)
    (x : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → R) (v : Fin A.places) (a : Fin 3 × Fin m) :
    (nativePlaceMatrix A M).mulVec x (v, a) =
      (M v).mulVec (fun j => x (v, finProdFinEquiv.symm j)) (finProdFinEquiv a) := by
  change (∑ i, nativePlaceMatrix A M (v, a) i * x i) = _
  simp only [Fintype.sum_prod_type, native_place_matrix_entry, ite_mul, zero_mul]
  rw [Finset.sum_eq_single v]
  · simpa only [Fintype.sum_prod_type, Equiv.symm_apply_apply, ite_true, Matrix.mulVec, dotProduct] using
      (Equiv.sum_comp finProdFinEquiv
      (fun j => M v (finProdFinEquiv a) j * x (v, finProdFinEquiv.symm j)))
  · intro w _ hw
    simp [Ne.symm hw]
  · simp

theorem native_place_matrix_det {R : Type*} [CommRing R]
    (M : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R) :
    (nativePlaceMatrix A M).det = ∏ v, (M v).det := by
  change (Matrix.reindex (nativePlaceIndexEquiv A) (nativePlaceIndexEquiv A) (Matrix.blockDiagonal M)).det = _
  rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPlaceMatrices.CM
