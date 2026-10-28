import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Diagonal Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalFrame.CM

noncomputable section

section

/-! ThetaCycle: explicit symplectic frames for the actual diagonal unitary tensor forms. -/

open scoped Classical Kronecker BigOperators
open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction

variable {F : Type*} [Field F] [CharZero F] {n m : ℕ}

def diagonalUnitaryHermitian (d : F) (h : Fin n → F) :
    Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) :=
  Matrix.diagonal (fun j => ⟨h j, 0⟩)

def diagonalUnitarySkew (d : F) (a : Fin m → F) :
    Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) :=
  Matrix.diagonal (fun i => ⟨0, -2 * a i⟩)

def diagonalFrameWeight (d : F) (h : Fin n → F) (a : Fin m → F) (ji : Fin n × Fin m) : F :=
  -2 * d * h ji.1 * a ji.2

theorem diagonal_frame_weight_ne_zero (d : F) (hd : d ≠ 0)
    (h : Fin n → F) (hh : ∀ j, h j ≠ 0) (a : Fin m → F) (ha : ∀ i, a i ≠ 0)
    (ji : Fin n × Fin m) : diagonalFrameWeight d h a ji ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by norm_num)) hd) (hh _)) (ha _)

def diagonalFrameCoordinates (d : F) (hd : d ≠ 0)
    (h : Fin n → F) (hh : ∀ j, h j ≠ 0) (a : Fin m → F) (ha : ∀ i, a i ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m ≃ₗ[F] RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := F) n m where
  toFun x := Sum.elim
    (fun k => diagonalFrameWeight d h a (finProdFinEquiv.symm k) * (x (finProdFinEquiv.symm k)).re)
    (fun k => (x (finProdFinEquiv.symm k)).im)
  invFun v := fun ji =>
    ⟨v (Sum.inl (finProdFinEquiv ji)) / diagonalFrameWeight d h a ji,
      v (Sum.inr (finProdFinEquiv ji))⟩
  left_inv x := by
    funext ji
    change (⟨diagonalFrameWeight d h a (finProdFinEquiv.symm (finProdFinEquiv ji)) *
      (x (finProdFinEquiv.symm (finProdFinEquiv ji))).re / diagonalFrameWeight d h a ji,
      (x (finProdFinEquiv.symm (finProdFinEquiv ji))).im⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) = x ji
    rw [Equiv.symm_apply_apply]
    apply QuadraticAlgebra.ext
    · simp [diagonal_frame_weight_ne_zero d hd h hh a ha ji]
    · rfl
  right_inv v := by
    funext k
    cases k with
    | inl k =>
      change diagonalFrameWeight d h a (finProdFinEquiv.symm k) *
        (v (Sum.inl (finProdFinEquiv (finProdFinEquiv.symm k))) /
          diagonalFrameWeight d h a (finProdFinEquiv.symm k)) = v (Sum.inl k)
      rw [Equiv.apply_symm_apply]
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ _
        (diagonal_frame_weight_ne_zero d hd h hh a ha (finProdFinEquiv.symm k))
    | inr k =>
      change v (Sum.inr (finProdFinEquiv (finProdFinEquiv.symm k))) = v (Sum.inr k)
      rw [Equiv.apply_symm_apply]
  map_add' x y := by
    funext k
    cases k <;> simp [mul_add]
  map_smul' c x := by
    funext k
    cases k <;> simp [smul_eq_mul, mul_left_comm]

omit [CharZero F] in
theorem native_coordinate_pairing (x y : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := F) n m) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m x y =
      ∑ i : Fin (n * m), (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  simp [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing, Matrix.toBilin'_apply, Matrix.J, Fintype.sum_sum_type,
    Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib]
  ring

theorem diagonal_tensor_trace (d : F) (h : Fin n → F) (a : Fin m → F)
    (x y : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d n m (diagonalUnitaryHermitian d h) (diagonalUnitarySkew d a) x y =
      ∑ ji : Fin n × Fin m, diagonalFrameWeight d h a ji *
        ((x ji).re * (y ji).im - (x ji).im * (y ji).re) := by
  simp only [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing, RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, diagonalUnitaryHermitian, diagonalUnitarySkew,
    Matrix.diagonal_kronecker_diagonal, Matrix.mulVec_diagonal, dotProduct, map_sum,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ji _
  simp only [QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, zero_mul, mul_zero, add_zero,
    zero_add, diagonalFrameWeight]
  field_simp
  ring

/-- The frame is built from real and imaginary coordinates, weighted by the
literal diagonal coefficients; no frame existence hypothesis is required. -/
def diagonalUnitaryFrame (d : F) (hd : d ≠ 0)
    (h : Fin n → F) (hh : ∀ j, h j ≠ 0) (a : Fin m → F) (ha : ∀ i, a i ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m (diagonalUnitaryHermitian d h) (diagonalUnitarySkew d a) where
  coordinates := diagonalFrameCoordinates d hd h hh a ha
  preserves x y := by
    rw [native_coordinate_pairing, diagonal_tensor_trace]
    rw [← Equiv.sum_comp finProdFinEquiv]
    apply Finset.sum_congr rfl
    intro ji _
    simp only [diagonalFrameCoordinates, Equiv.symm_apply_apply, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
    ring

/-- The explicit frame commutes with scalar extension, including at split
quadratic places. The coordinate equation is proved on actual vectors. -/
theorem diagonal_frame_baseChange {F' : Type*} [Field F'] [CharZero F']
    (f : F →+* F') (d : F) (hd : d ≠ 0)
    (h : Fin n → F) (hh : ∀ j, h j ≠ 0) (a : Fin m → F) (ha : ∀ i, a i ≠ 0)
    (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) (i : Fin (n * m) ⊕ Fin (n * m)) :
    (diagonalUnitaryFrame (f d) ((map_ne_zero f).mpr hd)
      (fun j => f (h j)) (fun j => (map_ne_zero f).mpr (hh j))
      (fun j => f (a j)) (fun j => (map_ne_zero f).mpr (ha j))).coordinates
        (fun ji => RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f d (x ji)) i =
      f ((diagonalUnitaryFrame d hd h hh a ha).coordinates x i) := by
  cases i with
  | inl i =>
    simp [diagonalUnitaryFrame, diagonalFrameCoordinates,
      diagonalFrameWeight, RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, map_ofNat]
  | inr i => rfl

end

/-! ThetaCycle: genuine invertible matrices for the diagonal Hermitian and skew-Hermitian forms. -/

open scoped Classical
open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction

def diagonalMatrixUnit {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (u : I → Rˣ) : (Matrix I I R)ˣ where
  val := Matrix.diagonal (fun i => (u i).val)
  inv := Matrix.diagonal (fun i => (u i).inv)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    have h : (fun i => (u i).val * (u i).inv) = fun _ => (1 : R) := by
      funext i
      exact (u i).val_inv
    rw [h, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have h : (fun i => (u i).inv * (u i).val) = fun _ => (1 : R) := by
      funext i
      exact (u i).inv_val
    rw [h, Matrix.diagonal_one]

variable {F : Type*} [Field F] [CharZero F] {n m : ℕ}

def quadraticScalarUnit (d r : F) (hr : r ≠ 0) : (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ :=
  Units.map (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)).toMonoidHom (Units.mk0 r hr)

def quadraticImaginaryUnit (d : F) (hd : d ≠ 0) (r : F) (hr : r ≠ 0) : (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ where
  val := ⟨0, r⟩
  inv := ⟨0, (d * r)⁻¹⟩
  val_inv := by
    apply QuadraticAlgebra.ext
    · change 0 * 0 + d * r * (d * r)⁻¹ = 1
      rw [zero_mul, zero_add, mul_inv_cancel₀ (mul_ne_zero hd hr)]
    · simp [QuadraticAlgebra.im_one]
  inv_val := by
    apply QuadraticAlgebra.ext
    · change 0 * 0 + d * (d * r)⁻¹ * r = 1
      rw [zero_mul, zero_add]
      calc
        d * (d * r)⁻¹ * r = (d * r)⁻¹ * (d * r) := by ring
        _ = 1 := inv_mul_cancel₀ (mul_ne_zero hd hr)
    · simp [QuadraticAlgebra.im_one]

def diagonalHermitianUnit (d : F) (h : Fin n → F) (hh : ∀ j, h j ≠ 0) :
    (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ :=
  diagonalMatrixUnit (fun j => quadraticScalarUnit d (h j) (hh j))

def diagonalSkewUnit (d : F) (hd : d ≠ 0) (a : Fin m → F) (ha : ∀ i, a i ≠ 0) :
    (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ :=
  diagonalMatrixUnit (fun i => quadraticImaginaryUnit d hd (-2 * a i)
    (mul_ne_zero (neg_ne_zero.mpr (by norm_num)) (ha i)))

omit [CharZero F] in
theorem diagonal_hermitian_unit_val (d : F) (h : Fin n → F) (hh : ∀ j, h j ≠ 0) :
    (diagonalHermitianUnit d h hh).val = diagonalUnitaryHermitian d h := rfl

theorem diagonal_skew_unit_val (d : F) (hd : d ≠ 0) (a : Fin m → F) (ha : ∀ i, a i ≠ 0) :
    (diagonalSkewUnit d hd a ha).val = diagonalUnitarySkew d a := rfl

omit [CharZero F] in
theorem diagonal_hermitian_conjugateTranspose (d : F) (h : Fin n → F) :
    (diagonalUnitaryHermitian d h).conjTranspose = diagonalUnitaryHermitian d h := by
  unfold diagonalUnitaryHermitian
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  change (⟨h j + 0 * 0, -0⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) = ⟨h j, 0⟩
  simp

omit [CharZero F] in
theorem diagonal_skew_conjugateTranspose (d : F) (a : Fin m → F) :
    (diagonalUnitarySkew d a).conjTranspose = -diagonalUnitarySkew d a := by
  unfold diagonalUnitarySkew
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  congr 1
  funext i
  change (⟨0 + 0 * (-2 * a i), -(-2 * a i)⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) =
    ⟨-0, -(-2 * a i)⟩
  simp

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalFrame.CM
