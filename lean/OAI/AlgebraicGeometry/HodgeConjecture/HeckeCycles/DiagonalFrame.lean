import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Diagonal Frame -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame.CM.Symplectic

/-! Explicit Darboux coordinates for a diagonal Hermitian space tensored
with one skew-Hermitian line over a quadratic algebra. -/

open scoped Classical _root_.Matrix Kronecker
open _root_.Matrix OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction
variable {k : Type*} [Field k] [CharZero k]
  (d c : k) (h : Fin 3 → k)

def hermitian : Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :=
  Matrix.diagonal (fun i => algebraMap k (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) (h i))

def skew : Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :=
  Matrix.diagonal (fun _ => (⟨0, c⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

def scale (i : Fin 3) : k := d * c * h i

def forward (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 1 :=
  Sum.elim (fun i => (x (i, 0)).re) (fun i => scale d c h i * (x (i, 0)).im)

def backward (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 1) : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1 :=
  fun ij => ⟨x (Sum.inl ij.1), x (Sum.inr ij.1) / scale d c h ij.1⟩

omit [CharZero k] in
theorem scale_ne_zero (hd : d ≠ 0) (hc : c ≠ 0) (hh : ∀ i, h i ≠ 0) (i : Fin 3) :
    scale d c h i ≠ 0 := mul_ne_zero (mul_ne_zero hd hc) (hh i)

def coordinates (hd : d ≠ 0) (hc : c ≠ 0) (hh : ∀ i, h i ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1 ≃ₗ[k] RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 1 where
  toFun := forward d c h
  invFun := backward d c h
  left_inv x := by
    funext ij
    apply QuadraticAlgebra.ext
    · change (x (ij.1, 0)).re = (x ij).re
      exact congrArg (fun p => (x p).re) (Prod.ext rfl (Subsingleton.elim _ _))
    · change scale d c h ij.1 * (x (ij.1, 0)).im / scale d c h ij.1 = (x ij).im
      rw [mul_div_cancel_left₀ _ (scale_ne_zero d c h hd hc hh _)]
      exact congrArg (fun p => (x p).im) (Prod.ext rfl (Subsingleton.elim _ _))
  right_inv x := by
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
      change scale d c h i * (x (Sum.inr i) / scale d c h i) = x (Sum.inr i)
      field_simp [scale_ne_zero d c h hd hc hh i]
  map_add' x y := by
    funext i
    cases i <;> simp [forward, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, mul_add]
  map_smul' a x := by
    funext i
    cases i <;> simp [forward, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, mul_left_comm]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame.CM.Symplectic

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame.CM.TracePairing

/-! Verification of the explicit diagonal tensor Darboux frame. -/

open scoped Classical _root_.Matrix Kronecker
open _root_.Matrix OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame.CM.Symplectic
variable {k : Type*} [Field k] [CharZero k]
  (d c : k) (h : Fin 3 → k)

omit [CharZero k] in
theorem standard_pairing (x y : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 1) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1 x y =
      ∑ i : Fin 3, (x (Sum.inl i) * y (Sum.inr i) - y (Sum.inl i) * x (Sum.inr i)) := by
  simp [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing, Matrix.toBilin'_apply, Matrix.J, Fintype.sum_sum_type,
    Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib, mul_comm]
  ring

theorem trace_pairing (x y : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d 3 1 (Symplectic.hermitian d h) (Symplectic.skew d c) x y =
      ∑ i : Fin 3, Symplectic.scale d c h i * ((x (i, 0)).re * (y (i, 0)).im - (y (i, 0)).re * (x (i, 0)).im) := by
  unfold RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing Symplectic.hermitian Symplectic.skew RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue
  rw [Matrix.diagonal_kronecker_diagonal]
  simp only [dotProduct, Matrix.mulVec_diagonal, Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, Symplectic.scale]
  ring

theorem preserves (x y : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1 (Symplectic.forward d c h x) (Symplectic.forward d c h y) =
      RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d 3 1 (Symplectic.hermitian d h) (Symplectic.skew d c) x y := by
  rw [standard_pairing, trace_pairing]
  apply Finset.sum_congr rfl
  intro i _
  change (x (i, 0)).re * (Symplectic.scale d c h i * (y (i, 0)).im) -
    (y (i, 0)).re * (Symplectic.scale d c h i * (x (i, 0)).im) = _
  ring

def frame (hd : d ≠ 0) (hc : c ≠ 0) (hh : ∀ i, h i ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d 3 1 (Symplectic.hermitian d h) (Symplectic.skew d c) where
  coordinates := Symplectic.coordinates d c h hd hc hh
  preserves := TracePairing.preserves d c h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame.CM.TracePairing

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame.CM.BaseChange

/-! The explicit tensor frame commutes with coefficient extension. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame.CM.Symplectic
variable {k l : Type*} [Field k] [Field l]
  (f : k →+* l) (d c : k) (h : Fin 3 → k)

theorem hermitian_map : (Symplectic.hermitian d h).map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f d) =
    Symplectic.hermitian (f d) (fun i => f (h i)) := by
  unfold Symplectic.hermitian
  rw [Matrix.diagonal_map (map_zero (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f d))]
  congr 1
  funext i
  apply QuadraticAlgebra.ext <;> simp [RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange]

theorem skew_map : (Symplectic.skew d c).map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f d) = Symplectic.skew (f d) (f c) := by
  unfold Symplectic.skew
  rw [Matrix.diagonal_map (map_zero (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f d))]
  congr 1
  funext i
  apply QuadraticAlgebra.ext <;> simp [RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange]

theorem forward_map (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1) (i : Fin (3 * 1) ⊕ Fin (3 * 1)) :
    Symplectic.forward (f d) (f c) (fun j => f (h j)) (fun j => RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange f d (x j)) i =
      f (Symplectic.forward d c h x i) := by
  cases i with
  | inl i => rfl
  | inr i =>
    change (f d * f c * f (h i)) * f (x (i, 0)).im = f ((d * c * h i) * (x (i, 0)).im)
    rw [map_mul, map_mul, map_mul]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalFrame.CM.BaseChange

end

end OAI
