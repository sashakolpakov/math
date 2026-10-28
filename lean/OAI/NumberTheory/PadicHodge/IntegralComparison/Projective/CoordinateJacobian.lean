import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorDeterminant
import Mathlib.RingTheory.Derivation.Basic

/-! # Coordinate Jacobian -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoordinateJacobian

noncomputable section

/-! Inverting one affine projective coordinate changes the top
differential by the exact power and sign of the usual canonical twist. -/

universe u v w

variable {R : Type u} [CommRing R]

theorem det_updateRow_one {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) (v : ι → R) :
    (Matrix.updateRow (1 : Matrix ι ι R) k v).det = v k := by
  have hv : (∑ i, v i • (1 : Matrix ι ι R) i) = v := by
    funext j
    simp [Matrix.one_apply]
  simpa only [hv, Matrix.det_one, smul_eq_mul, mul_one] using
    Matrix.det_updateRow_sum (1 : Matrix ι ι R) k v

variable {n : ℕ}

def jacobian (k : Fin n) (u : Rˣ) (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.updateRow (((u⁻¹ : Rˣ) : R) • (1 : Matrix (Fin n) (Fin n) R)) k
    (fun j => if j = k then -((u⁻¹ : Rˣ) : R) ^ 2 else -((u⁻¹ : Rˣ) : R) ^ 2 * x j)

theorem jacobian_det (k : Fin n) (u : Rˣ) (x : Fin n → R) :
    (jacobian k u x).det = -((u⁻¹ : Rˣ) : R) ^ (n + 1) := by
  rw [jacobian, Matrix.det_updateRow_smul_left, det_updateRow_one, ite_eq_left rfl,
    Fintype.card_fin, mul_neg, ← pow_add]
  congr 2
  have := k.isLt
  omega

variable {M : Type v} [AddCommGroup M] [Module R M]
  (b : Module.Basis (Fin n) R M)

def frame (k : Fin n) (u : Rˣ) (x : Fin n → R) (j : Fin n) : M :=
  if j = k then -((u⁻¹ : Rˣ) : R) ^ 2 • b k
  else ((u⁻¹ : Rˣ) : R) • b j - (((u⁻¹ : Rˣ) : R) ^ 2 * x j) • b k

theorem frame_matrix (k : Fin n) (u : Rˣ) (x : Fin n → R) :
    b.toMatrix (frame b k u x) = jacobian k u x := by
  ext i j
  by_cases hi : i = k <;> by_cases hj : j = k
  all_goals simp [Module.Basis.toMatrix_apply, frame, jacobian, Matrix.updateRow_apply,
    Matrix.one_apply, Finsupp.single_apply, hi, hj, eq_comm, sub_eq_add_neg]
  all_goals exact fun h => (hj h.symm).elim

theorem wedge_frame (k : Fin n) (u : Rˣ) (x : Fin n → R) :
    exteriorPower.ιMulti R n (frame b k u x) =
      (-((u⁻¹ : Rˣ) : R) ^ (n + 1)) • exteriorPower.ιMulti R n b := by
  rw [TopExteriorDeterminant.alternating_apply_eq_det_smul b,
    Module.Basis.det_apply, frame_matrix, jacobian_det]

def coordinates (k : Fin n) (u : Rˣ) (x : Fin n → R) (j : Fin n) : R :=
  if j = k then ((u⁻¹ : Rˣ) : R) else ((u⁻¹ : Rˣ) : R) * x j

variable {A : Type w} [CommRing A] [Algebra A R] [Module A M] [IsScalarTower A R M]

omit [IsScalarTower A R M] in
theorem differential_coordinates (D : Derivation A R M) (k : Fin n) (u : Rˣ) (x : Fin n → R)
    (hx : ∀ j, D (x j) = b j) (hk : x k = (u : R)) (j : Fin n) :
    D (coordinates k u x j) = frame b k u x j := by
  have hi : D ((u⁻¹ : Rˣ) : R) = -((u⁻¹ : Rˣ) : R) ^ 2 • b k := by
    rw [D.leibniz_of_mul_eq_one (Units.inv_mul u), ← hk, hx]
  by_cases hj : j = k
  · simp only [coordinates, frame, ite_eq_left hj]
    exact hi
  · simp [coordinates, frame, hj, D.leibniz, hx, hi, sub_eq_add_neg, smul_smul, mul_comm, add_comm]

omit [IsScalarTower A R M] in
theorem wedge_differential_coordinates (D : Derivation A R M) (k : Fin n) (u : Rˣ)
    (x : Fin n → R) (hx : ∀ j, D (x j) = b j) (hk : x k = (u : R)) :
    exteriorPower.ιMulti R n (fun j => D (coordinates k u x j)) =
      (-((u⁻¹ : Rˣ) : R) ^ (n + 1)) • exteriorPower.ιMulti R n b := by
  have he : (fun j => D (coordinates k u x j)) = frame b k u x :=
    funext (differential_coordinates b D k u x hx hk)
  rw [he, wedge_frame]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoordinateJacobian
