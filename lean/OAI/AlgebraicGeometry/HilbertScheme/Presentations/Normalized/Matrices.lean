import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Matrices -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Matrices.Grassmannian

noncomputable section

/-!
Quotient matrices with selected columns equal to the identity. Changing the
selected columns is multiplication by the inverse pivot matrix. These
formulas, their domains, and their cocycles commute with arbitrary ring maps.
-/

universe u v w z

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
variable {ι : Type w} {ν : Type z} [Fintype ι] [DecidableEq ι]

def selectedColumns (a : ι → ν) (Q : Matrix ι ν R) : Matrix ι ι R :=
  Q.submatrix id a

def IsNormalized (a : ι → ν) (Q : Matrix ι ν R) : Prop :=
  selectedColumns a Q = 1

def normalizeColumns (a : ι → ν) (Q : Matrix ι ν R) : Matrix ι ν R :=
  (selectedColumns a Q)⁻¹ * Q

omit [DecidableEq ι] in
theorem selectedColumns_mul (a : ι → ν) (B : Matrix ι ι R) (Q : Matrix ι ν R) :
    selectedColumns a (B * Q) = B * selectedColumns a Q := rfl

theorem normalizeColumns_normalized (a : ι → ν) (Q : Matrix ι ν R)
    (h : IsUnit (selectedColumns a Q).det) : IsNormalized a (normalizeColumns a Q) :=
  Matrix.nonsing_inv_mul _ h

theorem normalizeColumns_of_normalized (a : ι → ν) (Q : Matrix ι ν R)
    (h : IsNormalized a Q) : normalizeColumns a Q = Q := by
  dsimp [normalizeColumns]
  rw [h, inv_one, Matrix.one_mul]

theorem selectedColumns_normalize (a b : ι → ν) (Q : Matrix ι ν R) :
    selectedColumns a (normalizeColumns b Q) =
      (selectedColumns b Q)⁻¹ * selectedColumns a Q := rfl

theorem normalizeColumns_pivot_isUnit_iff (a b : ι → ν) (Q : Matrix ι ν R)
    (hb : IsUnit (selectedColumns b Q).det) :
    IsUnit (selectedColumns a (normalizeColumns b Q)).det ↔
      IsUnit (selectedColumns a Q).det := by
  rw [selectedColumns_normalize, Matrix.det_mul]
  exact IsUnit.mul_iff.trans (and_iff_right (Matrix.isUnit_nonsing_inv_det_iff.mpr hb))

theorem normalizeColumns_inverse (a b : ι → ν) (Q : Matrix ι ν R)
    (ha : IsNormalized a Q) (hb : IsUnit (selectedColumns b Q).det) :
    normalizeColumns a (normalizeColumns b Q) = Q := by
  unfold normalizeColumns
  rw [selectedColumns_mul, ha, Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ hb,
    Matrix.mul_nonsing_inv_cancel_left _ _ hb]

theorem normalizeColumns_cocycle (a b : ι → ν) (Q : Matrix ι ν R)
    (ha : IsUnit (selectedColumns a Q).det) (hb : IsUnit (selectedColumns b Q).det) :
    normalizeColumns a (normalizeColumns b Q) = normalizeColumns a Q := by
  have hi : ((selectedColumns b Q)⁻¹ * selectedColumns a Q)⁻¹ =
      (selectedColumns a Q)⁻¹ * selectedColumns b Q := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (selectedColumns b Q),
      Matrix.mul_nonsing_inv _ hb, Matrix.one_mul, Matrix.nonsing_inv_mul _ ha]
  unfold normalizeColumns
  rw [selectedColumns_mul, hi, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hb]

omit [Fintype ι] [DecidableEq ι] in
theorem selectedColumns_map (φ : R →+* S) (a : ι → ν) (Q : Matrix ι ν R) :
    selectedColumns a (Q.map φ) = (selectedColumns a Q).map φ := rfl

omit [Fintype ι] in
theorem IsNormalized.map {a : ι → ν} {Q : Matrix ι ν R}
    (h : IsNormalized a Q) (φ : R →+* S) : IsNormalized a (Q.map φ) := by
  change (selectedColumns a Q).map φ = 1
  rw [h, Matrix.map_one φ (map_zero φ) (map_one φ)]

theorem matrix_inverse_map (φ : R →+* S) (B : Matrix ι ι R)
    (h : IsUnit B.det) : (B⁻¹).map φ = (B.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h,
    Matrix.map_one φ (map_zero φ) (map_one φ)]

theorem normalizeColumns_map (φ : R →+* S) (a : ι → ν) (Q : Matrix ι ν R)
    (h : IsUnit (selectedColumns a Q).det) :
    normalizeColumns a (Q.map φ) = (normalizeColumns a Q).map φ := by
  unfold normalizeColumns
  rw [selectedColumns_map, ← matrix_inverse_map φ _ h, Matrix.map_mul]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Matrices.Grassmannian
