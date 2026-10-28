import Mathlib

/-!
Concrete two-by-two quaternionic Hermitian matrices and the Schur energy
inequality, as used in Section 4 of `sections/energy.tex`. This is the first
noncommutative block size; no abstract determinant properties are postulated.
-/

namespace OAI.LinearAlgebra.Quaternion

/-- The Hermitian matrix `[[a,b],[star b,d]]`, with its real diagonal explicit. -/
structure Hermitian where
  a : ℝ
  b : Quaternion ℝ
  d : ℝ

/-- The real quaternionic Hermitian quadratic form. -/
def quadratic (A : Hermitian) (x y : Quaternion ℝ) : ℝ :=
  A.a * Quaternion.normSq x + 2 * (star x * A.b * y).re +
    A.d * Quaternion.normSq y

def PositiveSemidefinite (A : Hermitian) : Prop :=
  ∀ x y, 0 ≤ quadratic A x y

/-- In size two the Moore determinant is this explicit real polynomial. -/
def determinant (A : Hermitian) : ℝ :=
  A.a * A.d - Quaternion.normSq A.b

/-- The real trace pairing of two quaternionic Hermitian matrices. -/
def pairing (A B : Hermitian) : ℝ :=
  A.a * B.a + 2 * (star A.b * B.b).re + A.d * B.d

/-- The rank-one positive matrix `v v*` for the quaternionic column `(x,y)`. -/
def rankOne (x y : Quaternion ℝ) : Hermitian where
  a := Quaternion.normSq x
  b := x * star y
  d := Quaternion.normSq y

def segment (D B : Hermitian) (t : ℝ) : Hermitian where
  a := t * D.a + (1 - t) * B.a
  b := t • D.b + (1 - t) • B.b
  d := t * D.d + (1 - t) * B.d

/-- The mixed coefficient of the two-dimensional Moore determinant. -/
def mixedDeterminant (D B : Hermitian) : ℝ :=
  D.a * B.d + D.d * B.a - 2 * (star D.b * B.b).re

theorem re_star_mul_comm (x y : Quaternion ℝ) :
    (star x * y).re = (star y * x).re := by
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

theorem re_mul_comm (x y : Quaternion ℝ) : (x * y).re = (y * x).re := by
  simp only [Quaternion.re_mul]
  ring

private theorem cross_identity (b x y : Quaternion ℝ) :
    (star b * x * star y).re = (star x * b * y).re := by
  calc
    _ = (star (star b * x * star y)).re := (Quaternion.re_star _).symm
    _ = (y * (star x * b)).re := by simp only [star_mul, star_star]
    _ = _ := re_mul_comm _ _

theorem rankOne_determinant (x y : Quaternion ℝ) : determinant (rankOne x y) = 0 := by
  simp [determinant, rankOne, map_mul]

theorem rankOne_positiveSemidefinite (u v : Quaternion ℝ) :
    PositiveSemidefinite (rankOne u v) := by
  intro x y
  have hc : (star u * x * star (star v * y)).re =
      (star x * (u * star v) * y).re := by
    calc
      _ = ((star y * v) * (star u * x)).re := by
        rw [star_mul, star_star, re_mul_comm]
      _ = (star ((star y * v) * (star u * x))).re := (Quaternion.re_star _).symm
      _ = _ := by simp only [star_mul, star_star, mul_assoc]
  have hid : quadratic (rankOne u v) x y =
      Quaternion.normSq (star u * x + star v * y) := by
    simp only [quadratic, rankOne, Quaternion.normSq_add, map_mul,
      Quaternion.normSq_star, hc]
    ring
  rw [hid]
  exact Quaternion.normSq_nonneg

/-- Polynomial expansion of the actual quaternionic determinant along a segment. -/
theorem determinant_segment (D B : Hermitian) (t : ℝ) :
    determinant (segment D B t) = t ^ 2 * determinant D +
      t * (1 - t) * mixedDeterminant D B + (1 - t) ^ 2 * determinant B := by
  simp only [determinant, segment, mixedDeterminant, Quaternion.normSq_def',
    Quaternion.re_add, Quaternion.re_smul, Quaternion.imI_add, Quaternion.imI_smul,
    Quaternion.imJ_add, Quaternion.imJ_smul, Quaternion.imK_add, Quaternion.imK_smul,
    Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul]
  ring

/-- Quaternionic rank-one determinant segment formula, with no positivity
assumption on `D` and no commutativity assumption on the quaternion entries. -/
theorem determinant_rankOne_segment (D : Hermitian) (u v : Quaternion ℝ) (t : ℝ) :
    determinant (segment D (rankOne u v) t) = t ^ 2 * determinant D +
      t * (1 - t) * mixedDeterminant D (rankOne u v) := by
  rw [determinant_segment, rankOne_determinant, mul_zero, add_zero]

/-- Completing the square gives the quaternionic Schur complement directly. -/
theorem quadratic_complete_square (Q : Hermitian) (hd : Q.d ≠ 0)
    (x y : Quaternion ℝ) :
    quadratic Q x y =
      (Q.a - Quaternion.normSq Q.b / Q.d) * Quaternion.normSq x +
        Q.d * Quaternion.normSq ((Q.d⁻¹ • star Q.b) * x + y) := by
  simp only [quadratic, Quaternion.normSq_add, map_mul, Quaternion.normSq_smul,
    Quaternion.normSq_star, smul_mul_assoc, Quaternion.re_smul,
    smul_eq_mul, cross_identity]
  field_simp
  ring

/-- Positivity immediately controls the time component of the current. -/
theorem time_nonneg {A : Hermitian} (hA : PositiveSemidefinite A) : 0 ≤ A.a := by
  simpa [quadratic] using hA 1 0

/-- Quaternionic Schur pairing inequality without assuming positivity of the
full Hessian `Q`; only the spatial entry `Q.d` must be positive. -/
theorem schur_pairing_lower_bound {A : Hermitian} (hA : PositiveSemidefinite A)
    (Q : Hermitian) (hQ : 0 < Q.d) :
    A.a * (Q.a - Quaternion.normSq Q.b / Q.d) ≤ pairing A Q := by
  have h := mul_nonneg hQ.le (hA (Q.d⁻¹ • Q.b) 1)
  have hstar : star (Q.d⁻¹ • Q.b) = Q.d⁻¹ • star Q.b := by
    exact Quaternion.star_smul _ _
  have hid : Q.d * quadratic A (Q.d⁻¹ • Q.b) 1 =
      pairing A Q - A.a * (Q.a - Quaternion.normSq Q.b / Q.d) := by
    simp only [quadratic, pairing, Quaternion.normSq_smul, hstar,
      smul_mul_assoc, mul_one, Quaternion.re_smul, map_one, smul_eq_mul,
      re_star_mul_comm Q.b A.b]
    field_simp
    ring
  rw [hid] at h
  exact sub_nonneg.mp h

/-- Exact determinant identity underlying the preceding Schur estimate. -/
theorem determinant_eq_schur (Q : Hermitian) (hQ : Q.d ≠ 0) :
    determinant Q = Q.d * (Q.a - Quaternion.normSq Q.b / Q.d) := by
  unfold determinant
  field_simp

/-- The usual Schur positivity criterion, proved for actual quaternionic
quadratic forms and the explicit two-dimensional Moore determinant. -/
theorem positiveSemidefinite_iff_determinant_nonneg (Q : Hermitian) (hd : 0 < Q.d) :
    PositiveSemidefinite Q ↔ 0 ≤ determinant Q := by
  constructor
  · intro h
    have hc := h 1 (-(Q.d⁻¹ • star Q.b))
    rw [quadratic_complete_square Q hd.ne'] at hc
    simp only [map_one, mul_one, add_neg_cancel, map_zero, mul_zero, add_zero] at hc
    rw [determinant_eq_schur Q hd.ne']
    exact mul_nonneg hd.le hc
  · intro h x y
    have hc : 0 ≤ Q.a - Quaternion.normSq Q.b / Q.d := by
      rw [determinant_eq_schur Q hd.ne'] at h
      exact (mul_nonneg_iff_of_pos_left hd).mp h
    rw [quadratic_complete_square Q hd.ne']
    exact add_nonneg (mul_nonneg hc Quaternion.normSq_nonneg)
      (mul_nonneg hd.le Quaternion.normSq_nonneg)

/-- The determinant-normalized quaternionic energy inequality in size two. -/
theorem schur_energy_inequality {A : Hermitian} (hA : PositiveSemidefinite A)
    (Q : Hermitian) (hQ : 0 < Q.d) {lam : ℝ} (hlam : lam ≠ 0)
    (hfiber : Q.d = lam * A.a) :
    determinant Q / lam ≤ pairing A Q := by
  rw [determinant_eq_schur Q hQ.ne']
  nth_rw 1 [hfiber]
  convert schur_pairing_lower_bound hA Q hQ using 1
  field_simp

end OAI.LinearAlgebra.Quaternion
