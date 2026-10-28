import Mathlib

/-! # Determinant Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

noncomputable section

/-! Concrete automorphy factors for L ⊕ (V/L)* in rank three. The
annihilator determinant is calculated from the actual inverse-transpose
matrix, so the square-root identity is an equality of coordinate factors. -/

open _root_.Matrix
open scoped _root_.Matrix

variable {k : Type*} [Field k]

def lineVector (z : Fin 2 → k) : Fin 3 → k := ![z 0, z 1, 1]

def annihilatorVector (z : Fin 2 → k) (i : Fin 2) : Fin 3 → k :=
  if i = 0 then ![1, 0, -z 0] else ![0, 1, -z 1]

def denominator (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k) : k :=
  g.val.mulVec (lineVector z) 2

def chartImage (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k) : Fin 2 → k :=
  fun i => g.val.mulVec (lineVector z) i.castSucc / denominator g z

def dualColumn (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k) (j : Fin 2) : Fin 3 → k :=
  (g⁻¹).val.transpose.mulVec (annihilatorVector z j)

def dualCoordinates (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k) : Matrix (Fin 2) (Fin 2) k :=
  fun i j => dualColumn g z j i.castSucc

theorem cross_mulVec (A : Matrix (Fin 3) (Fin 3) k) (x y : Fin 3 → k) :
    (A.mulVec x) ⨯₃ (A.mulVec y) = A.adjugate.transpose.mulVec (x ⨯₃ y) := by
  funext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.adjugate_fin_three] <;> ring

theorem annihilator_cross (z : Fin 2 → k) :
    annihilatorVector z 0 ⨯₃ annihilatorVector z 1 = lineVector z := by
  simp [annihilatorVector, cross_apply, lineVector]

theorem adjugate_inverseTranspose (g : Matrix.SpecialLinearGroup (Fin 3) k) :
    ((g⁻¹).val.transpose).adjugate.transpose = g.val := by
  change (g.val.adjugate.transpose).adjugate.transpose = g.val
  rw [← Matrix.adjugate_transpose, Matrix.transpose_transpose, Matrix.adjugate_adjugate']
  simp [g.property]

/-- The actual determinant on the rank-two annihilator frame is the same
projective denominator as the factor on the tautological line. -/
theorem dualCoordinates_det (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k) :
    (dualCoordinates g z).det = denominator g z := by
  have h := congrFun (cross_mulVec (g⁻¹).val.transpose (annihilatorVector z 0) (annihilatorVector z 1)) 2
  rw [adjugate_inverseTranspose, annihilator_cross] at h
  calc
    (dualCoordinates g z).det = ((dualColumn g z 0) ⨯₃ (dualColumn g z 1)) 2 := by
      simp [Matrix.det_fin_two, dualCoordinates, cross_apply]
      ring
    _ = denominator g z := h

theorem lineVector_chartImage (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k)
    (hd : denominator g z ≠ 0) :
    g.val.mulVec (lineVector z) = denominator g z • lineVector (chartImage g z) := by
  funext i
  fin_cases i
  · change g.val.mulVec (lineVector z) 0 = denominator g z * (g.val.mulVec (lineVector z) 0 / denominator g z)
    field_simp
  · change g.val.mulVec (lineVector z) 1 = denominator g z * (g.val.mulVec (lineVector z) 1 / denominator g z)
    field_simp
  · change g.val.mulVec (lineVector z) 2 = denominator g z * 1
    rw [mul_one]
    rfl

theorem denominator_mul (g h : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k)
    (hh : denominator h z ≠ 0) :
    denominator (g * h) z = denominator g (chartImage h z) * denominator h z := by
  change (g.val * h.val).mulVec (lineVector z) 2 = _
  rw [← Matrix.mulVec_mulVec, lineVector_chartImage h z hh, Matrix.mulVec_smul]
  change denominator h z * denominator g (chartImage h z) = _
  exact mul_comm _ _

@[simp] theorem denominator_one (z : Fin 2 → k) : denominator 1 z = 1 := by
  simp [denominator, lineVector]

@[simp] theorem chartImage_one (z : Fin 2 → k) : chartImage 1 z = z := by
  funext i
  fin_cases i <;> simp [chartImage, lineVector]

theorem chartImage_mul (g h : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k)
    (hh : denominator h z ≠ 0) : chartImage (g * h) z = chartImage g (chartImage h z) := by
  funext i
  change ((g.val * h.val).mulVec (lineVector z) i.castSucc) / denominator (g * h) z = _
  rw [← Matrix.mulVec_mulVec, lineVector_chartImage h z hh, Matrix.mulVec_smul,
    Pi.smul_apply, smul_eq_mul, denominator_mul g h z hh,
    mul_comm (denominator g (chartImage h z)) (denominator h z)]
  exact mul_div_mul_left _ _ hh

/-- Determinant of the block action on L ⊕ Ann(L). -/
def hodgeDeterminantFactor (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k) : k :=
  denominator g z * (dualCoordinates g z).det

theorem hodgeDeterminantFactor_eq (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k) :
    hodgeDeterminantFactor g z = denominator g z ^ 2 := by
  rw [hodgeDeterminantFactor, dualCoordinates_det, pow_two]

/-- For m multiplicity lines the tautological factor to the power m is
an explicit square root of the determinant factor. -/
theorem natural_halfDeterminant_sq (m : ℕ) (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k) :
    (denominator g z ^ m) ^ 2 = hodgeDeterminantFactor g z ^ m := by
  rw [hodgeDeterminantFactor_eq, ← pow_mul, ← pow_mul, Nat.mul_comm m 2]

end

end OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
