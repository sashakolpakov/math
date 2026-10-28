import OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

/-! # Unitary Frame Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryFrameAction

noncomputable section

section

/-! The determinant on the native weighted line-annihilator frame.
The rank-two factor is computed from the actual conjugate matrix. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
open scoped _root_.Matrix

variable {k : Type*} [Field k]

def diagonalForm (b : k) : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal ![1, 1, b]

def weightedAnnihilator (b : k) (z : Fin 2 → k) (j : Fin 2) : Fin 3 → k :=
  if j = 0 then ![1, 0, -z 0 / b] else ![0, 1, -z 1 / b]

theorem weightedAnnihilator_cross (b : k) (hb : b ≠ 0) (z : Fin 2 → k) :
    weightedAnnihilator b z 0 ⨯₃ weightedAnnihilator b z 1 =
      b⁻¹ • ((diagonalForm b).mulVec (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z)) := by
  funext i
  fin_cases i <;>
    simp [weightedAnnihilator, cross_apply, diagonalForm, Matrix.mulVec_diagonal,
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, div_eq_mul_inv, hb, mul_comm]

theorem inverseTranspose_cross_form (b : k) (A B : Matrix.SpecialLinearGroup (Fin 3) k)
    (hAB : A.val.transpose * diagonalForm b * B.val = diagonalForm b) :
    (B⁻¹).val.transpose * diagonalForm b = diagonalForm b * A.val := by
  have hs : (diagonalForm b).transpose = diagonalForm b := Matrix.diagonal_transpose _
  have ht := congrArg Matrix.transpose hAB
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs] at ht
  have hi : (B⁻¹).val.transpose * B.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have h := congrArg (fun M => (B⁻¹).val.transpose * M) ht
  simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul] using h.symm

def weightedDualCoordinates (b : k) (B : Matrix.SpecialLinearGroup (Fin 3) k)
    (z : Fin 2 → k) : Matrix (Fin 2) (Fin 2) k :=
  fun i j => (B.val.mulVec (weightedAnnihilator b z j)) i.castSucc

theorem weightedDualCoordinates_det (b : k) (hb : b ≠ 0)
    (A B : Matrix.SpecialLinearGroup (Fin 3) k)
    (hAB : A.val.transpose * diagonalForm b * B.val = diagonalForm b)
    (z : Fin 2 → k) :
    (weightedDualCoordinates b B z).det = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z := by
  have h := congrFun (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.cross_mulVec B.val (weightedAnnihilator b z 0)
    (weightedAnnihilator b z 1)) 2
  rw [weightedAnnihilator_cross b hb z, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at h
  change _ = (b⁻¹ • (((B⁻¹).val.transpose * diagonalForm b).mulVec (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z))) 2 at h
  rw [inverseTranspose_cross_form b A B hAB, ← Matrix.mulVec_mulVec] at h
  have h' : (B.val.mulVec (weightedAnnihilator b z 0) ⨯₃
      B.val.mulVec (weightedAnnihilator b z 1)) 2 = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z := by
    have heval : ((diagonalForm b).mulVec (A.val.mulVec (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z))) 2 =
        b * (A.val.mulVec (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z)) 2 := Matrix.mulVec_diagonal _ _ 2
    change _ = b⁻¹ * ((diagonalForm b).mulVec (A.val.mulVec (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z))) 2 at h
    rw [heval, ← mul_assoc, inv_mul_cancel₀ hb, one_mul] at h
    exact h
  calc
    (weightedDualCoordinates b B z).det =
        (B.val.mulVec (weightedAnnihilator b z 0) ⨯₃
          B.val.mulVec (weightedAnnihilator b z 1)) 2 := by
      simp [weightedDualCoordinates, Matrix.det_fin_two, cross_apply]
      ring
    _ = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z := h'

def activeFrameMatrix (b : k) (A B : Matrix.SpecialLinearGroup (Fin 3) k)
    (z : Fin 2 → k) : Matrix (Fin 3) (Fin 3) k :=
  !![RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z, 0, 0;
    0, weightedDualCoordinates b B z 0 0, weightedDualCoordinates b B z 0 1;
    0, weightedDualCoordinates b B z 1 0, weightedDualCoordinates b B z 1 1]

theorem activeFrameMatrix_det (b : k) (hb : b ≠ 0)
    (A B : Matrix.SpecialLinearGroup (Fin 3) k)
    (hAB : A.val.transpose * diagonalForm b * B.val = diagonalForm b)
    (z : Fin 2 → k) :
    (activeFrameMatrix b A B z).det = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z ^ 2 := by
  have h : (activeFrameMatrix b A B z).det =
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z * (weightedDualCoordinates b B z).det := by
    simp [activeFrameMatrix, Matrix.det_fin_three, Matrix.det_fin_two]
    ring
  rw [h, weightedDualCoordinates_det b hb A B hAB, pow_two]

end

/-! The actual rank-three matrices transport the weighted line and its
annihilator to the new projective point, with the calculated frame matrix. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
open scoped _root_.Matrix

variable {k : Type*} [Field k]

theorem weighted_pairing_preserved (b : k) (A B : Matrix.SpecialLinearGroup (Fin 3) k)
    (hAB : A.val.transpose * diagonalForm b * B.val = diagonalForm b)
    (u w : Fin 3 → k) :
    A.val.mulVec u ⬝ᵥ (diagonalForm b).mulVec (B.val.mulVec w) =
      u ⬝ᵥ (diagonalForm b).mulVec w := by
  calc
    _ = u ⬝ᵥ A.val.transpose.mulVec ((diagonalForm b).mulVec (B.val.mulVec w)) := by
      rw [dotProduct_transpose_mulVec, dotProduct_comm]
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAB]

theorem weightedAnnihilator_orthogonal (b : k) (hb : b ≠ 0)
    (z : Fin 2 → k) (j : Fin 2) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z ⬝ᵥ (diagonalForm b).mulVec (weightedAnnihilator b z j) = 0 := by
  fin_cases j <;>
    simp [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, diagonalForm, Matrix.mulVec_diagonal, weightedAnnihilator,
      dotProduct, Fin.sum_univ_succ] <;> field_simp <;> ring

theorem weightedAnnihilator_reconstruct (b : k) (hb : b ≠ 0)
    (z : Fin 2 → k) (w : Fin 3 → k)
    (hw : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z ⬝ᵥ (diagonalForm b).mulVec w = 0) :
    w = w 0 • weightedAnnihilator b z 0 + w 1 • weightedAnnihilator b z 1 := by
  have he : z 0 * w 0 + z 1 * w 1 + b * w 2 = 0 := by
    simpa [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, diagonalForm, Matrix.mulVec_diagonal, dotProduct,
      Fin.sum_univ_succ, add_assoc] using hw
  funext i
  fin_cases i <;> simp [weightedAnnihilator]
  field_simp
  linear_combination he

theorem weightedAnnihilator_transform (b : k) (hb : b ≠ 0)
    (A B : Matrix.SpecialLinearGroup (Fin 3) k)
    (hAB : A.val.transpose * diagonalForm b * B.val = diagonalForm b)
    (z : Fin 2 → k) (hd : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z ≠ 0) (j : Fin 2) :
    B.val.mulVec (weightedAnnihilator b z j) =
      weightedDualCoordinates b B z 0 j • weightedAnnihilator b (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage A z) 0 +
        weightedDualCoordinates b B z 1 j • weightedAnnihilator b (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage A z) 1 := by
  apply weightedAnnihilator_reconstruct b hb
  have h := weighted_pairing_preserved b A B hAB (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z) (weightedAnnihilator b z j)
  rw [weightedAnnihilator_orthogonal b hb z j, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector_chartImage A z hd,
    smul_dotProduct] at h
  exact (mul_eq_zero.mp h).resolve_left hd

def weightedFrame (b : k) (z : Fin 2 → k) (u : Fin 3 → k) : (Fin 3 → k) × (Fin 3 → k) :=
  (u 0 • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z,
    u 1 • weightedAnnihilator b z 0 + u 2 • weightedAnnihilator b z 1)

theorem activeFrameMatrix_mulVec (b : k) (A B : Matrix.SpecialLinearGroup (Fin 3) k)
    (z : Fin 2 → k) (u : Fin 3 → k) :
    (activeFrameMatrix b A B z).mulVec u =
      ![RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z * u 0,
        weightedDualCoordinates b B z 0 0 * u 1 + weightedDualCoordinates b B z 0 1 * u 2,
        weightedDualCoordinates b B z 1 0 * u 1 + weightedDualCoordinates b B z 1 1 * u 2] := by
  funext i
  fin_cases i <;> simp [activeFrameMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem weightedFrame_transform (b : k) (hb : b ≠ 0)
    (A B : Matrix.SpecialLinearGroup (Fin 3) k)
    (hAB : A.val.transpose * diagonalForm b * B.val = diagonalForm b)
    (z : Fin 2 → k) (hd : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z ≠ 0) (u : Fin 3 → k) :
    (A.val.mulVec (weightedFrame b z u).1, B.val.mulVec (weightedFrame b z u).2) =
      weightedFrame b (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage A z) ((activeFrameMatrix b A B z).mulVec u) := by
  rw [activeFrameMatrix_mulVec]
  apply Prod.ext
  · change A.val.mulVec (u 0 • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z) = (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A z * u 0) • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage A z)
    rw [Matrix.mulVec_smul, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector_chartImage A z hd, smul_smul, mul_comm]
  · change B.val.mulVec (u 1 • weightedAnnihilator b z 0 + u 2 • weightedAnnihilator b z 1) = _
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      weightedAnnihilator_transform b hb A B hAB z hd 0,
      weightedAnnihilator_transform b hb A B hAB z hd 1]
    funext i
    simp [weightedFrame, smul_add, smul_smul]
    ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryFrameAction
