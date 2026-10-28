import OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

/-! # Annihilator Frame -/

namespace OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame

noncomputable section

/-! The inverse-transpose action really maps the displayed annihilator
frames at z to the displayed frames at g z. Thus the determinant computed
in DeterminantCoordinates is the coordinate determinant of that map. -/

open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable {k : Type*} [Field k]

def frameVector (z a : Fin 2 → k) : Fin 3 → k :=
  ![a 0, a 1, -(z 0 * a 0 + z 1 * a 1)]

theorem line_dot_annihilator (z : Fin 2 → k) (j : Fin 2) :
    dotProduct (DeterminantCoordinates.lineVector z) (DeterminantCoordinates.annihilatorVector z j) = 0 := by
  fin_cases j <;> simp [DeterminantCoordinates.lineVector, DeterminantCoordinates.annihilatorVector, dotProduct, Fin.sum_univ_succ]

theorem inverseTranspose_pairing (g : Matrix.SpecialLinearGroup (Fin 3) k) (x y : Fin 3 → k) :
    dotProduct (g.val.mulVec x) ((g⁻¹).val.transpose.mulVec y) = dotProduct x y := by
  rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]
  have hmul : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  rw [hmul, Matrix.one_mulVec, dotProduct_comm]

theorem line_dot_dualColumn (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k)
    (hd : DeterminantCoordinates.denominator g z ≠ 0) (j : Fin 2) :
    dotProduct (DeterminantCoordinates.lineVector (DeterminantCoordinates.chartImage g z)) (DeterminantCoordinates.dualColumn g z j) = 0 := by
  have h : dotProduct (g.val.mulVec (DeterminantCoordinates.lineVector z)) (DeterminantCoordinates.dualColumn g z j) = 0 :=
    (inverseTranspose_pairing g (DeterminantCoordinates.lineVector z) (DeterminantCoordinates.annihilatorVector z j)).trans (line_dot_annihilator z j)
  rw [DeterminantCoordinates.lineVector_chartImage g z hd, smul_dotProduct] at h
  exact (mul_eq_zero.mp h).resolve_left hd

theorem annihilator_frame_coordinates (z : Fin 2 → k) (x : Fin 3 → k)
    (hx : dotProduct (DeterminantCoordinates.lineVector z) x = 0) :
    x = frameVector z (fun i : Fin 2 => x i.castSucc) := by
  have hlast : x 2 = -(z 0 * x 0 + z 1 * x 1) := by
    have hsum : z 0 * x 0 + z 1 * x 1 + x 2 = 0 := by
      simpa [DeterminantCoordinates.lineVector, dotProduct, Fin.sum_univ_succ, add_assoc] using hx
    exact eq_neg_of_add_eq_zero_right hsum
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact hlast

theorem dualColumn_frame (g : Matrix.SpecialLinearGroup (Fin 3) k) (z : Fin 2 → k)
    (hd : DeterminantCoordinates.denominator g z ≠ 0) (j : Fin 2) :
    DeterminantCoordinates.dualColumn g z j = frameVector (DeterminantCoordinates.chartImage g z) (fun i => DeterminantCoordinates.dualCoordinates g z i j) :=
  annihilator_frame_coordinates (DeterminantCoordinates.chartImage g z) (DeterminantCoordinates.dualColumn g z j) (line_dot_dualColumn g z hd j)

end

end OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame
