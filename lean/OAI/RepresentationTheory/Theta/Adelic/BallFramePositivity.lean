import OAI.RepresentationTheory.Theta.Adelic.BallNatural
import OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame

/-! # Ball Frame Positivity -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.BallFramePositivity.RankThreeHodgeAction

/-! The explicit rank-three Hodge-frame action: the tautological line
and its two annihilator columns, with determinant equal to the square
of the projective denominator. -/

open _root_.Matrix
open scoped Classical

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame

variable (g : BallNatural.BallGroup) (z : BallNatural.Ball)

def hodgeFrameMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![DeterminantCoordinates.denominator (BallNatural.asSL g) z.val, 0, 0;
     0, DeterminantCoordinates.dualCoordinates (BallNatural.asSL g) z.val 0 0, DeterminantCoordinates.dualCoordinates (BallNatural.asSL g) z.val 0 1;
     0, DeterminantCoordinates.dualCoordinates (BallNatural.asSL g) z.val 1 0, DeterminantCoordinates.dualCoordinates (BallNatural.asSL g) z.val 1 1]

theorem hodgeFrameMatrix_det : (hodgeFrameMatrix g z).det = DeterminantCoordinates.denominator (BallNatural.asSL g) z.val ^ 2 := by
  calc
    _ = DeterminantCoordinates.denominator (BallNatural.asSL g) z.val * (DeterminantCoordinates.dualCoordinates (BallNatural.asSL g) z.val).det := by
      simp [hodgeFrameMatrix, Matrix.det_fin_three, Matrix.det_fin_two]
      ring
    _ = _ := by rw [DeterminantCoordinates.dualCoordinates_det, pow_two]

def hodgeFrameUnit : (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (hodgeFrameMatrix g z)
    (by rw [hodgeFrameMatrix_det]; exact pow_ne_zero _ (BallNatural.denominator_ne_zero g z))

def standardHodgeColumn (a : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => DeterminantCoordinates.lineVector z.val i * a 0

def dualHodgeColumn (a : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => DeterminantCoordinates.annihilatorVector z.val 0 i * a 1 + DeterminantCoordinates.annihilatorVector z.val 1 i * a 2

theorem standard_hodge_transform (a : Fin 3 → ℂ) :
    (BallNatural.asSL g).val.mulVec (standardHodgeColumn z a) =
      standardHodgeColumn (g • z) ((hodgeFrameMatrix g z).mulVec a) := by
  have he : standardHodgeColumn z a = a 0 • DeterminantCoordinates.lineVector z.val := by
    ext i
    exact mul_comm _ _
  rw [he, Matrix.mulVec_smul, DeterminantCoordinates.lineVector_chartImage (BallNatural.asSL g) z.val (BallNatural.denominator_ne_zero g z)]
  have hrow : (hodgeFrameMatrix g z).mulVec a 0 = DeterminantCoordinates.denominator (BallNatural.asSL g) z.val * a 0 := by
    simp [hodgeFrameMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ext i
  change a 0 * (DeterminantCoordinates.denominator (BallNatural.asSL g) z.val * DeterminantCoordinates.lineVector (DeterminantCoordinates.chartImage (BallNatural.asSL g) z.val) i) =
    DeterminantCoordinates.lineVector (g • z).val i * (hodgeFrameMatrix g z).mulVec a 0
  rw [hrow]
  change _ = DeterminantCoordinates.lineVector (DeterminantCoordinates.chartImage (BallNatural.asSL g) z.val) i * (DeterminantCoordinates.denominator (BallNatural.asSL g) z.val * a 0)
  ring

theorem dual_hodge_transform (a : Fin 3 → ℂ) :
    (BallNatural.asSL g)⁻¹.val.transpose.mulVec (dualHodgeColumn z a) =
      dualHodgeColumn (g • z) ((hodgeFrameMatrix g z).mulVec a) := by
  have he : dualHodgeColumn z a = a 1 • DeterminantCoordinates.annihilatorVector z.val 0 + a 2 • DeterminantCoordinates.annihilatorVector z.val 1 := by
    ext i
    change DeterminantCoordinates.annihilatorVector z.val 0 i * a 1 + DeterminantCoordinates.annihilatorVector z.val 1 i * a 2 = _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  change a 1 • DeterminantCoordinates.dualColumn (BallNatural.asSL g) z.val 0 + a 2 • DeterminantCoordinates.dualColumn (BallNatural.asSL g) z.val 1 = _
  rw [AnnihilatorFrame.dualColumn_frame (BallNatural.asSL g) z.val (BallNatural.denominator_ne_zero g z) 0,
    AnnihilatorFrame.dualColumn_frame (BallNatural.asSL g) z.val (BallNatural.denominator_ne_zero g z) 1]
  have hchart : (g • z).val = DeterminantCoordinates.chartImage (BallNatural.asSL g) z.val := rfl
  ext i
  fin_cases i <;>
    simp [dualHodgeColumn, hodgeFrameMatrix, AnnihilatorFrame.frameVector, DeterminantCoordinates.annihilatorVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hchart] <;> ring

end RepresentationTheory.Theta.Adelic.BallFramePositivity.RankThreeHodgeAction

namespace RepresentationTheory.Theta.Adelic.BallFramePositivity

/-! Explicit positivity of the tautological line and annihilator
frame on the unit two-ball. -/

open scoped Classical ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallFramePositivity.RankThreeHodgeAction OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

theorem complex_cauchy_two (z w a b : ℂ) :
    (Complex.normSq z + Complex.normSq w) * (Complex.normSq a + Complex.normSq b) -
      Complex.normSq (z * a + w * b) =
        Complex.normSq (conj z * b - conj w * a) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

def annihilatorEnergy (z : BallNatural.Ball) (a b : ℂ) : ℝ :=
  Complex.normSq a + Complex.normSq b - Complex.normSq (z.val 0 * a + z.val 1 * b)

theorem annihilatorEnergy_nonneg (z : BallNatural.Ball) (a b : ℂ) :
    0 ≤ annihilatorEnergy z a b := by
  have h := complex_cauchy_two (z.val 0) (z.val 1) a b
  have hn := Complex.normSq_nonneg (conj (z.val 0) * b - conj (z.val 1) * a)
  have hp := add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b)
  have hz : Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < 1 := z.property
  dsimp [annihilatorEnergy]
  nlinarith

theorem annihilatorEnergy_pos (z : BallNatural.Ball) (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < annihilatorEnergy z a b := by
  have h := complex_cauchy_two (z.val 0) (z.val 1) a b
  have hn := Complex.normSq_nonneg (conj (z.val 0) * b - conj (z.val 1) * a)
  have hp : 0 < Complex.normSq a + Complex.normSq b := by
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr ha) (Complex.normSq_nonneg b)
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg a) (Complex.normSq_pos.mpr hb)
  have hz : Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < 1 := z.property
  dsimp [annihilatorEnergy]
  nlinarith

def ballFrameEnergy (z : BallNatural.Ball) (a : Fin 3 → ℂ) : ℝ :=
  (1 - (Complex.normSq (z.val 0) + Complex.normSq (z.val 1))) * Complex.normSq (a 0) +
    annihilatorEnergy z (a 1) (a 2)

theorem ballFrameEnergy_nonneg (z : BallNatural.Ball) (a : Fin 3 → ℂ) : 0 ≤ ballFrameEnergy z a :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr z.property.le) (Complex.normSq_nonneg _))
    (annihilatorEnergy_nonneg z _ _)

theorem ballFrameEnergy_pos (z : BallNatural.Ball) (a : Fin 3 → ℂ) (ha : a ≠ 0) :
    0 < ballFrameEnergy z a := by
  by_cases ha0 : a 0 = 0
  · have hab : a 1 ≠ 0 ∨ a 2 ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      funext i
      fin_cases i <;> simp [ha0, h]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr z.property.le) (Complex.normSq_nonneg _))
      (annihilatorEnergy_pos z _ _ hab)
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr z.property) (Complex.normSq_pos.mpr ha0))
      (annihilatorEnergy_nonneg z _ _)

theorem ballFrameEnergy_formula (z : BallNatural.Ball) (a : Fin 3 → ℂ) :
    ∑ i : Fin 3, (if i = 2 then (1 : ℝ) else -1) *
      (Complex.normSq (RankThreeHodgeAction.standardHodgeColumn z a i) - Complex.normSq (RankThreeHodgeAction.dualHodgeColumn z a i)) =
        ballFrameEnergy z a := by
  simp [Fin.sum_univ_succ, RankThreeHodgeAction.standardHodgeColumn, RankThreeHodgeAction.dualHodgeColumn,
    DeterminantCoordinates.lineVector, DeterminantCoordinates.annihilatorVector, ballFrameEnergy, annihilatorEnergy, map_mul]
  rw [← neg_add, Complex.normSq_neg]
  ring

end RepresentationTheory.Theta.Adelic.BallFramePositivity

end

end OAI
