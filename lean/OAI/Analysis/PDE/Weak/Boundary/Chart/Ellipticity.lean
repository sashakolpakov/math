import OAI.Analysis.PDE.Weak.Boundary.Chart.Coefficient

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem chartCoefficient_elliptic
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (y : OAI.Analysis.PDE.Variational.CellCoordinates m) {lam c M : ℝ} (hlam : 0 ≤ lam) (hc : 0 ≤ c)
    (hM : 0 < M) (hw : c ≤ w y)
    (hCM : ‖chartGradientMap G y‖ ≤ M)
    (hinv : (chartGradientMap G y).comp (chartGradientMap P (G y)) =
      ContinuousLinearMap.id ℝ _)
    (hA : ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A (G y) v) v) (v : OAI.Analysis.PDE.Variational.CellVectors m) :
    (c * lam / M^2) * ‖v‖^2 ≤ inner ℝ (chartCoefficient A G P w y v) v := by
  let z := chartGradientMap P (G y) v
  have he : chartGradientMap G y z = v := congrArg (fun T => T v) hinv
  have hn : ‖v‖ ≤ M * ‖z‖ := by
    rw [← he]
    exact (chartGradientMap G y).le_opNorm z |>.trans
      (mul_le_mul_of_nonneg_right hCM (norm_nonneg z))
  have hs : ‖v‖^2 ≤ M^2 * ‖z‖^2 := by nlinarith [norm_nonneg v, norm_nonneg z]
  have hcz : c * lam * ‖z‖^2 ≤ w y * inner ℝ (A (G y) z) z := by
    calc
      c * lam * ‖z‖^2 = c * (lam * ‖z‖^2) := by ring
      _ ≤ c * inner ℝ (A (G y) z) z := mul_le_mul_of_nonneg_left (hA z) hc
      _ ≤ w y * inner ℝ (A (G y) z) z :=
        mul_le_mul_of_nonneg_right hw ((mul_nonneg hlam (sq_nonneg _)).trans (hA z))
  rw [chartCoefficient_form]
  calc
    (c * lam / M^2) * ‖v‖^2 = (c * lam * ‖v‖^2) / M^2 := by ring
    _ ≤ (c * lam * (M^2 * ‖z‖^2)) / M^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (mul_nonneg hc hlam)) (sq_nonneg M)
    _ = c * lam * ‖z‖^2 := by field_simp
    _ ≤ w y * inner ℝ (A (G y) z) z := hcz

/-- A single smooth signed determinant equals the positive volume
Jacobian near every nonsingular chart point. -/
theorem exists_smooth_positive_chartWeight
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hPG : ∀ y ∈ U, P (G y) = y)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ U) :
    ∃ (W : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (c : ℝ),
      IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ContDiff ℝ ∞ w ∧ 0 < c ∧
      (∀ y ∈ W, c ≤ w y ∧ w y = |(fderiv ℝ G y).det|) := by
  have hd := contDiff_chartJacobian hG
  have hn := chartJacobian_ne_zero hU (hG.of_le (by simp)) (hP.of_le (by simp)) hPG hx
  rcases lt_or_gt_of_ne hn with hn | hn
  · let c := -(fderiv ℝ G x).det / 2
    let W := U ∩ {y | (fderiv ℝ G y).det < -c}
    refine ⟨W, fun y => -(fderiv ℝ G y).det, c, hU.inter (isOpen_lt hd.continuous continuous_const),
      ⟨hx, ?_⟩, inter_subset_left, hd.neg, ?_, ?_⟩
    · dsimp [c]; linarith
    · dsimp [c]; linarith
    · intro y hy
      have hc : 0 < c := by dsimp [c]; linarith
      have hdy : (fderiv ℝ G y).det < -c := hy.2
      refine ⟨by dsimp only; linarith, ?_⟩
      rw [abs_of_neg (show (fderiv ℝ G y).det < 0 by linarith)]
  · let c := (fderiv ℝ G x).det / 2
    let W := U ∩ {y | c < (fderiv ℝ G y).det}
    refine ⟨W, fun y => (fderiv ℝ G y).det, c, hU.inter (isOpen_lt continuous_const hd.continuous),
      ⟨hx, ?_⟩, inter_subset_left, hd, ?_, ?_⟩
    · dsimp [c]; linarith
    · dsimp [c]; linarith
    · intro y hy
      have hc : 0 < c := by dsimp [c]; linarith
      refine ⟨le_of_lt hy.2, ?_⟩
      rw [abs_of_pos (hc.trans hy.2)]

end OAI.Analysis.PDE.Weak
