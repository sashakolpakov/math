import OAI.Analysis.PDE.Weak.Boundary.Chart.Ellipticity

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem exists_chart_local_ellipticity
    {U V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hGU : MapsTo G U V) (hPG : ∀ y ∈ U, P (G y) = y)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ z ∈ V, ∀ v, lam * ‖v‖^2 ≤ inner ℝ (A z v) v)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ U) :
    ∃ (W : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (lam' : ℝ),
      IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ContDiff ℝ ∞ w ∧ 0 < lam' ∧
      (∀ y ∈ W, w y = |(fderiv ℝ G y).det|) ∧
      (∀ y ∈ W, ∀ v, lam' * ‖v‖^2 ≤ inner ℝ (chartCoefficient A G P w y v) v) := by
  obtain ⟨W, w, c, hW, hxW, hWU, hw, hc, hwc⟩ :=
    exists_smooth_positive_chartWeight hU hG hP hPG hx
  let M := ‖chartGradientMap G x‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let W' := W ∩ {y | ‖chartGradientMap G y‖ < M}
  refine ⟨W', w, c * lam / M^2,
    hW.inter (isOpen_lt (continuous_chartGradientMap (hG.of_le (by simp))).norm continuous_const),
    ⟨hxW, by dsimp [M]; linarith⟩, inter_subset_left.trans hWU, hw,
    div_pos (mul_pos hc hlam) (sq_pos_of_pos hM), ?_, ?_⟩
  · intro y hy
    exact (hwc y hy.1).2
  · intro y hy v
    exact chartCoefficient_elliptic A G P w y hlam.le hc.le hM (hwc y hy.1).1
      (le_of_lt hy.2) (chartGradientMap_inverse_other hU (hG.of_le (by simp))
        (hP.of_le (by simp)) hPG (hWU hy.1)) (hell _ (hGU (hWU hy.1))) v

end OAI.Analysis.PDE.Weak
