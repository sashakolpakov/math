import OAI.Analysis.PDE.Weak.Elliptic.Regularity
import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
import OAI.Analysis.PDE.Green.GreenReal

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem smooth_scalar_weak_derivative
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin (m + 1)) :
    HasWeakDirectionalDerivative volume (Pi.single j 1) f (coordinateDerivative f j) := by
  intro φ hφ hs
  simpa only [coordinateDerivative, RCLike.inner_apply, conj_trivial, mul_comm] using
    OAI.Analysis.PDE.Green.integral_directional_by_parts hφ hf hs (Pi.single j 1)

theorem weakRegularity_of_smooth_compact
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ) :
    WeakRegularity Ω k ((hf.continuous.memLp_of_hasCompactSupport hs).toLp f) := by
  induction k generalizing f with
  | zero => trivial
  | succ k ih =>
    intro j
    have hd := contDiff_coordinateDerivative hf j
    have hds : HasCompactSupport (coordinateDerivative f j) := hs.fderiv_apply ℝ _
    let g : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) :=
      (hd.continuous.memLp_of_hasCompactSupport hds).toLp (coordinateDerivative f j)
    refine ⟨g, ?_, ih hd hds⟩
    apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on volume
      (smooth_scalar_weak_derivative (hf.of_le (by simp)) j).on
    · filter_upwards [(hf.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp] with x hx
      exact fun _ ↦ hx.symm
    · filter_upwards [(hd.continuous.memLp_of_hasCompactSupport hds).coeFn_toLp] with x hx
      exact fun _ ↦ hx.symm

end OAI.Analysis.PDE.Weak
