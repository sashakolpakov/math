import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Directional Commutation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.DirectionalCommutation.Dolbeault

noncomputable section

/-! Actual constant real directional derivatives commute for a smooth
function, by symmetry of its genuine second Fréchet derivative. -/

open scoped ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_constantDerivative_commute {g : E → F} {x : E}
    (hg : ContDiffAt ℝ ∞ g x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hd := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hs := hg.isSymmSndFDerivAt (by simp)
  have hv : fderiv ℝ (fun y => fderiv ℝ g y v) x =
      (ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ g) x) :=
    ((ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  have hw : fderiv ℝ (fun y => fderiv ℝ g y w) x =
      (ContinuousLinearMap.apply ℝ F w).comp (fderiv ℝ (fderiv ℝ g) x) :=
    ((ContinuousLinearMap.apply ℝ F w).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  rw [hv, hw]
  exact hs.eq w v

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.DirectionalCommutation.Dolbeault
