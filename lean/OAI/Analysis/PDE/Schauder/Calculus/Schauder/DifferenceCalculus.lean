import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceHolder
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Actual differentiation and limits of the classical difference quotients. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Weak

theorem contDiff_differenceQuotient {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (u : E → F) (hu : ContDiff ℝ n u) (v : E) (h : ℝ) :
    ContDiff ℝ n (OAI.Analysis.PDE.Weak.differenceQuotient v h u) :=
  ((hu.comp (contDiff_id.add contDiff_const)).sub hu).const_smul _

theorem fderiv_differenceQuotient {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → F) (hu : Differentiable ℝ u) (v : E) (h : ℝ) (x : E) :
    fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x = OAI.Analysis.PDE.Weak.differenceQuotient v h (fderiv ℝ u) x := by
  have hd : HasFDerivAt (fun y => u (y + h • v)) (fderiv ℝ u (x + h • v)) x :=
    (hasFDerivAt_comp_add_right (h • v)).mpr (hu (x + h • v)).hasFDerivAt
  exact ((hd.sub (hu x).hasFDerivAt).const_smul (h⁻¹)).fderiv

theorem second_fderiv_differenceQuotient {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → F) (hu : ContDiff ℝ 2 u) (v : E) (h : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u)) x =
      OAI.Analysis.PDE.Weak.differenceQuotient v h (fderiv ℝ (fderiv ℝ u)) x := by
  have he : fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u) = OAI.Analysis.PDE.Weak.differenceQuotient v h (fderiv ℝ u) :=
    funext (fderiv_differenceQuotient u (hu.differentiable (by norm_num)) v h)
  rw [he]
  exact fderiv_differenceQuotient (fderiv ℝ u)
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) v h x

theorem tendsto_differenceQuotient {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E → F) (v x : E) (hu : DifferentiableAt ℝ u x) :
    Tendsto (fun h => OAI.Analysis.PDE.Weak.differenceQuotient v h u x) (𝓝[≠] 0) (𝓝 (fderiv ℝ u x v)) := by
  exact (hu.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero

end OAI.Analysis.PDE.Schauder
