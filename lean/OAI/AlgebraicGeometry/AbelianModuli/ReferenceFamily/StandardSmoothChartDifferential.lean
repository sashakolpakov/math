import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StandardSmoothDualCoordinates
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts

/-! # Standard Smooth Chart Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StandardSmoothChartDifferential

noncomputable section

/-! The native standard-smooth chart differentiates to the constructed
dual-number point, with equality on every actual regular function. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts Filter
open scoped _root_.Topology ContDiff

variable {S ι σ : Type*} [CommRing S] [Algebra ℂ S]
  [Fintype ι] [Fintype σ] [DecidableEq ι]

theorem standardSmoothChart_differential (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
    (he : ∀ y i, e y i = y (P.val i.val))
    (hd : ∀ a : S, ContDiffOn ℂ ω (fun u => e.symm u a) e.target)
    (u : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) (hu : u ∈ e.target) (v : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) :
    ∀ a : S, ((StandardSmoothDualCoordinates.standardSmoothDualPointsEquiv P (e.symm u) v).val a).snd =
      fderiv ℂ (fun w => e.symm w a) u v := by
  have hφ (a : S) : DifferentiableAt ℂ (fun w => e.symm w a) u :=
    ((hd a).contDiffAt (e.open_target.mem_nhds hu)).differentiableAt (by simp)
  let f := PresentedPointDifferential.presentedDifferentialPoint P.toPresentation (fun w => e.symm w) u v hφ
  have hf : StandardSmoothDualCoordinates.standardSmoothDualPointsEquiv P (e.symm u) v = f := by
    apply StandardSmoothDualCoordinates.standardSmoothDualPointsEquiv_unique
    intro i
    have heq : (fun w => e.symm w (P.val i.val)) =ᶠ[𝓝 u] (fun w => w i) := by
      filter_upwards [e.open_target.mem_nhds hu] with w hw
      exact (he (e.symm w) i).symm.trans (congrFun (e.right_inv hw) i)
    have hder := (hasFDerivAt_apply (𝕜 := ℂ) i u).congr_of_eventuallyEq heq
    exact (PresentedPointDifferential.presentedDifferentialPoint_snd P.toPresentation (fun w => e.symm w) u v hφ (P.val i.val)).trans
      (DFunLike.congr_fun hder.fderiv v)
  intro a
  exact (congrArg (fun f : Dual.PresentedAlgebra.DualAlgebraPoints (e.symm u) => (f.val a).snd) hf).trans
    (PresentedPointDifferential.presentedDifferentialPoint_snd P.toPresentation (fun w => e.symm w) u v hφ a)

theorem exists_standardSmooth_chart_dual_comparison
    (P : Algebra.SubmersivePresentation ℂ S ι σ) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ),
      x ∈ e.source ∧
      (∀ y i, e y i = y (P.val i.val)) ∧
      (∀ a : S, ContDiffOn ℂ ω (fun u => e.symm u a) e.target) ∧
      ∀ (u : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ), u ∈ e.target →
        ∀ (v : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) (a : S),
          ((StandardSmoothDualCoordinates.standardSmoothDualPointsEquiv P (e.symm u) v).val a).snd =
            fderiv ℂ (fun w => e.symm w a) u v := by
  obtain ⟨e, hx, he, hd⟩ := ComplexPoints.Analytic.SmoothAffineCharts.exists_standardSmooth_point_chart P x
  exact ⟨e, hx, he, hd, standardSmoothChart_differential P e he hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StandardSmoothChartDifferential
