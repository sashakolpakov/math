import OAI.Analysis.PDE.Weak.SobolevWeakCompactTest
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Weak

variable {X Y V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Weak derivatives commute with a measure-preserving linear change of
coordinates, including a change between the finite Pi and Euclidean norms. -/
theorem HasWeakDirectionalDerivative.comp_measurePreserving_equiv
    {μ : Measure X} {ν : Measure Y} (e : X ≃L[ℝ] Y)
    (he : MeasurePreserving e μ ν) {v : X} {u g : Y → V}
    (h : HasWeakDirectionalDerivative ν (e v) u g) :
    HasWeakDirectionalDerivative μ v (u ∘ e) (g ∘ e) := by
  intro φ hφ hφs
  let ψ : Y → V := φ ∘ e.symm
  have hψ : ContDiff ℝ 1 ψ := hφ.comp e.symm.contDiff
  have hψs : HasCompactSupport ψ := hφs.comp_homeomorph e.symm.toHomeomorph
  have hd (y : Y) : fderiv ℝ ψ y (e v) = fderiv ℝ φ (e.symm y) v := by
    have hder := ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp y
      e.symm.toContinuousLinearMap.hasFDerivAt
    have hder' : HasFDerivAt ψ
        ((fderiv ℝ φ (e.symm y)).comp e.symm.toContinuousLinearMap) y := hder
    rw [hder'.fderiv]
    simp
  have htest := h ψ hψ hψs
  have hleft := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y ↦ inner ℝ (g y) (ψ y))
  have hright := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y ↦ inner ℝ (u y) (fderiv ℝ ψ y (e v)))
  rw [← hleft, ← hright] at htest
  simpa only [hd, ψ, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using htest

end OAI.Analysis.PDE.Weak
