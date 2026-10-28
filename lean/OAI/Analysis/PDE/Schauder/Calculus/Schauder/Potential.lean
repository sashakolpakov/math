import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PrincipalValue

/-! The actual Newtonian convolution and its classical derivatives for smooth compact data. -/

noncomputable section
open _root_.MeasureTheory
open scoped Convolution
namespace OAI.Analysis.PDE.Schauder

theorem locallyIntegrable_newtonianKernel {m : ℕ} (hm : 1 ≤ m) :
    LocallyIntegrable (newtonianKernel (E := EuclideanSpace ℝ (Fin m)) m) := by
  apply locallyIntegrable_of_norm_le_rpow (by simpa using hm)
    (α := (m : ℝ) - 2) (C := 1) (by simp only [finrank_euclideanSpace_fin]; linarith)
  · filter_upwards [] with y
    rw [newtonianKernel_eq_norm_rpow, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _), one_mul]
    simp only [neg_sub]
    exact le_rfl
  · have he : newtonianKernel (E := EuclideanSpace ℝ (Fin m)) m =
        fun y => ‖y‖ ^ (2 - (m : ℝ)) := funext (newtonianKernel_eq_norm_rpow m)
    rw [he]
    exact (measurable_norm.pow_const _).aestronglyMeasurable

def newtonianPotential {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ y, newtonianKernel m y * f (x - y)

theorem newtonianPotential_eq_convolution {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    newtonianPotential f =
      newtonianKernel m ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f := rfl

theorem newtonianPotential_integrable {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun y => newtonianKernel m y * f (x - y)) :=
  hfc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel hm) hf x

theorem contDiff_newtonianPotential {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) {k : ℕ∞} (hf : ContDiff ℝ k f)
    (hfc : HasCompactSupport f) : ContDiff ℝ k (newtonianPotential f) := by
  rw [newtonianPotential_eq_convolution]
  exact hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel hm) hf

theorem hasFDerivAt_newtonianPotential {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (newtonianPotential f)
      ((newtonianKernel m ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR
        (EuclideanSpace ℝ (Fin m)), volume] fderiv ℝ f) x) x := by
  rw [newtonianPotential_eq_convolution]
  exact hfc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel hm) hf x

end OAI.Analysis.PDE.Schauder
