import OAI.Analysis.PDE.Schauder.Calculus.Boundary.JetTransform

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ}

/-- Transport a drift vector by an affine change of variables, together
with the scalar used to normalize the equation. -/
def affineDriftHolder (hα : 0 ≤ α) (b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α)
    (x₀ : E) (T : E ≃L[ℝ] E) (c : ℝ) : OAI.Analysis.Normed.Function.Holder.HolderMap E E α :=
  c • OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM T.symm.toContinuousLinearMap
    (holderLinearAffinePullback hα b x₀ T.toContinuousLinearMap)

@[simp] theorem affineDriftHolder_value (hα : 0 ≤ α) (b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α)
    (x₀ : E) (T : E ≃L[ℝ] E) (c : ℝ) (x : E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (affineDriftHolder hα b x₀ T c) x =
      c • T.symm (OAI.Analysis.Normed.Function.Holder.HolderMap.value b (x₀ + T x)) := rfl

theorem norm_affineDriftHolder_le (hα : 0 ≤ α) (b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α)
    (x₀ : E) (T : E ≃L[ℝ] E) (c : ℝ) :
    ‖affineDriftHolder hα b x₀ T c‖ ≤
      |c| * ‖T.symm.toContinuousLinearMap‖ *
        (1 + ‖T.toContinuousLinearMap‖ ^ α) * ‖b‖ := by
  change ‖c • OAI.Analysis.Normed.Function.Holder.HolderMap.map T.symm.toContinuousLinearMap
    (holderLinearAffinePullback hα b x₀ T.toContinuousLinearMap)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |c| * (‖T.symm.toContinuousLinearMap‖ *
        ‖holderLinearAffinePullback hα b x₀ T.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le _ _) (abs_nonneg _)
    _ ≤ |c| * (‖T.symm.toContinuousLinearMap‖ *
        ((1 + ‖T.toContinuousLinearMap‖ ^ α) * ‖b‖)) := by
      gcongr
      exact OAI.Analysis.PDE.Nonlinear.norm_holderLinearAffinePullback_le hα b x₀ T.toContinuousLinearMap
    _ = _ := by ring

theorem affineDriftHolder_derivative (hα : 0 ≤ α) (b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α)
    (u : E → ℝ) (hu : Differentiable ℝ u)
    (x₀ : E) (T : E ≃L[ℝ] E) (c : ℝ) (x : E) :
    fderiv ℝ (fun y => u (x₀ + T y)) x
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (affineDriftHolder hα b x₀ T c) x) =
      c * fderiv ℝ u (x₀ + T x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value b (x₀ + T x)) := by
  rw [affineDriftHolder_value]
  have hd : fderiv ℝ (fun y => u (x₀ + T y)) x =
      (fderiv ℝ u (x₀ + T x)).comp T.toContinuousLinearMap :=
    OAI.Analysis.PDE.Nonlinear.fderiv_linearAffine u hu x₀ x T.toContinuousLinearMap
  rw [hd]
  change fderiv ℝ u (x₀ + T x) (T (c • T.symm (OAI.Analysis.Normed.Function.Holder.HolderMap.value b (x₀ + T x)))) = _
  simp only [map_smul, T.apply_symm_apply, smul_eq_mul]

end OAI.Analysis.PDE.Schauder
