import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Affine

/-! Genuine difference quotients for the weak-to-classical elliptic regularity argument. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.PDE.Weak

def differenceQuotient {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E) (h : ℝ) (u : E → F) (x : E) : F :=
  h⁻¹ • (u (x + h • v) - u x)

theorem differenceQuotient_add {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E) (h : ℝ) (u w : E → F) (x : E) :
    differenceQuotient v h (fun y => u y + w y) x =
      differenceQuotient v h u x + differenceQuotient v h w x := by
  unfold differenceQuotient
  rw [add_sub_add_comm, smul_add]

theorem differenceQuotient_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (h : ℝ) (u w : E → ℝ) (x : E) :
    differenceQuotient v h (fun y => u y * w y) x =
      u (x + h • v) * differenceQuotient v h w x + differenceQuotient v h u x * w x := by
  simp only [differenceQuotient, smul_eq_mul]
  ring

theorem differenceQuotient_eq_integral {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (u : E → F) (hu : ContDiff ℝ 1 u) (v x : E) {h : ℝ} (hh : h ≠ 0) :
    differenceQuotient v h u x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ u (x + t • (h • v)) v := by
  have hpath (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • (h • v)) (h • v) t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const (h • v)).const_add x
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => u (x + t • (h • v)))
      (h • fderiv ℝ u (x + t • (h • v)) v) t := by
    simpa only [map_smul, Function.comp_def] using!
      (hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t (hpath t)
  have hc : Continuous (fun t : ℝ => fderiv ℝ u (x + t • (h • v)) v) :=
    ((hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) ((continuous_const.smul hc).intervalIntegrable 0 1)
  simp only [zero_smul, add_zero, one_smul, intervalIntegral.integral_smul] at hi
  unfold differenceQuotient
  rw [← hi, smul_smul, inv_mul_cancel₀ hh, one_smul]

end OAI.Analysis.PDE.Weak
