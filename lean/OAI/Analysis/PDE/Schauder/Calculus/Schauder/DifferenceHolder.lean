import OAI.Analysis.PDE.Weak.CalculusWeakDifference

/-! Difference quotients preserve the Hölder exponent with a derivative-controlled norm. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Weak

theorem differenceQuotient_holder_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {α : ℝ} (u : E → F) (hu : ContDiff ℝ 1 u)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] F) α) (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u x)
    (v : E) {h : ℝ} (hh : h ≠ 0) :
    (∀ x, ‖OAI.Analysis.PDE.Weak.differenceQuotient v h u x‖ ≤ ‖D‖ * ‖v‖) ∧
    (∀ x y, ‖OAI.Analysis.PDE.Weak.differenceQuotient v h u x - OAI.Analysis.PDE.Weak.differenceQuotient v h u y‖ ≤
      (‖D‖ * ‖v‖) * (dist x y) ^ α) := by
  have hc (x : E) : Continuous (fun t : ℝ => fderiv ℝ u (x + t • (h • v)) v) :=
    ((hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  constructor
  · intro x
    rw [OAI.Analysis.PDE.Weak.differenceQuotient_eq_integral u hu v x hh]
    have hb (t : ℝ) (_ : t ∈ Set.uIoc (0 : ℝ) 1) :
        ‖fderiv ℝ u (x + t • (h • v)) v‖ ≤ ‖D‖ * ‖v‖ := by
      rw [← hD]
      exact ((OAI.Analysis.Normed.Function.Holder.HolderMap.value D _).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le D _) (norm_nonneg v))
    simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
  · intro x y
    rw [OAI.Analysis.PDE.Weak.differenceQuotient_eq_integral u hu v x hh, OAI.Analysis.PDE.Weak.differenceQuotient_eq_integral u hu v y hh,
      ← intervalIntegral.integral_sub ((hc x).intervalIntegrable 0 1) ((hc y).intervalIntegrable 0 1)]
    have hb (t : ℝ) (_ : t ∈ Set.uIoc (0 : ℝ) 1) :
        ‖fderiv ℝ u (x + t • (h • v)) v - fderiv ℝ u (y + t • (h • v)) v‖ ≤
          (‖D‖ * ‖v‖) * (dist x y) ^ α := by
      rw [← hD, ← hD, ← sub_apply]
      have hdist : dist (x + t • (h • v)) (y + t • (h • v)) = dist x y := dist_add_right _ _ _
      calc
        _ ≤ ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value D (x + t • (h • v)) - OAI.Analysis.Normed.Function.Holder.HolderMap.value D (y + t • (h • v))‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖D‖ * (dist x y) ^ α) * ‖v‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
          simpa only [hdist] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le D (x + t • (h • v)) (y + t • (h • v))
        _ = _ := by ring
    simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb

def differenceHolder {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {α : ℝ} (hα : 0 ≤ α) (u : E → F) (hu : ContDiff ℝ 1 u)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] F) α) (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u x)
    (v : E) {h : ℝ} (hh : h ≠ 0) : OAI.Analysis.Normed.Function.Holder.HolderMap E F α := by
  have hb := differenceQuotient_holder_bounds u hu D hD v hh
  have hc : Continuous (OAI.Analysis.PDE.Weak.differenceQuotient v h u) :=
    continuous_const.smul ((hu.continuous.comp (continuous_id.add continuous_const)).sub hu.continuous)
  let f : E →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (OAI.Analysis.PDE.Weak.differenceQuotient v h u) hc (‖D‖ * ‖v‖) hb.1
  exact OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα f hb.2

@[simp] theorem differenceHolder_value {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {α : ℝ} (hα : 0 ≤ α) (u : E → F) (hu : ContDiff ℝ 1 u)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] F) α) (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u x)
    (v : E) {h : ℝ} (hh : h ≠ 0) (x : E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (differenceHolder hα u hu D hD v hh) x = OAI.Analysis.PDE.Weak.differenceQuotient v h u x := rfl

theorem norm_differenceHolder_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {α : ℝ} (hα : 0 ≤ α) (u : E → F) (hu : ContDiff ℝ 1 u)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] F) α) (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u x)
    (v : E) {h : ℝ} (hh : h ≠ 0) :
    ‖differenceHolder hα u hu D hD v hh‖ ≤ ‖D‖ * ‖v‖ := by
  have hb := differenceQuotient_holder_bounds u hu D hD v hh
  exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (by positivity) _ hb.1 hb.2

end OAI.Analysis.PDE.Schauder
