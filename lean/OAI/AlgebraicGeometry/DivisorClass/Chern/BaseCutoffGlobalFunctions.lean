import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseCutoffBounds
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealChartExtension

/-! # Base Cutoff Global Functions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCutoffGlobalFunctions

noncomputable section

/-! Actual smooth global cutoff-error functions and exact reconstruction of the fixed squared base partition. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def projectiveBaseCutoffGlobalError (i : Projective.BasePartition.projectiveBaseFiniteCover V) : V.analyticSpace → ℝ :=
  RealChartExtension.projectiveRealChartExtension V (chartAt V.analyticModel i.val)
    (Projective.CutoffEnergy.projectiveCutoffEnergy V (chartAt V.analyticModel i.val) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i))

theorem projectiveBaseCutoffGlobalError_smooth (i : Projective.BasePartition.projectiveBaseFiniteCover V) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ) ∞ (projectiveBaseCutoffGlobalError V i) :=
  RealChartExtension.projectiveRealChartExtension_smooth V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val) _
    (Projective.CutoffEnergy.projectiveCutoffEnergy_smooth V _ (chart_mem_atlas V.analyticModel i.val) _
      (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_smooth V i) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_support V i))
    (Projective.CutoffEnergy.projectiveCutoffEnergy_hasCompactSupport V _ _ (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_compact V i))
    ((Projective.CutoffEnergy.projectiveCutoffEnergy_tsupport V _ _).trans (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_support V i))

theorem projectiveBaseCutoffGlobalError_bound (i : Projective.BasePartition.projectiveBaseFiniteCover V) (x : V.analyticSpace) :
    projectiveBaseCutoffGlobalError V i x ≤ Projective.BaseCutoffBounds.projectiveBaseCutoffErrorBound V i :=
  RealChartExtension.projectiveRealChartExtension_bound V (chartAt V.analyticModel i.val) _ _
    (Projective.BaseCutoffBounds.projectiveBaseCutoffErrorBound_pos V i).le (Projective.BaseCutoffBounds.projectiveBaseCutoffEnergy_bound V i) x

theorem projectiveBaseCutoffGlobalError_sum_bound (x : V.analyticSpace) :
    (∑ i, projectiveBaseCutoffGlobalError V i x) ≤ Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V := by
  apply (Finset.sum_le_sum (fun i _ => projectiveBaseCutoffGlobalError_bound V i x)).trans
  unfold Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound
  linarith

theorem projectiveBaseSquareChartExtension (i : Projective.BasePartition.projectiveBaseFiniteCover V) (x : V.analyticSpace) :
    RealChartExtension.projectiveRealChartExtension V (chartAt V.analyticModel i.val)
      (fun z => Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i z ^ 2) x = Projective.BaseSquarePartition.projectiveBaseSquarePartition V i x ^ 2 := by
  by_cases hx : x ∈ (chartAt V.analyticModel i.val).source
  · rw [RealChartExtension.projectiveRealChartExtension_apply V _ _ hx]
    rw [Projective.BaseChartCutoffs.projectiveBaseChartCutoff_reconstruct V i hx]
  · rw [RealChartExtension.projectiveRealChartExtension_zero V _ _ hx,
      image_eq_zero_of_notMem_tsupport (fun ht => hx (Projective.BaseSquarePartition.projectiveBaseSquarePartition_support V i ht)),
      zero_pow (by decide : 2 ≠ 0)]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCutoffGlobalFunctions
