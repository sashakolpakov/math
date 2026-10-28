import OAI.Analysis.PDE.Schauder.Calculus.PointwiseDerivative
import OAI.Analysis.Normed.Function.Holder.Banach.Maps

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α : ℝ}

local instance holderCurveGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance
local instance holderCurveSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance

def holderNormingEval (i : X ⊕ OAI.Analysis.Normed.Function.Holder.DistinctPairs X) : OAI.Analysis.Normed.Function.Holder.HolderMap X F α →L[ℝ] F :=
  match i with
  | Sum.inl x => (OAI.Analysis.Normed.Function.Holder.boundedEvaluation x).comp OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM
  | Sum.inr q => (OAI.Analysis.Normed.Function.Holder.boundedEvaluation q).comp
      ((ContinuousLinearMap.snd ℝ (X →ᵇ F) (OAI.Analysis.Normed.Function.Holder.DistinctPairs X →ᵇ F)).comp
        (OAI.Analysis.Normed.Function.Holder.holderGraph X F α).subtypeL)

theorem holderNormingEval_bound (i : X ⊕ OAI.Analysis.Normed.Function.Holder.DistinctPairs X) (v : OAI.Analysis.Normed.Function.Holder.HolderMap X F α) :
    ‖holderNormingEval i v‖ ≤ ‖v‖ := by
  cases i with
  | inl x => exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le v x
  | inr q => exact (v.val.2.norm_coe_le_norm q).trans (le_max_right _ _)

theorem holderNormingEval_norm (i : X ⊕ OAI.Analysis.Normed.Function.Holder.DistinctPairs X) :
    ‖holderNormingEval (F := F) (α := α) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul] using holderNormingEval_bound i v

theorem holderNormingEval_norming (v : OAI.Analysis.Normed.Function.Holder.HolderMap X F α) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ i, ‖holderNormingEval i v‖ ≤ C) : ‖v‖ ≤ C := by
  change max ‖v.val.1‖ ‖v.val.2‖ ≤ C
  apply max_le
  · exact (BoundedContinuousFunction.norm_le hC).mpr (fun x => hv (Sum.inl x))
  · exact (BoundedContinuousFunction.norm_le hC).mpr (fun q => hv (Sum.inr q))

theorem holder_quotient_value (v : OAI.Analysis.Normed.Function.Holder.HolderMap X F α) (q : OAI.Analysis.Normed.Function.Holder.DistinctPairs X) :
    v.val.2 q = (dist q.val.1 q.val.2 ^ α)⁻¹ •
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value v q.val.1-OAI.Analysis.Normed.Function.Holder.HolderMap.value v q.val.2) := by
  change v.val.2 q = (dist q.val.1 q.val.2 ^ α)⁻¹ •
    (v.val.1 q.val.1-v.val.1 q.val.2)
  rw [← v.property q,smul_smul,inv_mul_cancel₀
    (Real.rpow_pos_of_pos (dist_pos.mpr q.property) α).ne',one_smul]

/-- Norm differentiability of a Hölder-valued curve follows from actual
pointwise derivatives and continuity of the candidate Hölder derivative. -/
theorem hasDerivAt_holder_of_pointwise
    {f g : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap X F α} {U : Set ℝ} (hU : IsOpen U)
    {a : ℝ} (ha : a ∈ U) (hg : ContinuousAt g a)
    (hd : ∀ t ∈ U, ∀ x, HasDerivAt (fun s => OAI.Analysis.Normed.Function.Holder.HolderMap.value (f s) x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (g t) x) t) : HasDerivAt f (g a) a := by
  have heval : ∀ t ∈ U, ∀ i : X ⊕ OAI.Analysis.Normed.Function.Holder.DistinctPairs X,
      HasDerivAt (fun s => holderNormingEval i (f s)) (holderNormingEval i (g t)) t := by
    intro t ht i
    cases i with
    | inl x => exact hd t ht x
    | inr q =>
        have h := ((hd t ht q.val.1).sub (hd t ht q.val.2)).const_smul
          ((dist q.val.1 q.val.2 ^ α)⁻¹)
        change HasDerivAt (fun s => (f s).val.2 q) ((g t).val.2 q) t
        simpa only [holder_quotient_value,Pi.sub_apply,Pi.smul_apply] using! h
  exact hasDerivAt_of_norming_family (f := f) (g := g)
    (holderNormingEval (X := X) (F := F) (α := α))
    holderNormingEval_norm holderNormingEval_norming hU ha hg heval

end OAI.Analysis.PDE.Schauder
