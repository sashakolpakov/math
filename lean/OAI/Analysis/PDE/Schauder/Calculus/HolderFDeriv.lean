import OAI.Analysis.PDE.Schauder.Calculus.NormingFDeriv
import OAI.Analysis.PDE.Schauder.Calculus.HolderDerivative

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {X Z F : Type*} [MetricSpace X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

local instance frechetHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance
local instance frechetHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance

theorem hasFDerivAt_holder_of_pointwise
    {f : Z → OAI.Analysis.Normed.Function.Holder.HolderMap X F α} {g : Z → Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X F α}
    {U : Set Z} (hU : IsOpen U) {a : Z} (ha : a ∈ U) (hg : ContinuousAt g a)
    (hd : ∀ t ∈ U, ∀ x, HasFDerivAt (fun s => OAI.Analysis.Normed.Function.Holder.HolderMap.value (f s) x)
      (((OAI.Analysis.Normed.Function.Holder.boundedEvaluation x).comp OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM).comp (g t)) t) :
    HasFDerivAt f (g a) a := by
  have heval : ∀ t ∈ U, ∀ i : X ⊕ OAI.Analysis.Normed.Function.Holder.DistinctPairs X,
      HasFDerivAt (fun s => holderNormingEval i (f s)) ((holderNormingEval i).comp (g t)) t := by
    intro t ht i
    cases i with
    | inl x => exact hd t ht x
    | inr q =>
      have h := ((hd t ht q.val.1).sub (hd t ht q.val.2)).const_smul
        ((dist q.val.1 q.val.2 ^ α)⁻¹)
      have he : (fun s => holderNormingEval (Sum.inr q) (f s)) =
          (fun s => (dist q.val.1 q.val.2 ^ α)⁻¹ •
            (OAI.Analysis.Normed.Function.Holder.HolderMap.value (f s) q.val.1-OAI.Analysis.Normed.Function.Holder.HolderMap.value (f s) q.val.2)) := by
        funext s
        exact holder_quotient_value (f s) q
      rw [he]
      convert h using 1
      ext z
      exact holder_quotient_value (g t z) q
  exact hasFDerivAt_of_norming_family (f := f) (g := g)
    (holderNormingEval (X := X) (F := F) (α := α))
    holderNormingEval_norm holderNormingEval_norming hU ha hg heval

end OAI.Analysis.PDE.Schauder
