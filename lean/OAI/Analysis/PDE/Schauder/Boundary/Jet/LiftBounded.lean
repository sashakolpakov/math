import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftEvaluation

noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder
variable {m : ℕ} {α R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance boundedLiftOpen : Fact (IsOpen (univ : Set E)) := ⟨isOpen_univ⟩

def globalC2Evaluation (x : E) : GlobalC2Holder m α →L[ℝ] ℝ :=
  LinearMap.mkContinuous {
    toFun := fun W ↦ OAI.Analysis.Normed.Function.Holder.fullValue W x
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
  } 1 (fun W ↦ by
    change ‖OAI.Analysis.Normed.Function.Holder.fullValue W x‖ ≤ 1 * ‖W‖
    simpa only [one_mul] using OAI.Analysis.Normed.Function.Holder.fullValue_norm_le W x)

@[simp] theorem globalC2Evaluation_apply (x : E) (W : GlobalC2Holder m α) :
    globalC2Evaluation x W = OAI.Analysis.Normed.Function.Holder.fullValue W x := rfl

theorem globalC2_ext {W V : GlobalC2Holder m α}
    (h : ∀ x, OAI.Analysis.Normed.Function.Holder.fullValue W x = OAI.Analysis.Normed.Function.Holder.fullValue V x) : W = V := by
  apply OAI.Analysis.Normed.Function.Holder.C2Holder.value_injective (by simp)
  apply BoundedContinuousFunction.ext
  intro x
  exact h x

def boundaryLift (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (hR : 0 < R) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) : GlobalC2Holder m α :=
  (exists_globalC2Holder_compactBoundaryLift hα hαone e he hR h).choose

theorem boundaryLift_value (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (hR : 0 < R) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (x : E) :
    OAI.Analysis.Normed.Function.Holder.fullValue (boundaryLift hα hαone e he hR h) x = compactBoundaryLift e R h x :=
  (exists_globalC2Holder_compactBoundaryLift hα hαone e he hR h).choose_spec x

def boundaryLiftLinear (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (hR : 0 < R) : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α →ₗ[ℝ] GlobalC2Holder m α where
  toFun := boundaryLift hα hαone e he hR
  map_add' := by
    intro h g
    apply globalC2_ext
    intro x
    change OAI.Analysis.Normed.Function.Holder.fullValue (boundaryLift hα hαone e he hR (h + g)) x =
      OAI.Analysis.Normed.Function.Holder.fullValue (boundaryLift hα hαone e he hR h) x + OAI.Analysis.Normed.Function.Holder.fullValue (boundaryLift hα hαone e he hR g) x
    simp only [boundaryLift_value, ← compactBoundaryLiftEvaluation_apply, map_add]
  map_smul' := by
    intro c h
    apply globalC2_ext
    intro x
    change OAI.Analysis.Normed.Function.Holder.fullValue (boundaryLift hα hαone e he hR (c • h)) x =
      c • OAI.Analysis.Normed.Function.Holder.fullValue (boundaryLift hα hαone e he hR h) x
    simp only [boundaryLift_value, ← compactBoundaryLiftEvaluation_apply, map_smul]

theorem continuous_boundaryLiftLinear (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (hR : 0 < R) :
    Continuous (boundaryLiftLinear hα hαone e he hR) := by
  apply LinearMap.continuous_of_seq_closed_graph
  intro u h W hu hW
  apply globalC2_ext
  intro x
  have ha := ((globalC2Evaluation (α := α) x).continuous.tendsto W).comp hW
  have hb := ((compactBoundaryLiftEvaluation (α := α) e R x).continuous.tendsto h).comp hu
  have heq : (fun n ↦ globalC2Evaluation x (boundaryLiftLinear hα hαone e he hR (u n))) =
      (fun n ↦ compactBoundaryLiftEvaluation e R x (u n)) := by
    funext n
    simp only [globalC2Evaluation_apply, compactBoundaryLiftEvaluation_apply]
    exact boundaryLift_value hα hαone e he hR (u n) x
  change Tendsto (fun n ↦ globalC2Evaluation x (boundaryLiftLinear hα hαone e he hR (u n)))
    atTop (𝓝 (globalC2Evaluation x W)) at ha
  rw [heq] at ha
  have hv := tendsto_nhds_unique ha hb
  simp only [globalC2Evaluation_apply, compactBoundaryLiftEvaluation_apply] at hv
  exact hv.trans (boundaryLift_value hα hαone e he hR h x).symm

/-- The actual compactly supported normal-jet lift is a bounded linear operator.
Boundedness follows by closed graph from its pointwise integral formula. -/
def boundaryLiftCLM (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (hR : 0 < R) : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α →L[ℝ] GlobalC2Holder m α :=
  ⟨boundaryLiftLinear hα hαone e he hR, continuous_boundaryLiftLinear hα hαone e he hR⟩

theorem boundaryLiftCLM_value (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (hR : 0 < R) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (x : E) :
    OAI.Analysis.Normed.Function.Holder.fullValue (boundaryLiftCLM hα hαone e he hR h) x = compactBoundaryLift e R h x :=
  boundaryLift_value hα hαone e he hR h x

end OAI.Analysis.PDE.Schauder
