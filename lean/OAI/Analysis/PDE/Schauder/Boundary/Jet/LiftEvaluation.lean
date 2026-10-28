import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftCompact
import OAI.Analysis.Normed.Function.Holder.C2HolderIsometry
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
open _root_.MeasureTheory Set
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder
variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem regularizedTrace_holder_add (h g : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (t : ℝ) (z : E) :
    regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value (h + g)) t z =
      regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) t z + regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value g) t z := by
  change (∫ y, (boundaryMollifier m).normed volume y *
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value h (z - t • y) + OAI.Analysis.Normed.Function.Holder.HolderMap.value g (z - t • y))) = _
  simp only [mul_add]
  exact integral_add (integrable_regularizedTrace _ (OAI.Analysis.Normed.Function.Holder.HolderMap.value h).continuous t z)
    (integrable_regularizedTrace _ (OAI.Analysis.Normed.Function.Holder.HolderMap.value g).continuous t z)

theorem regularizedTrace_holder_smul (c : ℝ) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (t : ℝ) (z : E) :
    regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value (c • h)) t z =
      c * regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) t z := by
  change (∫ y, (boundaryMollifier m).normed volume y *
    (c * OAI.Analysis.Normed.Function.Holder.HolderMap.value h (z - t • y))) = _
  simp only [mul_left_comm _ c]
  exact integral_const_mul c _

def regularizedTraceEvaluation (t : ℝ) (z : E) : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α →L[ℝ] ℝ :=
  LinearMap.mkContinuous {
    toFun := fun h ↦ regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) t z
    map_add' := fun h g ↦ regularizedTrace_holder_add h g t z
    map_smul' := fun c h ↦ regularizedTrace_holder_smul c h t z
  } 1 (fun h ↦ by
    change ‖regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) t z‖ ≤ 1 * ‖h‖
    simpa only [one_mul, Real.norm_eq_abs] using norm_regularizedTrace_le h t z)

@[simp] theorem regularizedTraceEvaluation_apply (t : ℝ) (z : E) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) :
    regularizedTraceEvaluation t z h = regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) t z := rfl

def compactBoundaryLiftEvaluation (e : E) (R : ℝ) (x : E) : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α →L[ℝ] ℝ :=
  (radialCutoff R x * (inner ℝ e x) ^ 2 / 2) •
    regularizedTraceEvaluation (inner ℝ e x) (normalProjection e x)

@[simp] theorem compactBoundaryLiftEvaluation_apply (e : E) (R : ℝ) (x : E)
    (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) :
    compactBoundaryLiftEvaluation e R x h = compactBoundaryLift e R h x := by
  simp only [compactBoundaryLiftEvaluation, smul_apply, smul_eq_mul,
    regularizedTraceEvaluation_apply, compactBoundaryLift, regularizedBoundaryLift]
  ring

end OAI.Analysis.PDE.Schauder
