import OAI.Analysis.PDE.Dirichlet.CoordinateTransport
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback
import OAI.Analysis.Normed.Function.Holder.Banach.Linear
import Mathlib.Analysis.Matrix.Normed

open Set Metric
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

local instance matrixTransportINormedGroup : NormedAddCommGroup (Matrix I I ℝ) :=
  inferInstanceAs (NormedAddCommGroup (I → I → ℝ))
local instance matrixTransportINormedSpace : NormedSpace ℝ (Matrix I I ℝ) :=
  inferInstanceAs (NormedSpace ℝ (I → I → ℝ))
local instance matrixTransportJNormedGroup : NormedAddCommGroup (Matrix J J ℝ) :=
  inferInstanceAs (NormedAddCommGroup (J → J → ℝ))
local instance matrixTransportJNormedSpace : NormedSpace ℝ (Matrix J J ℝ) :=
  inferInstanceAs (NormedSpace ℝ (J → J → ℝ))
local instance matrixTransportMapNormedGroup :
    NormedAddCommGroup (Matrix J J ℝ →L[ℝ] Matrix I I ℝ) :=
  inferInstanceAs (NormedAddCommGroup ((J → J → ℝ) →L[ℝ] (I → I → ℝ)))

def matrixReindexLinear (e : I ≃ J) : Matrix J J ℝ →ₗ[ℝ] Matrix I I ℝ where
  toFun A i j := A (e i) (e j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq I] [DecidableEq J] in
theorem norm_matrixReindex_le (e : I ≃ J) (A : Matrix J J ℝ) :
    ‖matrixReindexLinear e A‖ ≤ ‖A‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg A)).mpr
  intro i j
  exact Matrix.norm_entry_le_entrywise_sup_norm A

def matrixReindexCLM (e : I ≃ J) : Matrix J J ℝ →L[ℝ] Matrix I I ℝ :=
  (matrixReindexLinear e).mkContinuous 1 (fun A ↦ by simpa using norm_matrixReindex_le e A)

omit [DecidableEq I] [DecidableEq J] in
theorem norm_matrixReindexCLM_le (e : I ≃ J) : ‖matrixReindexCLM e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖matrixReindexLinear e A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using norm_matrixReindex_le e A

omit [DecidableEq I] [DecidableEq J] in
theorem matrixReindex_posDef (e : I ≃ J) {A : Matrix J J ℝ} (hA : A.PosDef) :
    (matrixReindexCLM e A).PosDef := hA.submatrix e.injective

/-- Transport both the argument and the coefficient indices. This preserves
the C^α norm bound used by the small-perturbation inverse. -/
def coefficientReindex {α : ℝ} (hα : 0 ≤ α) (e : I ≃ J)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ J) (Matrix J J ℝ) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) (Matrix I I ℝ) α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.map (matrixReindexCLM e)
    (OAI.Analysis.PDE.Schauder.holderIsometricPullback hα (coordinateReindex e) (coordinateReindex e).isometry A)

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem coefficientReindex_apply {α : ℝ} (hα : 0 ≤ α) (e : I ≃ J)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ J) (Matrix J J ℝ) α)
    (x : EuclideanSpace ℝ I) (i j : I) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (coefficientReindex hα e A) x i j =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value A (coordinateReindex e x) (e i) (e j) := rfl

omit [DecidableEq I] [DecidableEq J] in
theorem norm_coefficientReindex_le {α : ℝ} (hα : 0 ≤ α) (e : I ≃ J)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ J) (Matrix J J ℝ) α) :
    ‖coefficientReindex hα e A‖ ≤ ‖A‖ := by
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le _ _).trans
  calc
    _ ≤ 1 * ‖OAI.Analysis.PDE.Schauder.holderIsometricPullback hα (coordinateReindex e) (coordinateReindex e).isometry A‖ :=
      mul_le_mul_of_nonneg_right (norm_matrixReindexCLM_le e) (norm_nonneg _)
    _ ≤ ‖A‖ := by
      rw [one_mul]
      exact OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα _ _ A

omit [DecidableEq I] [DecidableEq J] in
theorem coefficientReindex_supported {α R : ℝ} (hα : 0 ≤ α) (e : I ≃ J)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ J) (Matrix J J ℝ) α)
    (hA : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = 0) :
    ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value (coefficientReindex hα e A) x = 0 := by
  intro x hx
  have he : coordinateReindex e x ∉ closedBall 0 R := by
    simpa only [mem_closedBall, dist_zero_right, (coordinateReindex e).norm_map] using hx
  apply Matrix.ext
  intro i j
  rw [coefficientReindex_apply, hA _ he]
  rfl

end OAI.Analysis.PDE.Dirichlet
