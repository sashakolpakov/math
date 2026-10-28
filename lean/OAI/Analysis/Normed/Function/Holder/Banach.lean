import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

abbrev DistinctPairs (X : Type*) := {p : X × X // p.1 ≠ p.2}

variable (X F : Type*) [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Hölder function together with its bounded continuous difference quotient.
The graph norm is the maximum of the supremum norm and the Hölder seminorm. -/
def holderGraph (α : ℝ) : Submodule ℝ ((X →ᵇ F) × (DistinctPairs X →ᵇ F)) where
  carrier := {p | ∀ q : DistinctPairs X,
    (dist q.val.1 q.val.2) ^ α • p.2 q = p.1 q.val.1 - p.1 q.val.2}
  zero_mem' := by simp
  add_mem' := by
    intro p r hp hr q
    change (dist q.val.1 q.val.2) ^ α • (p.2 q + r.2 q) =
      (p.1 q.val.1 + r.1 q.val.1) - (p.1 q.val.2 + r.1 q.val.2)
    rw [smul_add, hp q, hr q]
    abel
  smul_mem' := by
    intro c p hp q
    change (dist q.val.1 q.val.2) ^ α • (c • p.2 q) =
      c • p.1 q.val.1 - c • p.1 q.val.2
    rw [smul_comm, hp q, smul_sub]

abbrev HolderMap (α : ℝ) : Type _ := ↥(holderGraph X F α)

variable {X F}

def boundedEvaluation (x : X) : (X →ᵇ F) →L[ℝ] F :=
  BoundedContinuousFunction.evalCLM ℝ x

theorem isClosed_holderGraph (α : ℝ) :
    IsClosed (holderGraph X F α : Set ((X →ᵇ F) × (DistinctPairs X →ᵇ F))) := by
  change IsClosed {p : (X →ᵇ F) × (DistinctPairs X →ᵇ F) | ∀ q : DistinctPairs X,
    (dist q.val.1 q.val.2) ^ α • p.2 q = p.1 q.val.1 - p.1 q.val.2}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro q
  exact isClosed_eq
    (((boundedEvaluation q).continuous.comp continuous_snd).const_smul _)
    (((boundedEvaluation q.val.1).continuous.comp continuous_fst).sub
      ((boundedEvaluation q.val.2).continuous.comp continuous_fst))

instance {α : ℝ} [CompleteSpace F] : CompleteSpace (HolderMap X F α) :=
  (isClosed_holderGraph (X := X) (F := F) α).isComplete.completeSpace_coe

namespace HolderMap

variable {α : ℝ}

def value (f : HolderMap X F α) : X →ᵇ F := f.val.1

theorem value_norm_le (f : HolderMap X F α) : ‖HolderMap.value f‖ ≤ ‖f‖ :=
  le_max_left _ _

theorem norm_value_le (f : HolderMap X F α) (x : X) : ‖HolderMap.value f x‖ ≤ ‖f‖ :=
  ((HolderMap.value f).norm_coe_le_norm x).trans (HolderMap.value_norm_le f)

theorem norm_sub_le (f : HolderMap X F α) (x y : X) :
    ‖HolderMap.value f x - HolderMap.value f y‖ ≤ ‖f‖ * (dist x y) ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    positivity
  let q : DistinctPairs X := ⟨(x, y), hxy⟩
  have hq : (dist x y) ^ α • f.val.2 q = f.val.1 x - f.val.1 y := f.property q
  have hweight : 0 ≤ (dist x y) ^ α := Real.rpow_nonneg dist_nonneg _
  change ‖f.val.1 x - f.val.1 y‖ ≤ _
  rw [← hq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hweight]
  have hbound : ‖f.val.2 q‖ ≤ ‖f‖ :=
    (f.val.2.norm_coe_le_norm q).trans (le_max_right _ _)
  exact (mul_le_mul_of_nonneg_left hbound hweight).trans_eq (mul_comm _ _)

end HolderMap
end OAI.Analysis.Normed.Function.Holder
