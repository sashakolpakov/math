import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderBound
import OAI.Analysis.Normed.Function.Holder.C2HolderNorm
import OAI.Analysis.Normed.Function.Holder.C2HolderExt

/-! The closed Banach space of Hölder data supported in a fixed ball. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def supportedHolderSubmodule (m : ℕ) (α R : ℝ) :
    Submodule ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) where
  carrier := {f | ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value f x = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x hx; simp [hf x hx, hg x hx]
  smul_mem' := by intro c f hf x hx; simp [hf x hx]

abbrev SupportedHolder (m : ℕ) (α R : ℝ) := ↥(supportedHolderSubmodule m α R)

instance instSupportedHolderNormedGroup (m : ℕ) (α R : ℝ) :
    NormedAddCommGroup (SupportedHolder m α R) := inferInstance

instance instSupportedHolderNormedSpace (m : ℕ) (α R : ℝ) :
    NormedSpace ℝ (SupportedHolder m α R) := inferInstance

theorem isClosed_supportedHolderSubmodule (m : ℕ) (α R : ℝ) :
    IsClosed (supportedHolderSubmodule m α R : Set (OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)) := by
  change IsClosed {f : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α |
    ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value f x = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _hx
  exact isClosed_eq ((OAI.Analysis.Normed.Function.Holder.boundedEvaluation x).continuous.comp OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM.continuous) continuous_const

instance (m : ℕ) (α R : ℝ) : CompleteSpace (SupportedHolder m α R) :=
  (isClosed_supportedHolderSubmodule m α R).isComplete.completeSpace_coe

namespace SupportedHolder

variable {m : ℕ} {α R : ℝ}

def value (f : SupportedHolder m α R) : EuclideanSpace ℝ (Fin m) → ℝ :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val

theorem continuous (f : SupportedHolder m α R) : Continuous (SupportedHolder.value f) :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val).continuous

theorem support_subset (f : SupportedHolder m α R) :
    Function.support (SupportedHolder.value f) ⊆ closedBall 0 R := by
  intro x hx
  by_contra hc
  exact hx (f.property x hc)

theorem hasCompactSupport (f : SupportedHolder m α R) : HasCompactSupport (SupportedHolder.value f) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) (SupportedHolder.support_subset f)

theorem support_subset_ball (f : SupportedHolder m α R) :
    Function.support (SupportedHolder.value f) ⊆ ball 0 (R + 1) :=
  (SupportedHolder.support_subset f).trans (closedBall_subset_ball (by linarith))

theorem norm_value_le (f : SupportedHolder m α R) (x) : |SupportedHolder.value f x| ≤ ‖f‖ :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f.val x

theorem holder (f : SupportedHolder m α R) (x y) :
    |SupportedHolder.value f x - SupportedHolder.value f y| ≤ ‖f‖ * ‖x - y‖ ^ α := by
  change |OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val x - OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val y| ≤ ‖f.val‖ * ‖x - y‖ ^ α
  simpa only [SupportedHolder.value, Real.norm_eq_abs, dist_eq_norm] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f.val x y

@[simp] theorem value_add (f g : SupportedHolder m α R) : SupportedHolder.value (f + g) = SupportedHolder.value f + SupportedHolder.value g := rfl
@[simp] theorem value_smul (c : ℝ) (f : SupportedHolder m α R) : SupportedHolder.value (c • f) = c • SupportedHolder.value f := rfl

end SupportedHolder

abbrev GlobalC2Holder (m : ℕ) (α : ℝ) :=
  OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) (show (univ : Set (EuclideanSpace ℝ (Fin m))) ⊆ univ from Subset.rfl) α

instance instGlobalC2HolderNormedGroup (m : ℕ) (α : ℝ) :
    NormedAddCommGroup (GlobalC2Holder m α) := inferInstance

instance instGlobalC2HolderNormedSpace (m : ℕ) (α : ℝ) :
    NormedSpace ℝ (GlobalC2Holder m α) := inferInstance

end OAI.Analysis.PDE.Schauder
