import OAI.Analysis.Normed.Function.Holder.Boundary.LowerJetHolder

/-! Subtracting the fixed boundary datum at third order. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance thirdSubFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdSubFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdSubSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdSubSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdSubThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdSubThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_fixed_third_holder [ProperSpace E] {K : Set E} (hK : IsCompact K)
    (u : E → ℝ) (hu : ContDiff ℝ 4 u) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) := h₂.fderiv_right (by norm_num)
  exact OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hK _ h₃ hα hα1

theorem third_fderiv_sub {u v : E → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) (x : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u y-v y))) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x := by
  have hu₁ : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hv₁ : ContDiff ℝ 2 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hu₂ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := hu₁.fderiv_right (by norm_num)
  have hv₂ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ v)) := hv₁.fderiv_right (by norm_num)
  have h₁ : fderiv ℝ (fun y => u y-v y) = fun y => fderiv ℝ u y-fderiv ℝ v y := by
    funext y
    exact fderiv_sub (hu.differentiable (by norm_num) y) (hv.differentiable (by norm_num) y)
  have h₂ : fderiv ℝ (fun y => fderiv ℝ u y-fderiv ℝ v y) =
      fun y => fderiv ℝ (fderiv ℝ u) y-fderiv ℝ (fderiv ℝ v) y := by
    funext y
    exact fderiv_sub (hu₁.differentiable (by norm_num) y) (hv₁.differentiable (by norm_num) y)
  rw [h₁, h₂]
  exact fderiv_sub (hu₂.differentiable one_ne_zero x) (hv₂.differentiable one_ne_zero x)

theorem subtracted_third_holder {K : Set E} {α : ℝ} {u v : E → ℝ}
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (T B : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hT : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x)
    (hB : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x) :
    (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T-B) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u y-v y))) x) ∧ ‖T-B‖ ≤ ‖T‖+‖B‖ := by
  refine ⟨?_, norm_sub_le T B⟩
  intro x
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value T x-OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = _
  rw [hT, hB, third_fderiv_sub hu hv]

theorem exists_subtracted_third_holder {K : Set E} {α : ℝ} {u v : E → ℝ}
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (T B : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hT : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x)
    (hB : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x) :
    ∃ P : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u y-v y))) x) ∧
      ‖P‖ ≤ ‖T‖+‖B‖ :=
  ⟨T-B, subtracted_third_holder hu hv T B hT hB⟩

theorem exists_restored_third_holder {K : Set E} {α : ℝ} {u v : E → ℝ}
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (T B : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hT : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u y-v y))) x)
    (hB : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x) :
    ∃ P : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) ∧
      ‖P‖ ≤ ‖T‖+‖B‖ := by
  refine ⟨T+B, ?_, norm_add_le T B⟩
  intro x
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value T x+OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = _
  rw [hT, hB, third_fderiv_sub hu hv]
  exact sub_add_cancel _ _

theorem third_background_bound {C q R S p : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hp : p ≤ C*(R+S)) :
    p+q ≤ (C+q+1)*(1+R+S) := by
  nlinarith

end OAI.Analysis.PDE.Elliptic
