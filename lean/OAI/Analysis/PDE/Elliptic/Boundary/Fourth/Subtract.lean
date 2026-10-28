import OAI.Analysis.PDE.Elliptic.Boundary.Third.Subtract
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Tensor

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

private theorem exists_add_holder_bound {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α M : ℝ}
    (T B : OAI.Analysis.Normed.Function.Holder.HolderMap X F α) (hT : ‖T‖ ≤ M) :
    ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap X F α, (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x = OAI.Analysis.Normed.Function.Holder.HolderMap.value T x+OAI.Analysis.Normed.Function.Holder.HolderMap.value B x) ∧
      ‖Q‖ ≤ M+‖B‖ :=
  ⟨T+B,fun _ => rfl,(norm_add_le T B).trans (add_le_add hT le_rfl)⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance fourthSub1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthSub1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthSub2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthSub2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthSub3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthSub3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthSub4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthSub4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_fixed_fourth_holder [ProperSpace E] {K : Set E} (hK : IsCompact K)
    (u : E → ℝ) (hu : ContDiff ℝ 5 u) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x := by
  have h₁ : ContDiff ℝ 4 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 3 (fderiv ℝ (fderiv ℝ u)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) := h₂.fderiv_right (by norm_num)
  have h₄ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u)))) :=
    h₃.fderiv_right (by norm_num)
  exact OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hK _ h₄ hα hα1

theorem fourth_fderiv_sub {u v : E → ℝ} (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 4 v) (x : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u y-v y)))) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ v))) x := by
  have hu₁ : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hv₁ : ContDiff ℝ 3 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hu₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := hu₁.fderiv_right (by norm_num)
  have hv₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ v)) := hv₁.fderiv_right (by norm_num)
  have hu₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) := hu₂.fderiv_right (by norm_num)
  have hv₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ v))) := hv₂.fderiv_right (by norm_num)
  have heq : fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u y-v y))) =
      fun y => fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y-fderiv ℝ (fderiv ℝ (fderiv ℝ v)) y := by
    funext y
    exact third_fderiv_sub (hu.of_le (by norm_num)) (hv.of_le (by norm_num)) y
  rw [heq]
  exact fderiv_sub (hu₃.differentiable one_ne_zero x) (hv₃.differentiable one_ne_zero x)

theorem restored_fourth_holder {K : Set E} {α M : ℝ} {u v : E → ℝ}
    (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 4 v)
    (hT : HasFourthHolderBound K α (fun y => u y-v y) M)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hB : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ v))) x) :
    HasFourthHolderBound K α u (M+‖B‖) := by
  obtain ⟨T,hT,hTn⟩ := hT
  obtain ⟨Q,hQ,hQn⟩ := exists_add_holder_bound T B hTn
  refine ⟨Q,?_,hQn⟩
  intro x
  rw [hQ,hT,hB,fourth_fderiv_sub hu hv]
  exact sub_add_cancel _ _

end OAI.Analysis.PDE.Elliptic
