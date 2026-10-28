import OAI.Analysis.Normed.Function.Holder.C2HolderConstruct
import OAI.Analysis.Normed.Function.Holder.Banach.Norm

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

namespace C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance normFirstDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance normFirstDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance normSecondDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance normSecondDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

@[simp] theorem value_sub (f g : C2Holder (F := F) hΩK α) :
    C2Holder.value (f - g) = C2Holder.value f - C2Holder.value g := rfl

@[simp] theorem firstDerivative_sub (f g : C2Holder (F := F) hΩK α) :
    C2Holder.firstDerivative (f - g) = C2Holder.firstDerivative f - C2Holder.firstDerivative g := rfl

@[simp] theorem secondDerivative_sub (f g : C2Holder (F := F) hΩK α) :
    C2Holder.secondDerivative (f - g) = C2Holder.secondDerivative f - C2Holder.secondDerivative g := rfl

/-- Uniform bounds on the actual jet and the Hessian's Hölder differences
control the Banach norm, in particular for differences of approximating solutions. -/
theorem norm_le_of_bounds (hα : 0 ≤ α) {C : ℝ} (hC : 0 ≤ C)
    (f : C2Holder (F := F) hΩK α)
    (h₀ : ∀ x, ‖C2Holder.value f x‖ ≤ C)
    (h₁ : ∀ x, ‖C2Holder.firstDerivative f x‖ ≤ C)
    (h₂ : ∀ x, ‖C2Holder.secondDerivative f x‖ ≤ C)
    (hh : ∀ x y, ‖C2Holder.secondDerivative f x - C2Holder.secondDerivative f y‖ ≤ C * (dist x y) ^ α) :
    ‖f‖ ≤ C := by
  have hb₀ : ‖f.val.1‖ ≤ C := (BoundedContinuousFunction.norm_le hC).mpr h₀
  have hb₁ : ‖f.val.2.1‖ ≤ C := (BoundedContinuousFunction.norm_le hC).mpr h₁
  have hb₂ : ‖f.val.2.2‖ ≤ C := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα hC _ h₂ hh
  exact max_le hb₀ (max_le hb₁ hb₂)

end C2Holder
end OAI.Analysis.Normed.Function.Holder
