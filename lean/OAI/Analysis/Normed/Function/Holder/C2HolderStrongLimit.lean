import OAI.Analysis.Normed.Function.Holder.C2HolderCompactLimit
import OAI.Analysis.Normed.Function.Holder.C2HolderNorm

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α β M : ℝ}

local instance strongFirstNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance strongFirstNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance strongSecondNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance strongSecondNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Pointwise convergence of all three jets retains the original Hölder
exponent and bound. Convergence in that stronger norm is not asserted. -/
theorem exists_original_exponent_of_jet_limit (hα : 0 ≤ α) (hM : 0 ≤ M)
    (f : ℕ → C2Holder (F := F) hΩK α) (g : C2Holder (F := F) hΩK β)
    (hf : ∀ k, ‖f k‖ ≤ M)
    (hv : ∀ x : K, Tendsto (fun k ↦ C2Holder.value (f k) x) atTop (𝓝 (C2Holder.value g x)))
    (hG : ∀ x : K, Tendsto (fun k ↦ C2Holder.firstDerivative (f k) x) atTop
      (𝓝 (C2Holder.firstDerivative g x)))
    (hH : ∀ x : K, Tendsto (fun k ↦ C2Holder.secondDerivative (f k) x) atTop
      (𝓝 (C2Holder.secondDerivative g x))) :
    ∃ u : C2Holder (F := F) hΩK α, ‖u‖ ≤ M ∧
      C2Holder.value u = C2Holder.value g ∧ C2Holder.firstDerivative u = C2Holder.firstDerivative g ∧
      C2Holder.secondDerivative u = C2Holder.secondDerivative g := by
  have hb₀ (x : K) : ‖C2Holder.value g x‖ ≤ M := by
    apply le_of_tendsto (hv x).norm
    exact Eventually.of_forall fun k ↦ ((C2Holder.value (f k)).norm_coe_le_norm x).trans
      ((C2Holder.norm_value_le (f k)).trans (hf k))
  have hb₁ (x : K) : ‖C2Holder.firstDerivative g x‖ ≤ M := by
    apply le_of_tendsto (hG x).norm
    exact Eventually.of_forall fun k ↦ ((C2Holder.firstDerivative (f k)).norm_coe_le_norm x).trans
      ((C2Holder.norm_firstDerivative_le (f k)).trans (hf k))
  have hb₂ (x : K) : ‖C2Holder.secondDerivative g x‖ ≤ M := by
    apply le_of_tendsto (hH x).norm
    exact Eventually.of_forall fun k ↦ (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le (C2Holder.hessianCLM (f k)) x).trans
      ((C2Holder.norm_hessianCLM_apply_le (f k)).trans (hf k))
  have hh (x y : K) : ‖C2Holder.secondDerivative g x - C2Holder.secondDerivative g y‖ ≤
      M * dist x y ^ α := by
    apply le_of_tendsto ((hH x).sub (hH y)).norm
    exact Eventually.of_forall fun k ↦ (C2Holder.secondDerivative_holder (f k) x y).trans
      (mul_le_mul_of_nonneg_right (hf k) (Real.rpow_nonneg dist_nonneg _))
  let u : C2Holder (F := F) hΩK α :=
    ⟨(C2Holder.value g, C2Holder.firstDerivative g, OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα (C2Holder.secondDerivative g) hh), g.property⟩
  refine ⟨u, ?_, rfl, rfl, rfl⟩
  exact C2Holder.norm_le_of_bounds hα hM u hb₀ hb₁ hb₂ hh

theorem jet_value_tendsto {f : ℕ → C2Holder (F := F) hΩK β}
    {g : C2Holder (F := F) hΩK β} (h : Tendsto f atTop (𝓝 g)) (x : K) :
    Tendsto (fun k ↦ C2Holder.value (f k) x) atTop (𝓝 (C2Holder.value g x)) := by
  have ht := ((C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := β)).continuous.tendsto g).comp h
  exact ((BoundedContinuousFunction.evalCLM ℝ x : (K →ᵇ F) →L[ℝ] F).continuous.tendsto
    (C2Holder.value g)).comp ht

theorem jet_first_tendsto {f : ℕ → C2Holder (F := F) hΩK β}
    {g : C2Holder (F := F) hΩK β} (h : Tendsto f atTop (𝓝 g)) (x : K) :
    Tendsto (fun k ↦ C2Holder.firstDerivative (f k) x) atTop (𝓝 (C2Holder.firstDerivative g x)) := by
  have ht := ((C2Holder.firstDerivativeCLM (F := F) (hΩK := hΩK) (α := β)).continuous.tendsto g).comp h
  exact ((BoundedContinuousFunction.evalCLM ℝ x :
    (K →ᵇ (E →L[ℝ] F)) →L[ℝ] (E →L[ℝ] F)).continuous.tendsto
    (C2Holder.firstDerivative g)).comp ht

theorem jet_second_tendsto {f : ℕ → C2Holder (F := F) hΩK β}
    {g : C2Holder (F := F) hΩK β} (h : Tendsto f atTop (𝓝 g)) (x : K) :
    Tendsto (fun k ↦ C2Holder.secondDerivative (f k) x) atTop (𝓝 (C2Holder.secondDerivative g x)) := by
  have ht := ((C2Holder.secondDerivativeCLM (F := F) (hΩK := hΩK) (α := β)).continuous.tendsto g).comp h
  exact ((BoundedContinuousFunction.evalCLM ℝ x :
    (K →ᵇ (E →L[ℝ] E →L[ℝ] F)) →L[ℝ] (E →L[ℝ] E →L[ℝ] F)).continuous.tendsto
    (C2Holder.secondDerivative g)).comp ht

/-- A lower-Hölder compactness limit retains the uniform original Schauder
bound. This is the strong-space membership needed for approximating data. -/
theorem exists_original_exponent_of_lowerHalf_limit (hα : 0 ≤ α) (hM : 0 ≤ M)
    (f : ℕ → C2Holder (F := F) hΩK α) (g : C2Holder (F := F) hΩK (α / 2))
    (hf : ∀ k, ‖f k‖ ≤ M)
    (hlim : Tendsto (fun k ↦ C2Holder.lowerHalf hα (f k)) atTop (𝓝 g)) :
    ∃ u : C2Holder (F := F) hΩK α, ‖u‖ ≤ M ∧ C2Holder.lowerHalf hα u = g := by
  have hv (x : K) : Tendsto (fun k ↦ C2Holder.value (f k) x) atTop (𝓝 (C2Holder.value g x)) := by
    simpa only [C2Holder.value_lowerHalf] using C2Holder.jet_value_tendsto hlim x
  have hG (x : K) : Tendsto (fun k ↦ C2Holder.firstDerivative (f k) x) atTop
      (𝓝 (C2Holder.firstDerivative g x)) := by
    simpa only [C2Holder.firstDerivative_lowerHalf] using C2Holder.jet_first_tendsto hlim x
  have hH (x : K) : Tendsto (fun k ↦ C2Holder.secondDerivative (f k) x) atTop
      (𝓝 (C2Holder.secondDerivative g x)) := by
    simpa only [C2Holder.secondDerivative_lowerHalf] using C2Holder.jet_second_tendsto hlim x
  obtain ⟨u, hu, huv, huG, huH⟩ :=
    C2Holder.exists_original_exponent_of_jet_limit hα hM f g hf hv hG hH
  refine ⟨u, hu, ?_⟩
  apply Subtype.ext
  exact Prod.ext huv (Prod.ext huG (OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective huH))

end OAI.Analysis.Normed.Function.Holder.C2Holder
