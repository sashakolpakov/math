import OAI.Analysis.Normed.Function.Holder.Boundary.ChartJets
import OAI.Analysis.PDE.Elliptic.Boundary.CommutatorHolder

/-! The genuine vector-field commutator has a uniformly controlled
Hölder extension to a closed chart for every bounded C²,α potential.
No third derivatives of the potential occur in the bound. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Ω K S : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance sourceFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance sourceFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance sourceSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceFieldGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance sourceFieldSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance sourceFieldSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceFieldSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem exists_chart_commutator_holder_interior (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hconv : Convex ℝ S)
    {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ x ∈ closure S, ‖fderiv ℝ G x‖ ≤ L)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (A J : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E) α)
    (T₂ : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E) α)
    (a : E → E →L[ℝ] E) (T : E → E)
    (hA : ∀ x, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A ⟨x, subset_closure hx⟩ = a (G x))
    (hJ : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ T (G x))
    (hT₂ : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T₂ x = fderiv ℝ (fderiv ℝ T) (G x)) :
    ∃ R : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) ℝ α,
      (∀ x : E, ∀ hx : x ∈ S,
        OAI.Analysis.Normed.Function.Holder.HolderMap.value R ⟨x, subset_closure hx⟩ =
          fieldCommutator a (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) T (G x)) ∧
      ‖R‖ ≤ Module.finrank ℝ E *
        (8 * (max 1 (L^α) * ‖U‖) * ‖A‖ * ‖J‖ +
          4 * (max 1 L * ‖U‖) * ‖A‖ * ‖T₂‖) := by
  obtain ⟨D, hD, hnD⟩ := U.exists_chart_first_holder hS hconv hG hGK hGΩ
    hL hDG hα hα1 hdiam
  have hLip : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖G x-G y‖ ≤ L*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hG.differentiable one_ne_zero z) hDG hconv.closure hy hx
  obtain ⟨H, hH, hnH⟩ := U.exists_chart_second_holder hG.continuous hGK hL hLip hα
  refine ⟨holderFieldCommutator hα D H A J T₂, ?_, ?_⟩
  · intro x hx
    rw [value_holderFieldCommutator]
    have hj := U.genuine_derivatives hΩ (hGΩ hx)
    simp only [hD, hH, hA x hx, hJ, hT₂, fieldCommutator, hj.1, hj.2]
  · apply (holderFieldCommutator_norm_le hα D H A J T₂).trans
    gcongr

theorem exists_chart_commutator_holder (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hconv : Convex ℝ S)
    {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ x ∈ closure S, ‖fderiv ℝ G x‖ ≤ L)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (A J : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E) α)
    (T₂ : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E) α)
    (a : E → E →L[ℝ] E) (T : E → E)
    (hA : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = a (G x))
    (hJ : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ T (G x))
    (hT₂ : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T₂ x = fderiv ℝ (fderiv ℝ T) (G x)) :
    ∃ R : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) ℝ α,
      (∀ x : E, ∀ hx : x ∈ S,
        OAI.Analysis.Normed.Function.Holder.HolderMap.value R ⟨x, subset_closure hx⟩ =
          fieldCommutator a (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) T (G x)) ∧
      ‖R‖ ≤ Module.finrank ℝ E *
        (8 * (max 1 (L^α) * ‖U‖) * ‖A‖ * ‖J‖ +
          4 * (max 1 L * ‖U‖) * ‖A‖ * ‖T₂‖) :=
  exists_chart_commutator_holder_interior U hΩ hS hconv hG hGK hGΩ hL hDG
    hα hα1 hdiam A J T₂ a T (fun x hx => hA ⟨x, subset_closure hx⟩) hJ hT₂

end OAI.Analysis.PDE.Elliptic
