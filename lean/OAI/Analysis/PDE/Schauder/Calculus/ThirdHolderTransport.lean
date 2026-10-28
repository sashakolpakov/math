import OAI.Analysis.PDE.Schauder.Calculus.ThirdIsometry

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

local instance transFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance transFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance transSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance transSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance transThirdGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance transThirdSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Restriction and isometric pullback of an actual third jet do not
increase its Hölder norm. -/
theorem exists_third_holder_isometry (e : E ≃ₗᵢ[ℝ] F) {K : Set F} {α : ℝ}
    (hα : 0 ≤ α) (u : F → ℝ) (hu : ContDiff ℝ 4 u)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap K (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) α)
    (hT : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) :
    ∃ T' : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' K) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      ‖T'‖ ≤ ‖T‖ ∧ ∀ x : e ⁻¹' K,
        OAI.Analysis.Normed.Function.Holder.HolderMap.value T' x = fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x := by
  have hu3 : ContDiff ℝ 3 u := hu.of_le (by norm_num)
  have hc : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e)))) :=
    ((((hu.comp e.contDiff).fderiv_right (m := 3) (by norm_num)).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuous
  have hn x (hx : x ∈ e ⁻¹' K) :
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x‖ ≤ ‖T‖ := by
    rw [norm_third_isometry_comp e u hu3, ← hT ⟨e x,hx⟩]
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le T _
  let v := OAI.Analysis.Normed.Function.Holder.boundedRestriction (fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e)))) hc.continuousOn ‖T‖ hn
  have hh (x y : e ⁻¹' K) : ‖v x-v y‖ ≤ ‖T‖*(dist x y)^α := by
    change ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x-
      fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) y‖ ≤ _
    rw [norm_third_sub_isometry_comp e u hu3, ← hT ⟨e x,x.property⟩, ← hT ⟨e y,y.property⟩]
    simpa only [Subtype.dist_eq,e.isometry.dist_eq] using
      OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le T ⟨e x,x.property⟩ ⟨e y,y.property⟩
  let T' := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα v hh
  refine ⟨T', ?_, fun _ => rfl⟩
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (norm_nonneg _)
  · intro x
    exact hn x x.property
  · exact hh

end OAI.Analysis.PDE.Schauder
