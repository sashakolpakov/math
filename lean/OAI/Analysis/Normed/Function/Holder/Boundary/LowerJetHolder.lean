import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationJets
import OAI.Analysis.Normed.Function.Holder.Boundary.HolderPullback

/-! Actual local derivative bounds as Hölder fields. -/

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
theorem exists_holder_field_of_bounds {S : Set E} {α M : ℝ}
    (hα : 0 ≤ α) (hM : 0 ≤ M) (f : E → F) (hf : ContinuousOn f S)
    (hn : ∀ x ∈ S, ‖f x‖ ≤ M)
    (hh : ∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤ M*‖x-y‖^α) :
    ∃ P : HolderMap S F α, (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x = f x) ∧ ‖P‖ ≤ M := by
  let b : S →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f x) hf.domRestrict M (fun x => hn x x.property)
  have hb (x y : S) : ‖b x-b y‖ ≤ M*dist x y^α := by
    change ‖f x-f y‖ ≤ M*dist x y^α
    simpa only [Subtype.dist_eq, dist_eq_norm] using hh x x.property y y.property
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα b hb, fun _ => rfl, ?_⟩
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα b hM hb).trans
    (max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM _) le_rfl)

theorem exists_fixed_holder_on_compact [ProperSpace E] {S : Set E}
    (hS : IsCompact S) (f : E → F) (hf : ContDiff ℝ 1 f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ P : HolderMap S F α, ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x = f x := by
  obtain ⟨C, hC, hn, hh⟩ := OAI.Analysis.PDE.Dirichlet.smooth_jet_compact_holder_bound f hf hS hα hα1
  obtain ⟨P, hP, _⟩ := exists_holder_field_of_bounds hα hC.le f hf.continuous.continuousOn hn
    (fun x hx y hy => by simpa only [dist_eq_norm] using hh x hx y hy)
  exact ⟨P, hP⟩

local instance lowerHolderFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance lowerHolderFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance lowerHolderSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance lowerHolderSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_lower_jet_holder {S : Set E} {α M : ℝ}
    (hα : 0 ≤ α) (hM : 0 ≤ M) (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (hb : OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn u S α M) :
    ∃ (D : HolderMap S (E →L[ℝ] ℝ) α) (H : HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x) ∧
      ‖D‖ ≤ M ∧ ‖H‖ ≤ M := by
  obtain ⟨D, hD, hDn⟩ := exists_holder_field_of_bounds hα hM (fderiv ℝ u)
    (hu.continuous_fderiv (by norm_num)).continuousOn hb.first hb.first_sub
  have h₁ : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  obtain ⟨H, hH, hHn⟩ := exists_holder_field_of_bounds hα hM (fderiv ℝ (fderiv ℝ u))
    (h₁.continuous_fderiv one_ne_zero).continuousOn hb.second hb.second_sub
  exact ⟨D, H, hD, hH, hDn, hHn⟩

end OAI.Analysis.Normed.Function.Holder
