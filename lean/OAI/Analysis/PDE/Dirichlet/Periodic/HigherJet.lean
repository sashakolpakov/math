import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJetBounds
import OAI.Analysis.Normed.Function.Holder.Banach.Construct
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

open Set Module
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Every smooth periodic field supplies a genuine closed-domain Hölder
field; no quantitative bound is required as input. -/
theorem exists_periodic_holder_field
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfp : LatticePeriodic e b f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α,
      ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = f x := by
  obtain ⟨C, _, hn, hh⟩ := periodic_smooth_jet_holder_bound e b hK hr hrp hbounded f hf hfp hα hα1
  let f₀ : {x | r x ≤ 0} →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f x) (hf.continuous.comp continuous_subtype_val) C (fun x => hn x x.property)
  have hholder : ∀ x y, ‖f₀ x-f₀ y‖ ≤ C*dist x y^α :=
    fun x y => hh x x.property y y.property
  exact ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα f₀ hholder, fun _ => rfl⟩

local instance periodicThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A retained C⁴ periodic solution has an actual third-derivative
Hölder field to which small-error absorption can be applied. -/
theorem exists_periodic_third_derivative_field
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u : E → ℝ) (hu : ContDiff ℝ 4 u) (hup : LatticePeriodic e b u)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) := h₂.fderiv_right (by norm_num)
  exact exists_periodic_holder_field e b hK hr hrp hbounded _ h₃
    hup.fderiv.fderiv.fderiv hα hα1

end OAI.Analysis.PDE.Dirichlet
