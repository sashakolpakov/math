import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJetBounds
import OAI.Analysis.Normed.Function.Holder.C2HolderConstruct
import OAI.Analysis.PDE.Dirichlet.Path.Solution

noncomputable section
open Set Module
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance periodicThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance periodicThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Each smooth periodic potential has a genuine bounded third-jet
Hölder field. Its norm is initially arbitrary; the Schauder absorption
argument, not this existence lemma, supplies its uniform bound. -/
theorem exists_periodic_third_holder
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u : E → ℝ) (hu : ContDiff ℝ 4 u) (hup : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) := h₂.fderiv_right (by norm_num)
  obtain ⟨C,hC,hCn,hCh⟩ := OAI.Analysis.PDE.Dirichlet.periodic_smooth_jet_holder_bound e b hK hr hrp hbounded
    (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) h₃ hup.fderiv.fderiv.fderiv hα hα1
  let v := OAI.Analysis.Normed.Function.Holder.boundedRestriction (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) h₃.continuous.continuousOn C hCn
  have hh (x y : {x | r x ≤ 0}) : ‖v x-v y‖ ≤ C*dist x y^α :=
    hCh x x.property y y.property
  exact ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα v hh,fun _ => rfl⟩

end OAI.Analysis.PDE.Schauder
