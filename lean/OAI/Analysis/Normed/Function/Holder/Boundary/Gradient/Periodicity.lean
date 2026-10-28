import OAI.Analysis.Normed.Function.Holder.C2HolderPeriodicity

/-! Periodicity of the genuine stored first derivative, including the
boundary where differentiability of the zero extension is not assumed. -/

noncomputable section
open Set Module
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

open OAI.Analysis.PDE.Dirichlet

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P}
local instance gradientPeriodFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance gradientPeriodFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

omit [Fintype ι] in
theorem latticePeriodic_firstDerivative (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => x ∈ Ω))
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => x ∈ K))
    (u : C2Holder (F := F) hΩK α)
    (hu : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (C2Holder.value u))) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (C2Holder.firstDerivative u)) := by
  apply latticePeriodic_boundary_field hΩK hKΩ hΩper hKper hu.fderiv
  intro x hx
  rw [boundedZeroExtension_apply _ (hΩK hx)]
  exact (C2Holder.genuine_derivatives hΩ u hx).1.symm

end OAI.Analysis.Normed.Function.Holder.C2Holder
