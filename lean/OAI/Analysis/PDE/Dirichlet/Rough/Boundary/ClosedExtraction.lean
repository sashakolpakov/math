import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.TangentExtraction
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.NormalJet
import OAI.Analysis.PDE.Dirichlet.Closed.C2Regularity

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {r : E → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}

local instance closedExtractionFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance closedExtractionFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance closedExtractionSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedExtractionSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedExtractionHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance closedExtractionHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance

omit [Nontrivial E] in
theorem closed_tangent_contDiffOn_of_jet
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {S : Set V} {G : V → E} (hG : ContDiffOn ℝ 2 G S) (hGS : MapsTo G S {x | r x ≤ 0})
    (W : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) {f : V → ℝ}
    (he : ∀ z (hz : z ∈ S), OAI.Analysis.Normed.Function.Holder.C2Holder.value W ⟨G z,hGS hz⟩ = f z) :
    ContDiffOn ℝ 2 f S := by
  apply ((c2Holder_contDiffOn_two_closed hr hreg W).comp hG hGS).congr
  intro z hz
  rw [Function.comp_apply,OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hGS hz)]
  exact (he z hz).symm

omit [Nontrivial E] in
/-- One derivative of the Banach curve yields C² tangential regularity on
the closed chart, including its boundary plane. -/
theorem first_tangent_contDiffOn_of_parameter_curve
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α} (hU : DifferentiableAt ℝ U 0)
    {S : Set V} {G : V → E} (hG : ContDiffOn ℝ 2 G S) (hGS : MapsTo G S {x | r x ≤ 0})
    {f : V → ℝ} (v : V) (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (he : ∀ z (hz : z ∈ S),
      (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hGS hz⟩) =ᶠ[𝓝 0] fun t ↦ f (z + t • v)) :
    ContDiffOn ℝ 2 (constantDirectional f v) S := by
  apply closed_tangent_contDiffOn_of_jet hr hreg hG hGS (deriv U 0)
  intro z hz
  exact first_parameter_jet_matches_tangent hU _ v (hf z hz) (he z hz)

omit [Nontrivial E] in
/-- Two Banach derivatives give the diagonal second-tangential derivative
as a genuine C² function on the closed chart. -/
theorem diagonal_tangent_contDiffOn_of_parameter_curve
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α} (hU : ContDiffAt ℝ 2 U 0)
    {S : Set V} {G : V → E} (hG : ContDiffOn ℝ 2 G S) (hGS : MapsTo G S {x | r x ≤ 0})
    {f : V → ℝ} (v : V) (hf : ∀ z ∈ S, ContDiffAt ℝ 2 f z)
    (he : ∀ z (hz : z ∈ S),
      (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hGS hz⟩) =ᶠ[𝓝 0] fun t ↦ f (z + t • v)) :
    ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ (fderiv ℝ f) z v v) S := by
  apply closed_tangent_contDiffOn_of_jet hr hreg hG hGS (deriv (deriv U) 0)
  intro z hz
  exact second_parameter_jet_matches_tangent hU _ v (hf z hz) (he z hz)

end OAI.Analysis.PDE.Dirichlet
