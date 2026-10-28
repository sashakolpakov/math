import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ParameterJets
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance extractionFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance extractionFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance extractionSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance extractionSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Only C² of the original function is used. Extra spatial regularity comes
from differentiation of the curve in the complete jet space. -/
theorem exists_second_tangent_jet_of_parameter_curve
    {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α} (hU : ContDiffAt ℝ 2 U 0)
    {S : Set V} (G : V → E) (hG : MapsTo G S K) (f : V → ℝ) (v : V)
    (hf : ∀ z ∈ S, ContDiffAt ℝ 2 f z)
    (he : ∀ z (hz : z ∈ S),
      (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z, hG hz⟩) =ᶠ[𝓝 0] fun t ↦ f (z + t • v)) :
    ∃ W : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ∀ z (hz : z ∈ S),
      OAI.Analysis.Normed.Function.Holder.C2Holder.value W ⟨G z, hG hz⟩ = fderiv ℝ (fderiv ℝ f) z v v := by
  refine ⟨deriv (deriv U) 0, ?_⟩
  intro z hz
  exact second_parameter_jet_matches_tangent hU _ v (hf z hz) (he z hz)

def polarizedSecondJet (A B C : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α :=
  (1/2 : ℝ) • (C - A - B)

theorem polarizedSecondJet_matches
    {A B C : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α} (x : K)
    {f : V → ℝ} {z : V} (hf : ContDiffAt ℝ 2 f z) (v w : V)
    (hA : OAI.Analysis.Normed.Function.Holder.C2Holder.value A x = fderiv ℝ (fderiv ℝ f) z v v)
    (hB : OAI.Analysis.Normed.Function.Holder.C2Holder.value B x = fderiv ℝ (fderiv ℝ f) z w w)
    (hC : OAI.Analysis.Normed.Function.Holder.C2Holder.value C x = fderiv ℝ (fderiv ℝ f) z (v+w) (v+w)) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (polarizedSecondJet A B C) x = fderiv ℝ (fderiv ℝ f) z v w := by
  change (1/2 : ℝ) * (OAI.Analysis.Normed.Function.Holder.C2Holder.value C x - OAI.Analysis.Normed.Function.Holder.C2Holder.value A x - OAI.Analysis.Normed.Function.Holder.C2Holder.value B x) = _
  rw [hA, hB, hC]
  have hsym := (hf.isSymmSndFDerivAt (by norm_num)).eq v w
  simp only [map_add, add_apply]
  linarith

theorem second_tangent_contDiffOn_of_jet
    (hΩ : IsOpen Ω) {O : Set V} (_ : IsOpen O)
    {G : V → E} (hG : ContDiffOn ℝ 2 G O) (hGO : MapsTo G O Ω)
    {f : V → ℝ} (v w : V) (W : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (he : ∀ z (hz : z ∈ O), OAI.Analysis.Normed.Function.Holder.C2Holder.value W ⟨G z, hΩK (hGO hz)⟩ =
      fderiv ℝ (fderiv ℝ f) z v w) :
    ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ (fderiv ℝ f) z v w) O := by
  apply ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ W).comp hG hGO).congr
  intro z hz
  rw [Function.comp_apply, OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hΩK (hGO hz))]
  exact (he z hz).symm

/-- Parameter differentiation preserves the actual zero boundary trace. -/
theorem second_parameter_jet_zeroTrace
    {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α} (hU : ContDiffAt ℝ 2 U 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ), U t ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.zeroTrace) :
    deriv (deriv U) 0 ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.zeroTrace := by
  intro x hx
  rw [value_second_deriv_curve hU x]
  have he : (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) x) =ᶠ[𝓝 0] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hz] with t ht
    exact ht x hx
  rw [he.deriv.deriv_eq]
  simp

end OAI.Analysis.PDE.Dirichlet
