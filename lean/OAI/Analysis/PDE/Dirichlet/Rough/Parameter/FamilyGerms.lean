import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.GermSlices
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ParameterJets

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

namespace ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

/-- Combine the uniform-in-space value identity from the implicit curve
with the local chart-translation germ. Only the resulting scalar germs
are used for parameter differentiation. -/
theorem translation_curve_germs
    {Φ : Z × E → E} {G : V → E} {S : Set V} (hGS : MapsTo G S K)
    {ψ B : E → ℝ} {U : Z → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α}
    {a : V} (A : Z →L[ℝ] V)
    (hvalue : ∀ᶠ t in 𝓝 (0 : Z), ∀ x : K,
      OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) x = ψ (Φ (t,x)) - B (Φ (t,x)))
    (hflow : (fun p : Z × V ↦ Φ (p.1,G p.2)) =ᶠ[𝓝 (0,a)]
      (fun p ↦ G (p.2 + A p.1))) :
    ∃ O : Set V, IsOpen O ∧ a ∈ O ∧ ∀ z (hz : z ∈ S ∩ O),
      (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hGS hz.1⟩) =ᶠ[𝓝 0]
        fun t ↦ ψ (G (z + A t)) - B (G (z + A t)) := by
  obtain ⟨O,hO,ha,hgerm⟩ := ParameterDeformation.exists_open_parameter_germ_slices hflow
  refine ⟨O,hO,ha,?_⟩
  intro z hz
  filter_upwards [hvalue,hgerm z hz.2] with t ht htz
  rw [ht ⟨G z,hGS hz.1⟩]
  change ψ (Φ (t,G z)) - B (Φ (t,G z)) = _
  rw [htz]

end ParameterDeformation
end OAI.Analysis.PDE.Dirichlet
