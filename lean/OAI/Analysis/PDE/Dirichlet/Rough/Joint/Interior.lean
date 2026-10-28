import OAI.Analysis.PDE.Dirichlet.Rough.Joint.ParameterExtraction

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z E : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E] in
/-- The literal joint implicit-family identity and a local translation
flow imply actual joint smoothness in external parameters and space. -/
theorem joint_contDiffAt_of_interior_flow
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    {U : Z × E → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α} {p₀ : Z} {x₀ : E}
    (hx₀ : x₀ ∈ K) (hU : ContDiffAt ℝ ∞ U (p₀,0))
    {Φ : E × E → E} {f : Z × E → ℝ}
    (hvalue : ∀ᶠ p in 𝓝 (p₀,(0:E)), ∀ x : K,
      OAI.Analysis.Normed.Function.Holder.C2Holder.value (U p) x = f (p.1,Φ (p.2,x)))
    (hflow : (fun q : E × E ↦ Φ q) =ᶠ[𝓝 (0,x₀)] fun q ↦ q.2+q.1) :
    ContDiffAt ℝ ∞ f (p₀,x₀) := by
  apply ParameterDeformation.contDiffAt_joint_of_translation_family hx₀ hU
  have ht : Tendsto (fun p : Z × E ↦ (p.2,x₀)) (𝓝 (p₀,0)) (𝓝 (0,x₀)) :=
    (continuous_snd.prodMk continuous_const).tendsto (p₀,0)
  filter_upwards [hvalue,ht.eventually hflow] with p hp hflowp
  rw [hp ⟨x₀,hx₀⟩]
  change f (p.1,Φ (p.2,x₀)) = f (p.1,x₀+p.2)
  rw [hflowp]

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
