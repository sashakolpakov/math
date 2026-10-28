import OAI.Analysis.PDE.Dirichlet.Rough.SmoothGeometricCurves
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.HigherParameterJets

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E X P V ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- All pure tangential orders are controlled on a single neighborhood
for each direction. The neighborhood is chosen from the geometric germ,
before the derivative order N. This is the input for higher normal
recovery, with no finite-order regularity assumption on the solution. -/
theorem HasSmoothGeometricSolutionCurves.all_tangent_orders
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r ψ B : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hc : HasSmoothGeometricSolutionCurves e b r ψ B hΩD α)
    (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (j : X ≃ₗᵢ[ℝ] E) (G : X → E) (P' : E → X)
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P')
    (hinv : (fun z ↦ P' (G z)) =ᶠ[𝓝 (0 : X)] id)
    (ℓ : X →L[ℝ] ℝ) (c : ℝ)
    (hlevel : ∀ z ∈ ball (0 : X) 1, r (G z) = c+ℓ z)
    {S : Set X} (hGS : MapsTo G S {x | r x ≤ 0}) :
    ∀ v : X, ℓ v = 0 → ∃ O : Set X, IsOpen O ∧ (0 : X) ∈ O ∧
      ∀ N : ℕ, ContDiffOn ℝ 2 (fun z ↦ iteratedDeriv N
        (fun t : ℝ ↦ ψ (G (z+t • v))-B (G (z+t • v))) 0) (S ∩ O) := by
  intro v hv
  obtain ⟨D,hD⟩ := exists_boundary_periodicDomainDeformation j e b r hrp hG hP rfl
    hinv ℓ c hlevel v hv
  obtain ⟨U,hU,he⟩ := hc D
  obtain ⟨O,hO,hzero,hgerm⟩ := translation_curve_germs hGS he hD
  refine ⟨O,hO,hzero,?_⟩
  intro N
  exact higher_tangent_contDiffOn_of_parameter_curve (S := S ∩ O) (G := G)
    (f := fun z ↦ ψ (G z)-B (G z)) hr hreg hU
    (hG.of_le (by simp)).contDiffOn (fun z hz ↦ hGS hz.1) v hgerm N

end OAI.Analysis.PDE.Dirichlet
