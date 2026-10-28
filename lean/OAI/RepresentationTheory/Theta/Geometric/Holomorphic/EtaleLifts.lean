import OAI.AlgebraicGeometry.Cycles.Functoriality.IntrinsicEtale
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold

/-! # Etale Lifts -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.EtaleLifts

noncomputable section

/-! A continuous lift of a holomorphic map through an actual local
analytic diffeomorphism is holomorphic. This applies to finite étale branch lifts. -/

open scoped _root_.Manifold ContDiff

theorem mdifferentiable_lift_of_localDiffeomorph
    {E F V M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace P] [ChartedSpace V P]
    {n : ℕ∞ω} (hn : n ≠ 0) (f : M → N)
    (hf : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F) n f)
    (g : P → M) (hg : Continuous g)
    (hfg : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, F) (f ∘ g)) :
    MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, E) g := by
  intro x
  let h := hf (g x)
  have hi := (h.localInverse_mdifferentiableAt hn).comp x (hfg x)
  have he := h.localInverse_eventuallyEq_left.comp_tendsto hg.continuousAt
  exact hi.congr_of_eventuallyEq he.symm

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.EtaleLifts
