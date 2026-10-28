import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Transport Differentiable -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportDifferentiable.Constructions

noncomputable section

/-! Ambient transport preserves genuine complex differentiability of the
normal chart when the ambient homeomorphism is holomorphic both ways. -/

open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport.Constructions

variable {M N N' E F G H : Type} [TopologicalSpace N] [TopologicalSpace N']
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [ChartedSpace G N] [ChartedSpace H N']
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x) (e : N ≃ₜ N')

theorem transportNormalPair_mdifferentiable
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F))
    (he : MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, H) e)
    (hi : MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, G) e.symm) :
    (AmbientTransport.Constructions.transportNormalPair P e).ambientChart.MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, E × F) := by
  change (P.ambientChart.symm.transHomeomorph e).symm.MDifferentiable _ _
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact (hP.symm.trans ⟨he.mdifferentiableOn, hi.mdifferentiableOn⟩).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportDifferentiable.Constructions
