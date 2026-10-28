import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Holomorphic Manifold -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity

noncomputable section

/-! # RiemannProjectivity: holomorphic manifold maps are smooth in every finite order -/

open Set
open scoped _root_.Manifold ContDiff

variable {V W M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓘(ℂ, V)) ∞ M]
  [TopologicalSpace N] [ChartedSpace W N] [IsManifold (𝓘(ℂ, W)) ∞ N]

theorem contMDiff_of_mdifferentiable {f : M → N}
    (hf : MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, W)) f) : ContMDiff (𝓘(ℂ, V)) (𝓘(ℂ, W)) ∞ f := by
  apply contMDiff_iff.mpr
  refine ⟨hf.continuous, fun x y => ?_⟩
  have hc : ContinuousOn (fun z => f ((extChartAt (𝓘(ℂ, V)) x).symm z))
      (extChartAt (𝓘(ℂ, V)) x).target :=
    hf.continuous.comp_continuousOn (continuousOn_extChartAt_symm (I := 𝓘(ℂ, V)) x)
  apply HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
    (hc.isOpen_inter_preimage (isOpen_extChartAt_target x) (isOpen_extChartAt_source y))
  exact (mdifferentiable_iff.mp hf).2 x y

def diffeomorph (e : M ≃ₜ N)
    (he : MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, W)) e)
    (hi : MDifferentiable (𝓘(ℂ, W)) (𝓘(ℂ, V)) e.symm) : M ≃ₘ⟮𝓘(ℂ, V), 𝓘(ℂ, W)⟯ N where
  toEquiv := e.toEquiv
  contMDiff_toFun := contMDiff_of_mdifferentiable he
  contMDiff_invFun := contMDiff_of_mdifferentiable hi

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity
