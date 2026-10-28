import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CoverSheets
import OAI.RepresentationTheory.Theta.Geometric.SmoothFormLocalSections
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic

/-! # Cover Local Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.CoverLocalSections

noncomputable section

/-! The actual holomorphic period cover has smooth local sections,
so smoothness of an actual covector field can be checked on that cover. -/

open OAI.Analysis.DifferentialForms.Manifold.Holomorphic _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem holomorphicCover_hasLocalSections
    {V W M N : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
    [FiniteDimensional ℂ W]
    [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℂ, V) ∞ M]
    [TopologicalSpace N] [ChartedSpace W N] [IsManifold 𝓘(ℂ, W) ∞ N]
    (f : M → N) (hsurj : Function.Surjective f) (hcover : IsCoveringMap f)
    (hf : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) f)
    (hbij : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) f x)) (y : N) :
    ∃ (U : Opens N) (r : N → M), y ∈ U ∧
      ContMDiffOn 𝓘(ℝ, W) 𝓘(ℝ, V) ∞ r U ∧ ∀ z ∈ U, f (r z) = z := by
  obtain ⟨x, rfl⟩ := hsurj y
  let h := Holomorphic.CoverSheets.holomorphicCover_isLocalDiffeomorph f hcover hf hbij x
  let U : Opens N := ⟨h.localInverse.source, h.localInverse.open_source⟩
  refine ⟨U, h.localInverse, h.localInverse_mem_source, ?_, fun _ hz => h.localInverse_right_inv hz⟩
  intro z hz
  exact (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex
    ((h.localInverse.contMDiffOn_toFun z hz).contMDiffAt (U.isOpen.mem_nhds hz))).contMDiffWithinAt

end

end OAI.RepresentationTheory.Theta.Geometric.Period.CoverLocalSections
