import OAI.AlgebraicGeometry.ComplexMultiplication.HomeomorphInverseDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Open Embedding Differentiable -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OpenEmbeddingDifferentiable

noncomputable section

/-! # The actual open-embedding partial homeomorphism is a complex local diffeomorphism -/

open scoped _root_.Manifold

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [Nonempty M]

theorem openEmbedding_mDifferentiable (f : M → N) (he : Topology.IsOpenEmbedding f)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f)
    (hb : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x)) :
    (he.toOpenPartialHomeomorph f).MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) := by
  let e := he.toOpenPartialHomeomorph f
  have heq : (e : M → N) = f := he.toOpenPartialHomeomorph_apply f
  constructor
  · intro x _
    rw [heq]
    exact (hf x).mdifferentiableWithinAt
  · intro y hy
    have hr : y ∈ Set.range f := by
      simpa only [e, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hy
    obtain ⟨x, rfl⟩ := hr
    have hx : x ∈ e.source := by
      simp only [e, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.mem_univ]
    have hfx : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) e x := heq.symm ▸ hf x
    have hbx : Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x) := heq.symm ▸ hb x
    have hi := HomeomorphInverseDifferentiable.partialHomeomorph_inverse_mDifferentiableAt e x hx hfx hbx
    rw [heq] at hi
    exact hi.mdifferentiableWithinAt

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OpenEmbeddingDifferentiable
