import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticLocalInverseAt
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential

/-! # Inclusion Local Inverse -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionLocalInverse.Constructions

noncomputable section

/-! Open inclusions are local analytic diffeomorphisms in the inherited manifold charts. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticLocalInverseAt.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

theorem inclusion_localInverse {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    (U : Opens M) (x : U) :
    IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (Subtype.val : U → M) x := by
  apply AnalyticLocalInverseAt.Constructions.isLocalDiffeomorphAt_of_bijective_mfderiv (Subtype.val : U → M) x
    (show ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (Subtype.val : U → M) x from contMDiff_subtype_val x)
  rw [InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal]
  exact Function.bijective_id

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionLocalInverse.Constructions
