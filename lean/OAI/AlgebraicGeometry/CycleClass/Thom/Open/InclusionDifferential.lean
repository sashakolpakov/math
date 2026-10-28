import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

/-! # Inclusion Differential -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

/-! The actual inclusion of an open submanifold has the identity
differential in the inherited tangent models. -/

open _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
open scoped _root_.Manifold

open _root_.Manifold

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem mfderiv_subtypeVal (U : Opens M) (x : U) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (Subtype.val : U → M) x = ContinuousLinearMap.id ℂ E := by
  have h := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := E) (F := E) U (id : U → U) x
  rw [mfderiv_id] at h
  exact h.symm

end AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

namespace AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions

/-! Inclusions between actual open submanifolds are holomorphic and
have the identity derivative in their inherited tangent models. -/

open _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

set_option backward.isDefEq.respectTransparency false

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (U W : Opens M) (h : U ≤ W)

local instance (O : Opens M) : ChartedSpace E (O : Set M) :=
  inferInstanceAs (ChartedSpace E O)

theorem openInclusion_analytic :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (Set.inclusion h : U → W) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff W (Set.inclusion h : U → W) ω).mp
  exact (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (Subtype.val : U → M) from contMDiff_subtype_val)

theorem openInclusion_mfderiv (x : U) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (Set.inclusion h : U → W) x = ContinuousLinearMap.id ℂ E :=
  (ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := E) (F := E) W (Set.inclusion h : U → W) x).trans
    (Manifold.mfderiv_subtypeVal U x)

end AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions

end

end OAI
