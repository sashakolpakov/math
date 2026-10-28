import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexThom

/-! # Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

noncomputable section

/-! The genuine Thom class in a displayed codimension, and its uniqueness
from actual differentiable normal neighborhoods. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexThom.Cycles
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N] [MetrizableSpace N]
  (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
  (he : Topology.IsClosedEmbedding f) (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = p)

def complexThomClassInDegree :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ (2 * p) :=
  eqToHom (congrArg (fun d => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of N) (Set.range f)ᶜ (2 * d)) hp) (Geometric.ComplexThom.Cycles.complexThomClass f hf hi he)

variable [NormedSpace ℝ E]

theorem complexThomClassInDegree_restrict (x : M)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E × (Fin p → ℂ))) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * p)
      (complexThomClassInDegree f hf hi he p hp) = P.rationalClassFin := by
  subst hp
  exact (Geometric.ComplexThom.Cycles.complexThomClass_restrict_normalPair f hf hi he x P hP).trans
    P.rationalClassFin_eq_normalPullback.symm

theorem complexThomClassInDegree_unique
    (P : ∀ x : M, ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (hP : ∀ x, (P x).ambientChart.MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E × (Fin p → ℂ)))
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ (2 * p))
    (ha : ∀ x, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (P x).openNeighborhood (2 * p) a = (P x).rationalClassFin) :
    a = complexThomClassInDegree f hf hi he p hp := by
  subst hp
  apply Geometric.ComplexThom.Cycles.complexThomClass_unique f hf hi he a
  intro x
  exact (P x).rationalClassFin_restriction_eq_of_charts
    (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi he x) (hP x)
    (Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable f hf hi he x) a (ha x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
