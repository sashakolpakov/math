import OAI.AlgebraicGeometry.CycleClass.Thom.Degree

/-! # Pair Pullback -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PairPullback.Constructions.ThomClass

noncomputable section

/-! Pulling the actual Thom class through a genuine normal neighborhood gives its specified normal-pair class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

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

theorem normalPair_pullback (x : M) (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E × (Fin p → ℂ)))
    {X : TopCat.{0}} (g : X ⟶ TopCat.of P.neighborhood) (A : Set X)
    (hg : Set.MapsTo g A P.relativeComplement) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (g ≫ Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
      (show Set.MapsTo (g ≫ Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) A (Set.range f)ᶜ from hg)
      (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * p) P.rationalClassFin := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) g
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) hg
      (B := P.relativeComplement) (C := (Set.range f)ᶜ) (fun _ hx => hx) (2 * p))
    (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi he p hp)
  exact h.symm.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * p))
    (Degree.Constructions.ThomClass.complexThomClassInDegree_restrict f hf hi he p hp x P hP))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PairPullback.Constructions.ThomClass
