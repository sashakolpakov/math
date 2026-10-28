import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.FundamentalClass.ProjectedClasses
import OAI.AlgebraicTopology.FundamentalClass.RelativeSmooth
import OAI.AlgebraicTopology.FundamentalClass.LocalSimplex
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothOpenReflection

/-! # Simplex Cycles -/

namespace OAI.AlgebraicTopology.FundamentalClass.SimplexCycles.IntegrationConstruction

noncomputable section

/-! A simplex whose faces lie in the subspace is a genuine relative cycle,
both for integral singular chains and for complex smooth singular chains. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
open _root_.CategoryTheory Opposite Set _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothOpenReflection OAI.AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry
open scoped Simplicial _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def SimplexFacesIn (X : TopCat.{0}) (A : Set X) (n : ℕ) (σ : Cohomology.Singular.Basic.singularSimplices X n) : Prop :=
  match n, σ with
  | 0, _ => True
  | n + 1, σ => ∀ (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))),
      X.toSSetObjEquiv (op ⦋n⦌) ((TopCat.toSSet.obj X).δ i σ) t ∈ A

theorem integralSimplex_relative_cycle (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (σ : Cohomology.Singular.Basic.singularSimplices X n) (hσ : SimplexFacesIn X A n σ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n := by
  cases n with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ n =>
    rw [Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    have h := ConcreteCategory.congr_hom ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).comm (n + 1) n).symm
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ)
    change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
        ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X).d (n + 1) n
          (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ)) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d (n + 1) n
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (n + 1) (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ)) at h
    rw [← h, Cohomology.Singular.ChainDual.simplexChain_boundary, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_zsmul, LocalSimplex.IntegrationGeometry.relativeProjection_simplex_zero A _ (hσ i), zsmul_zero]

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]

theorem smoothRelativeProjection_simplex_zero (U : Opens M) (n : ℕ)
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (hσ : ∀ t, (TopCat.of M).toSSetObjEquiv (op ⦋n⦌) σ.val t ∈ U) :
    (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n
      (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ) = 0 := by
  have hrange : range (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap (TopCat.of M) n σ.val) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact hσ t
  let τ := Cohomology.Singular.ManifoldSmoothOpenReflection.manifoldSmoothSimplexLift E U σ hrange
  have hτ : (RelativeSmooth.IntegrationConstruction.smoothOpenMap E M U).app _ τ = σ := Cohomology.Singular.ManifoldSmoothOpenReflection.manifoldSmoothSimplexLift_spec E U σ hrange
  have hchain : (RelativeSmooth.IntegrationConstruction.smoothOpenChainInclusion E M U).f n
      (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet τ) =
      Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ := by
    rw [Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex, hτ]
  rw [← hchain]
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (CategoryTheory.Limits.cokernel.condition (RelativeSmooth.IntegrationConstruction.smoothOpenChainInclusion E M U)) n)
    (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet τ)

theorem smoothSimplex_relative_cycle (U : Opens M) (n : ℕ)
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (hσ : SimplexFacesIn (TopCat.of M) U n σ.val) :
    (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n
      (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U) n := by
  cases n with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ n =>
    rw [Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    have h := ConcreteCategory.congr_hom ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).comm (n + 1) n).symm
      (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ)
    change (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n
        ((SmoothHomology.IntegrationConstruction.smoothChains E M).d (n + 1) n
          (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ)) =
      (RelativeSmooth.IntegrationConstruction.smoothRelativeChains E M U).d (n + 1) n
        ((RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f (n + 1)
          (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet σ)) at h
    rw [← h, Cohomology.Singular.ChainDual.simplexChain_boundary, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_zsmul]
    have hi : (RelativeSmooth.IntegrationConstruction.smoothRelativeProjection E M U).f n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
          ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ i σ)) = 0 :=
      smoothRelativeProjection_simplex_zero E M U n
        ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ i σ) (hσ i)
    rw [hi, zsmul_zero]

end

end OAI.AlgebraicTopology.FundamentalClass.SimplexCycles.IntegrationConstruction
