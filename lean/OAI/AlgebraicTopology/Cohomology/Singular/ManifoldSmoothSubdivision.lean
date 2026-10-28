import OAI.AlgebraicTopology.Cohomology.Singular.SubcomplexSubdivision
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSimplexComposition
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-! # Manifold Smooth Subdivision -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Genuine barycentric subdivision of manifold-smooth singular chains

The barycentric simplex maps have explicit smooth ambient linear extensions.
Composing neighborhood extensions, on the inverse image of the outer extension
domain, proves preservation of manifold smoothness. The resulting invariant
subcomplex therefore carries the actual signed barycentric subdivision chain
map, with its proved inclusion into ordinary subdivision.
-/

open _root_.CategoryTheory
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Geometry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- Precomposition by a simplex map with a genuine ambient smooth extension
preserves the manifold neighborhood-extension condition. -/
theorem ManifoldSmooth.IsManifoldSmoothSimplex.precomp_of_smoothExtension {m n : ℕ}
    {s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)} (hs : ManifoldSmooth.IsManifoldSmoothSimplex E s)
    (t : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))))
    (A : (Fin (m + 1) → ℝ) → (Fin (n + 1) → ℝ)) (hA : ContDiff ℝ ∞ A)
    (ht : ∀ x : Convexity.StdSimplex ℝ (Fin (m + 1)), A x = (t x : Fin (n + 1) → ℝ)) :
    ManifoldSmooth.IsManifoldSmoothSimplex E (s.comp t) :=
  hs.comp ⟨A, Set.univ, isOpen_univ, Set.subset_univ _, hA.contDiffOn, ht⟩

/-- Any continuous linear simplex parameterization preserves manifold smoothness. -/
theorem ManifoldSmooth.IsManifoldSmoothSimplex.precomp_continuousLinear {m n : ℕ}
    {s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)} (hs : ManifoldSmooth.IsManifoldSmoothSimplex E s)
    (t : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))))
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (ht : ∀ x : Convexity.StdSimplex ℝ (Fin (m + 1)), A x = (t x : Fin (n + 1) → ℝ)) :
    ManifoldSmooth.IsManifoldSmoothSimplex E (s.comp t) :=
  hs.precomp_of_smoothExtension t A A.contDiff ht

/-- Any continuous affine simplex parameterization preserves manifold smoothness. -/
theorem ManifoldSmooth.IsManifoldSmoothSimplex.precomp_continuousAffine {m n : ℕ}
    {s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)} (hs : ManifoldSmooth.IsManifoldSmoothSimplex E s)
    (t : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))))
    (A : (Fin (m + 1) → ℝ) →ᴬ[ℝ] (Fin (n + 1) → ℝ))
    (ht : ∀ x : Convexity.StdSimplex ℝ (Fin (m + 1)), A x = (t x : Fin (n + 1) → ℝ)) :
    ManifoldSmooth.IsManifoldSmoothSimplex E (s.comp t) :=
  hs.precomp_of_smoothExtension t A A.contDiff ht

/-- The explicit ambient continuous linear map of barycentric vertex interpolation. -/
def ManifoldSmoothSubdivision.simplexVertexContinuousLinearMap {m n : ℕ}
    (v : Fin (m + 1) → Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (Fin (m + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) where
  toLinearMap := AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.simplexVertexLinearMap v
  cont := AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.continuous_simplexVertexLinearMap v

/-- Vertex interpolation is a smooth simplex into the actual closed simplex model. -/
theorem ManifoldSmoothSubdivision.isSmoothSimplexIn_simplexVertexMap {m n : ℕ}
    (v : Fin (m + 1) → Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ManifoldSmoothSimplexComposition.IsSmoothSimplexMap (AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.simplexVertexMap v) :=
  ⟨ManifoldSmoothSubdivision.simplexVertexContinuousLinearMap v, Set.univ, isOpen_univ, Set.subset_univ _,
    (ManifoldSmoothSubdivision.simplexVertexContinuousLinearMap v).contDiff.contDiffOn, fun x => by
      change AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.simplexVertexLinearMap v x = (AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.simplexVertexMap v x : Fin (n + 1) → ℝ)
      funext i
      rw [AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.simplexVertexLinearMap_apply, AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.simplexVertexMap_apply]⟩

/-- Every actual barycentric cell belongs to the smooth closed-simplex model. -/
theorem ManifoldSmoothSubdivision.isSmoothSimplexIn_barycentricSubdivisionMap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    ManifoldSmoothSimplexComposition.IsSmoothSimplexMap (AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) :=
  ManifoldSmoothSubdivision.isSmoothSimplexIn_simplexVertexMap
    (fun j => AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.faceBarycenter ((AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face j)
      ((AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty j))

/-- Precomposition with the exact geometric subdivision cells preserves manifold smoothness. -/
theorem ManifoldSmooth.IsManifoldSmoothSimplex.precomp_barycentricSubdivisionMap {n : ℕ}
    {s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)} (hs : ManifoldSmooth.IsManifoldSmoothSimplex E s)
    (σ : Equiv.Perm (Fin (n + 1))) :
    ManifoldSmooth.IsManifoldSmoothSimplex E (s.comp (AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles.barycentricSubdivisionMap σ)) :=
  hs.comp (ManifoldSmoothSubdivision.isSmoothSimplexIn_barycentricSubdivisionMap σ)

/-- Actual barycentric subdivision preserves subset-smooth simplex membership. -/
theorem ManifoldSmoothSubdivision.subsetSmoothSubdivision_closed (U : Set E) {n : ℕ}
    (s : (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex (TopCat.of U) n s.val σ ∈
      (SmoothOpen.subsetSmoothSingularSubcomplex U).obj (.op ⦋n⦌) := by
  change SmoothOpen.IsSmoothSimplexIn U ((TopCat.of U).toSSetObjEquiv (.op ⦋n⦌)
    (AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex (TopCat.of U) n s.val σ))
  rw [AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap]
  have hs : SmoothOpen.IsSmoothSimplexIn U ((TopCat.of U).toSSetObjEquiv (.op ⦋n⦌) s.val) := s.property
  exact hs.comp (ManifoldSmoothSubdivision.isSmoothSimplexIn_barycentricSubdivisionMap σ)

end Geometry

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- Actual barycentric subdivision preserves manifold-smooth simplex membership. -/
theorem ManifoldSmoothSubdivision.manifoldSmoothSubdivision_closed {n : ℕ}
    (s : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex (TopCat.of M) n s.val σ ∈
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).obj (.op ⦋n⦌) := by
  change ManifoldSmooth.IsManifoldSmoothSimplex E ((TopCat.of M).toSSetObjEquiv (.op ⦋n⦌)
    (AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex (TopCat.of M) n s.val σ))
  rw [AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap]
  exact ManifoldSmooth.IsManifoldSmoothSimplex.precomp_barycentricSubdivisionMap s.property σ

/-- Genuine integral chains on the manifold-smooth singular simplicial subcomplex. -/
abbrev ManifoldSmoothSubdivision.manifoldSmoothIntegralChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  SubcomplexSubdivision.subcomplexIntegralChains (TopCat.of M) (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M)

/-- The actual inclusion into ordinary integral singular chains. -/
abbrev ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion :
    ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M) :=
  SubcomplexSubdivision.subcomplexIntegralChainInclusion (TopCat.of M) (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M)

theorem ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion_injective (n : ℕ) :
    Function.Injective ((ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E M).f n) :=
  SubcomplexSubdivision.subcomplexIntegralChainInclusion_injective (TopCat.of M) (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M) n

/-- The genuine signed subdivision operator on manifold-smooth chains. -/
def ManifoldSmoothSubdivision.manifoldSmoothSubdivisionDegree (n : ℕ) :
    (ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M).X n →ₗ[ℤ] (ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M).X n :=
  SubcomplexSubdivision.subcomplexSubdivisionDegree (TopCat.of M) (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M)
    (ManifoldSmoothSubdivision.manifoldSmoothSubdivision_closed E M) n

@[simp]
theorem ManifoldSmoothSubdivision.manifoldSmoothSubdivisionDegree_inclusion (n : ℕ)
    (c : (ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M).X n) :
    (ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E M).f n (ManifoldSmoothSubdivision.manifoldSmoothSubdivisionDegree E M n c) =
      AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionDegree (TopCat.of M) n ((ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E M).f n c) :=
  SubcomplexSubdivision.subcomplexSubdivisionDegree_inclusion (TopCat.of M) (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M)
    (ManifoldSmoothSubdivision.manifoldSmoothSubdivision_closed E M) n c

/-- The actual smooth subdivision chain map, with boundary compatibility proved. -/
def ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap :
    ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M ⟶ ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M :=
  SubcomplexSubdivision.subcomplexSubdivisionChainMap (TopCat.of M) (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M)
    (ManifoldSmoothSubdivision.manifoldSmoothSubdivision_closed E M)

@[simp]
theorem ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap_f (n : ℕ) :
    ((ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap E M).f n).hom = ManifoldSmoothSubdivision.manifoldSmoothSubdivisionDegree E M n := rfl

/-- The inclusion intertwines the actual smooth and ordinary subdivision chain maps. -/
theorem ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap_intertwining :
    ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E M ≫ AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary.Cycles.subdivisionChainMap (TopCat.of M) =
      ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap E M ≫ ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E M :=
  SubcomplexSubdivision.subcomplexSubdivisionChainMap_intertwining (TopCat.of M) (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M)
    (ManifoldSmoothSubdivision.manifoldSmoothSubdivision_closed E M)

@[simp]
theorem ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap_f_zero :
    (ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap E M).f 0 = 𝟙 _ :=
  SubcomplexSubdivision.subcomplexSubdivisionChainMap_f_zero (TopCat.of M) (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M)
    (ManifoldSmoothSubdivision.manifoldSmoothSubdivision_closed E M)

end

end OAI.AlgebraicTopology.Cohomology.Singular
