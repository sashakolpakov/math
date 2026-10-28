import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSimplexModels
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall

/-! # Smooth Small Spaces -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Cover-small smooth singular structures

The intersection of the cover-small and smooth singular subcomplexes is
closed under genuine smooth simplex substitutions. It is therefore an actual
object of the same concrete category; its inclusion has the identity
continuous map. Natural smooth-chain homotopies consequently apply to these
small chains as well.
-/

open _root_.CategoryTheory
open scoped Simplicial

/-- The actual intersection of cover-small and specified smooth simplices. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.small (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type} (U : J → Set X.space) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace where
  space := X.space
  smooth := AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X.space U ⊓ X.smooth
  precomp_mem σ hσ τ hτ := by
    refine ⟨?_, X.precomp_mem σ hσ.2 τ hτ⟩
    obtain ⟨j, hj⟩ := hσ.1
    refine ⟨j, ?_⟩
    change Set.range (σ.comp τ) ⊆ U j
    change Set.range σ ⊆ U j at hj
    rintro x ⟨t, rfl⟩
    exact hj ⟨τ t, rfl⟩

/-- The identity continuous map gives the actual small-to-all inclusion. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallInclusion (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type} (U : J → Set X.space) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.small X U ⟶ X where
  map := 𝟙 X.space
  map_mem _ s := s.property.2

/-- On simplicial sets this is precisely the canonical intersection inclusion. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallInclusion_mapSmooth (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {J : Type}
    (U : J → Set X.space) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.mapSmooth (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallInclusion X U) =
      SSet.Subcomplex.homOfLE (show AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X.space U ⊓
        X.smooth ≤ X.smooth from inf_le_right) := rfl

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- For a manifold the small structure is exactly the already constructed
small-and-manifold-smooth simplicial set. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.small_manifold_simplicialSet {J : Type} (U : J → Set M) :
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) U).smooth.toSSet =
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall.manifoldSmoothSmallSubcomplex E M U).toSSet := rfl

/-- The chain inclusion agrees with the actual small smooth chain inclusion. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallInclusion_manifold_chainMap {J : Type} (U : J → Set M) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallInclusion (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) U) =
      AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E M U := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
