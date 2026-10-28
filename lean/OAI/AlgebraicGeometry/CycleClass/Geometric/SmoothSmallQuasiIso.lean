import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSubdivisionSmall
import OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallRange

/-! # Smooth Small Quasi Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSmallQuasiIso.Cycles

noncomputable section

/-!
# The actual small smooth singular chain comparison

Smooth barycentric subdivision and its genuine smooth homotopy preserve the
cover-small smooth complex. Ordinary geometric mesh estimates make each finite
smooth chain cover-small after finitely many subdivisions. The actual support
description of the small smooth image identifies the resulting preimage.

Thus the canonical inclusion of cover-small smooth singular chains is a
quasi-isomorphism, with no compactness or finite-dimensionality assumption.
-/

open _root_.CategoryTheory

open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallRange

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]
variable {J : Type} (U : J → Set M)

/-- A finite actual smooth chain has a genuinely small smooth preimage after
some number of barycentric subdivisions. -/
theorem exists_manifoldSmoothSubdivision_iterate_small_preimage
    (hopen : ∀ j, IsOpen (U j)) (hcover : ∀ x : M, ∃ j, x ∈ U j)
    {n : ℕ} (c : (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M).X n) :
    ∃ N : ℕ, ∃ b : ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall.manifoldSmoothSmallSubcomplex E M U).toSSet.chainComplex
      (ModuleCat.of ℤ ℤ)).X n,
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E M U).f n b =
        ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap E M).f n)^[N] c := by
  obtain ⟨N, hN⟩ := SubdivisionSmallness.Cycles.exists_subdivisionDegree_iterate_small U hopen hcover
    ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E M).f n c)
  refine ⟨N, ?_⟩
  have hiter : (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E M).f n
      (((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap E M).f n)^[N] c) =
      (SubdivisionOperator.Cycles.subdivisionDegree (TopCat.of M) n)^[N]
        ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothIntegralChainInclusion E M).f n c) :=
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_subdivision_iterate (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) n N c
  apply (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallRange.mem_range_manifoldSmoothSmallIntegralChainInclusion_iff E M U n _).2
  rw [hiter]
  exact hN

/-- For an actual open cover, the actual small smooth chain inclusion is a
quasi-isomorphism in every degree, including degree zero. -/
theorem manifoldSmoothSmallIntegralChainInclusion_quasiIso
    (hopen : ∀ j, IsOpen (U j)) (hcover : ∀ x : M, ∃ j, x ∈ U j) :
    _root_.QuasiIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E M U) := by
  change _root_.QuasiIso (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) U)
  exact EventuallySmall.Cycles.quasiIso_of_eventuallySmall
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) U)
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_injective (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) U)
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) U))
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M))
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.smallChainInclusion_subdivision (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) U)
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy (SmoothSimplexModels.Cycles.SmoothSimplexSpace.small (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) U))
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M))
    (fun _ c => exists_manifoldSmoothSubdivision_iterate_small_preimage E M U hopen hcover c)

/-- The induced canonical isomorphism on actual small smooth singular homology. -/
def manifoldSmoothSmallHomologyIso
    (hopen : ∀ j, IsOpen (U j)) (hcover : ∀ x : M, ∃ j, x ∈ U j) (n : ℕ) :
    ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall.manifoldSmoothSmallSubcomplex E M U).toSSet.chainComplex
      (ModuleCat.of ℤ ℤ)).homology n ≅ (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M).homology n := by
  letI := manifoldSmoothSmallIntegralChainInclusion_quasiIso E M U hopen hcover
  exact isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E M U) n

@[simp]
theorem manifoldSmoothSmallHomologyIso_hom
    (hopen : ∀ j, IsOpen (U j)) (hcover : ∀ x : M, ∃ j, x ∈ U j) (n : ℕ) :
    (manifoldSmoothSmallHomologyIso E M U hopen hcover n).hom =
      HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall.manifoldSmoothSmallIntegralChainInclusion E M U) n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSmallQuasiIso.Cycles
