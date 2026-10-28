import OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechRestriction
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison
import OAI.AlgebraicTopology.Cohomology.Singular.CechComparison
import OAI.AlgebraicTopology.Cohomology.Singular.EuclideanBallCover
import OAI.AlgebraicTopology.Cohomology.Singular.ChartCechCover
import OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison
import OAI.AlgebraicTopology.DeRham.Comparison.CechTotal
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSmoothAugmentation

/-! # Global Smooth Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison

noncomputable section

/-!
# Global comparison with actual manifold-smooth singular cochains

The comparison map is restriction of ordinary singular cochains to genuine
smooth simplices. Its quasi-isomorphism is proved by two applications of
the verified Čech descent theorem. A normed-space open set is covered by
balls whose intersections have convex ambient images. A smooth manifold
is then covered by chart sources whose intersections have open model images.
Empty intersections are included throughout; no good-cover, compactness,
or separation hypothesis is added.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

section Cover

variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Opens X)

/-- The actual restriction on Čech totals is a quasi-isomorphism whenever
it is one on every actual ordered intersection. -/
theorem manifoldSmoothCechRestriction_quasiIso_of_intersections
    (A : ModuleCat.{0} ℂ)
    (hlocal : ∀ (p : ℕ) (a : Fin (p + 1) → ι),
      QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A (DeRham.Comparison.SmoothCech.cechIntersection U a))) :
    QuasiIso (SmoothCechRestriction.manifoldSmoothCechRestriction E X U A) := by
  change QuasiIso (DeRham.Comparison.CechTotalFunctor.cechTotalMap U (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A))
  exact DeRham.Comparison.CechTotal.cechTotalMap_quasiIso_of_intersections U
    (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A) hlocal

/-- Actual ordinary and smooth Čech augmentations transfer a comparison
on cover intersections to the genuine global cochain restriction. -/
theorem quasiIso_manifoldSmoothCochainRestriction_of_cover
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hlocal : ∀ (p : ℕ) (a : Fin (p + 1) → ι),
      QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ)
        (DeRham.Comparison.SmoothCech.cechIntersection U a))) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) X) := by
  let := CechComparison.complexGlobalSingularCechAugmentation_quasiIso (TopCat.of X) U hcover
  let := ManifoldSmoothCechComparison.complexGlobalManifoldSmoothCechAugmentation_quasiIso E X U hcover
  let := manifoldSmoothCechRestriction_quasiIso_of_intersections E X U
    (ModuleCat.of ℂ ℂ) hlocal
  have : QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) X ≫
      SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E X U (ModuleCat.of ℂ ℂ)) := by
    rw [SmoothCechRestriction.manifoldSmoothCechRestriction_augmentation]
    infer_instance
  exact quasiIso_of_comp_right
    (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) X)
    (SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E X U (ModuleCat.of ℂ ℂ))

end Cover

/-- Every ordered intersection in the actual ball cover of an open normed
domain has the genuine smooth/ordinary comparison, even if empty. -/
theorem quasiIso_euclideanBallCover_intersection (U : Opens E)
    (p : ℕ) (a : Fin (p + 1) → U) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ)
      (DeRham.Comparison.SmoothCech.cechIntersection (EuclideanBallCover.euclideanBallCover U) a)) :=
  (ChartSmoothComparison.quasiIso_manifoldSmoothRestriction_diffeomorph_iff (ModuleCat.of ℂ ℂ)
    (EuclideanBallCover.euclideanBallCoverCechDiffeomorph U a)).mp
      (DeRham.Comparison.ManifoldSmoothAugmentation.quasiIso_convexOpenManifoldSmoothRestriction E (ModuleCat.of ℂ ℂ)
        (ChartOpenDiffeomorph.nestedOpenImage U (DeRham.Comparison.SmoothCech.cechIntersection (EuclideanBallCover.euclideanBallCover U) a))
        (EuclideanBallCover.convex_nestedOpenImage_euclideanBallCover_cech U a))

/-- Restriction to genuine smooth singular simplices is a quasi-isomorphism
on every open subset of a real normed space. -/
theorem quasiIso_openManifoldSmoothCochainRestriction (U : Opens E) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) U) :=
  quasiIso_manifoldSmoothCochainRestriction_of_cover E U (EuclideanBallCover.euclideanBallCover U)
    (fun x => ⟨x, EuclideanBallCover.euclideanBallCover_mem_self U x⟩)
    (quasiIso_euclideanBallCover_intersection E U)

variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Every intersection of preferred chart sources is compared through its
actual open image in the normed model. -/
theorem quasiIso_preferredChartCover_intersection
    (p : ℕ) (a : Fin (p + 1) → M) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ)
      (DeRham.Comparison.SmoothCech.cechIntersection (ChartCechCover.preferredChartCover E M) a)) :=
  (ChartSmoothComparison.quasiIso_manifoldSmoothRestriction_diffeomorph_iff (ModuleCat.of ℂ ℂ)
    (ChartCechCover.preferredChartCechDiffeomorph E M a)).mp
      (quasiIso_openManifoldSmoothCochainRestriction E (ChartCechCover.preferredChartCechImage E M a))

/-- The canonical ordinary-to-smooth singular cochain restriction is a
quasi-isomorphism on every smooth manifold modeled on a real normed space. -/
theorem quasiIso_manifoldSmoothCochainRestriction :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) :=
  quasiIso_manifoldSmoothCochainRestriction_of_cover E M (ChartCechCover.preferredChartCover E M)
    (ChartCechCover.preferredChartCover_covers E M) (quasiIso_preferredChartCover_intersection E M)

/-- The resulting cohomology isomorphism is induced by actual restriction,
so it can be composed with a proved integration map without choosing a new map. -/
def manifoldSmoothCohomologyIso (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n ≅
      (ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).homology n := by
  letI := quasiIso_manifoldSmoothCochainRestriction E M
  exact isoOfQuasiIsoAt (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n

@[simp]
theorem manifoldSmoothCohomologyIso_hom (n : ℕ) :
    (manifoldSmoothCohomologyIso E M n).hom =
      HomologicalComplex.homologyMap
        (ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison
