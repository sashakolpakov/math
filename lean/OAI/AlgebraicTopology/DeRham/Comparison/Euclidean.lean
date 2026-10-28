import OAI.AlgebraicTopology.DeRham.Comparison.EuclideanOpenCover
import OAI.AlgebraicTopology.DeRham.Comparison.EuclideanIntegrationDescent
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothRelativeCech

/-! # Euclidean -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.Euclidean

noncomputable section

/-!
# Actual de Rham integration on every Euclidean open domain

Cover the domain by actual convex open balls. On all ordered intersections,
the genuine Duffy integration map is a quasi-isomorphism by the proved local
comparison. The actual form and smooth singular Čech augmentations are
quasi-isomorphisms, so their natural square proves the same for integration
on the entire open domain. The empty domain is included.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothRelativeCech

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Genuine Duffy integration is a quasi-isomorphism on every Euclidean open domain. -/
theorem manifoldOpenIntegration_quasiIso_euclideanOpen (W : Opens E) :
    QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E W) := by
  exact EuclideanIntegrationDescent.manifoldOpenIntegration_quasiIso_of_convex_cover E (EuclideanOpenCover.euclideanOpenBallCover W) W
    (EuclideanOpenCover.euclideanOpenBallCover_le W) (EuclideanOpenCover.euclideanOpenBallCover_covers W)
    (EuclideanOpenCover.euclideanOpenBallCover_convex W)
    (Cohomology.Singular.ManifoldSmoothRelativeCech.manifoldSmoothRelativeCechAugmentation_quasiIso E E (EuclideanOpenCover.euclideanOpenBallCover W) W
      (EuclideanOpenCover.euclideanOpenBallCover_le W) (EuclideanOpenCover.euclideanOpenBallCover_covers W))

/-- The same actual integration map is a quasi-isomorphism in the intrinsic
manifold-form model of an arbitrary Euclidean open. -/
theorem smoothSimplexIntegrationCochainMap_quasiIso_euclideanOpen (W : Opens E) :
    QuasiIso (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E W) := by
  let : QuasiIso ((Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E W).hom ≫
      SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E W) :=
    manifoldOpenIntegration_quasiIso_euclideanOpen E W
  exact quasiIso_of_comp_left (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso E W).hom
    (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E W)

/-- The comparison on actual cohomology is induced by genuine integration. -/
def euclideanOpenIntegrationCohomologyIso (W : Opens E) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamCohomology E W n ≅
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) W).homology n := by
  let : QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E W) :=
    manifoldOpenIntegration_quasiIso_euclideanOpen E W
  exact isoOfQuasiIsoAt (ManifoldOpenIntegration.manifoldOpenIntegration E W) n

@[simp]
theorem euclideanOpenIntegrationCohomologyIso_hom (W : Opens E) (n : ℕ) :
    (euclideanOpenIntegrationCohomologyIso E W n).hom =
      ManifoldOpenIntegration.manifoldOpenIntegrationCohomology E W n := rfl

/-- The integration isomorphisms commute with restriction between arbitrary
Euclidean open domains. -/
theorem euclideanOpenIntegrationCohomologyIso_naturality
    {U V : Opens E} (h : U ≤ V) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamCohomologyRestrict E h n ≫
        (euclideanOpenIntegrationCohomologyIso E U n).hom =
      (euclideanOpenIntegrationCohomologyIso E V n).hom ≫
        HomologicalComplex.homologyMap
          (Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E E (ModuleCat.of ℂ ℂ) (homOfLE h)) n := by
  simp only [euclideanOpenIntegrationCohomologyIso_hom]
  exact ManifoldOpenIntegration.manifoldOpenIntegrationCohomology_restrict E h n

end

end OAI.AlgebraicTopology.DeRham.Comparison.Euclidean
