import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearDivisorIdealIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.SplitHyperplane
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.DegreeOneCover

/-! # Hyperplane Ideal Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneIdealIso.BundleCycles

noncomputable section

/-! All hyperplanes obtained by splitting off one coordinate of
a module have isomorphic genuine Cartier ideal bundles. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem symmetricLinearChart_cover (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (x : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M) :
    ∃ v : SymmetricAlgebra R M, v ∈ Grading.BundleCycles.symmetricGrading R M 1 ∧
      x ∈ Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) v := by
  obtain ⟨m, a, ha⟩ := (DegreeOneCover.BundleCycles.symmetricDegreeOneCover R M).openCover.exists_eq x
  refine ⟨SymmetricAlgebra.ι R M m, DegreeOneCover.BundleCycles.symmetricGenerator_degree R M m, ?_⟩
  rw [← DegreeOneCover.BundleCycles.symmetricDegreeOneCover_opensRange R M m]
  exact ⟨a, ha⟩

variable {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] R × N) (e' : M ≃ₗ[R] R × P)

def symmetricSplitHyperplaneMap : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R N ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap (SplitHyperplane.BundleCycles.splitHyperplaneQuotient e) (SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective e)

instance symmetricSplitHyperplaneMap_isClosedImmersion : IsClosedImmersion (symmetricSplitHyperplaneMap e) :=
  inferInstanceAs (IsClosedImmersion (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap (SplitHyperplane.BundleCycles.splitHyperplaneQuotient e) (SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective e)))

theorem symmetricSplitHyperplane_regular : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals (symmetricSplitHyperplaneMap e) :=
  Projective.LinearDivisorIdealIso.BundleCycles.projectiveLinearDivisor_regularPrincipalImageIdeals (symmetricLinearChart_cover R M)
    (GradedMap.BundleCycles.symmetricGradedMap (SplitHyperplane.BundleCycles.splitHyperplaneQuotient e))
    (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant _ (SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective e))
    (SymmetricProjective.ClosedImmersion.BundleCycles.symmetricGradedMap_surjective _ (SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective e))
    (SplitHyperplane.BundleCycles.splitHyperplaneEquation e) (DegreeOneCover.BundleCycles.symmetricGenerator_degree R M _) (SplitHyperplane.BundleCycles.splitHyperplaneEquation_regular e)
    (SplitHyperplane.BundleCycles.splitHyperplaneEquation_kernel e)

def symmetricSplitHyperplaneIdealIso :
    Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule (symmetricSplitHyperplaneMap e) ≅ Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule (symmetricSplitHyperplaneMap e') :=
  Projective.LinearDivisorIdealIso.BundleCycles.projectiveLinearDivisorIdealIso (symmetricLinearChart_cover R M)
    (GradedMap.BundleCycles.symmetricGradedMap (SplitHyperplane.BundleCycles.splitHyperplaneQuotient e))
    (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant _ (SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective e))
    (SymmetricProjective.ClosedImmersion.BundleCycles.symmetricGradedMap_surjective _ (SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective e))
    (SplitHyperplane.BundleCycles.splitHyperplaneEquation e) (DegreeOneCover.BundleCycles.symmetricGenerator_degree R M _) (SplitHyperplane.BundleCycles.splitHyperplaneEquation_regular e)
    (SplitHyperplane.BundleCycles.splitHyperplaneEquation_kernel e)
    (GradedMap.BundleCycles.symmetricGradedMap (SplitHyperplane.BundleCycles.splitHyperplaneQuotient e'))
    (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant _ (SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective e'))
    (SymmetricProjective.ClosedImmersion.BundleCycles.symmetricGradedMap_surjective _ (SplitHyperplane.BundleCycles.splitHyperplaneQuotient_surjective e'))
    (SplitHyperplane.BundleCycles.splitHyperplaneEquation e') (DegreeOneCover.BundleCycles.symmetricGenerator_degree R M _) (SplitHyperplane.BundleCycles.splitHyperplaneEquation_regular e')
    (SplitHyperplane.BundleCycles.splitHyperplaneEquation_kernel e')

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneIdealIso.BundleCycles
