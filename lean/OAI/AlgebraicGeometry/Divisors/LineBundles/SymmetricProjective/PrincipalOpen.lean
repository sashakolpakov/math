import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LocalizationRange
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Localization
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv

/-! # Principal Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.PrincipalOpen.BundleCycles

noncomputable section

/-! Actual principal coefficient localization gives an open immersion
between the projective spectra of the module's symmetric algebras. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N] (r : R) [IsLocalization.Away r S]
    (f : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers r) f]

theorem symmetricModuleMap_principalLocalization :
    letI := (Symmetric.LocalizationMap.BundleCycles.symmetricModuleMap (S := S) f).toAlgebra
    IsLocalization.Away (algebraMap R (SymmetricAlgebra R M) r) (SymmetricAlgebra S N) := by
  have h := Symmetric.LocalizationEquiv.BundleCycles.symmetricModuleMap_isLocalization M (Submonoid.powers r) S f
  simpa only [Symmetric.LocalizationLift.BundleCycles.symmetricDenominators, Submonoid.map_powers] using h

theorem localizedSymmetricProjectiveMap_isOpenImmersion :
    IsOpenImmersion (Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f) := by
  apply Projective.PrincipalLocalization.BundleCycles.projectivePrincipalLocalization_isOpenImmersion (Symmetric.Grading.BundleCycles.symmetricGrading R M) (Symmetric.Grading.BundleCycles.symmetricGrading S N)
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f))
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant _ _ (Localization.BundleCycles.localizedModule_span_range (S := S) (Submonoid.powers r) f))
    (algebraMap R (SymmetricAlgebra R M) r) (SetLike.algebraMap_mem_graded (Symmetric.Grading.BundleCycles.symmetricGrading R M) r)
  exact symmetricModuleMap_principalLocalization (S := S) r f

theorem localizedSymmetricProjectiveMap_range :
    Set.range (Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f) =
      Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading R M) (algebraMap R (SymmetricAlgebra R M) r) :=
  Projective.LocalizationRange.BundleCycles.projectivePrincipalLocalization_range (Symmetric.Grading.BundleCycles.symmetricGrading R M) (Symmetric.Grading.BundleCycles.symmetricGrading S N)
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f))
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant _ _ (Localization.BundleCycles.localizedModule_span_range (S := S) (Submonoid.powers r) f))
    (algebraMap R (SymmetricAlgebra R M) r) (symmetricModuleMap_principalLocalization (S := S) r f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.PrincipalOpen.BundleCycles
