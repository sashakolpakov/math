import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Principal Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.PrincipalChart.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual principal-open charts of a conormal symmetric spectrum -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (r : R)

instance symmetricPrincipalChart_isLocalization :
    IsLocalization.Away (algebraMap R (SymmetricAlgebra R M) r)
      (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r)) := by
  have h : IsLocalization (LocalizationLift.BundleCycles.symmetricDenominators M (Submonoid.powers r))
      (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r)) := inferInstance
  simpa only [LocalizationLift.BundleCycles.symmetricDenominators, Submonoid.map_powers] using h

def symmetricPrincipalChartInclusion :
    Spec (.of (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r))) ⟶
      Spec (.of (SymmetricAlgebra R M)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (SymmetricAlgebra R M)
    (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r))))

instance symmetricPrincipalChartInclusion_isOpenImmersion :
    IsOpenImmersion (symmetricPrincipalChartInclusion M r) :=
  IsOpenImmersion.of_isLocalization (algebraMap R (SymmetricAlgebra R M) r)

def symmetricPrincipalChartProjection :
    Spec (.of (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r))) ⟶
      Spec (.of (Localization.Away r)) :=
  Spec.map (CommRingCat.ofHom
    (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M (Submonoid.powers r) (Localization.Away r)))

theorem symmetricPrincipalChartInclusion_range :
    Set.range (symmetricPrincipalChartInclusion M r) =
      (PrimeSpectrum.basicOpen (algebraMap R (SymmetricAlgebra R M) r) :
        Set (PrimeSpectrum (SymmetricAlgebra R M))) :=
  PrimeSpectrum.localization_away_comap_range _ _

theorem symmetricPrincipalChart_isPullback :
    IsPullback (symmetricPrincipalChartInclusion M r)
      (symmetricPrincipalChartProjection M r)
      (Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
  apply isPullback_SpecMap_of_isPushout
  apply CommRingCat.isPushout_of_isLocalization (algebraMap R (SymmetricAlgebra R M))
    (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M (Submonoid.powers r) (Localization.Away r))
    _ (Submonoid.powers r)
  apply RingHom.ext
  intro a
  exact (LocalizationLift.BundleCycles.localizedSymmetricScalarMap_algebraMap M (Submonoid.powers r)
    (Localization.Away r) a).trans
    (IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M)
      (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r)) a)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.PrincipalChart.BundleCycles
