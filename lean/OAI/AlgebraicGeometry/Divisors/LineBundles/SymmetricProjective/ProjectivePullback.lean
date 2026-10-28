import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.PrincipalOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ScalarOpen

/-! # Projective Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback.BundleCycles

noncomputable section

/-! The actual projective symmetric construction has the expected
principal-open pullback over the coefficient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem symmetricProjectiveToBase_preimage_basicOpen (r : R) :
    Scheme.BundleCycles.symmetricProjectiveToBase R M ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens) =
      Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading R M) (algebraMap R (SymmetricAlgebra R M) r) := by
  ext p
  exact not_congr (Projective.ScalarOpen.BundleCycles.projectiveToSpecZero_mem (Symmetric.Grading.BundleCycles.symmetricGrading R M) p (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M r))

variable {R M} {S N : Type} [CommRing S] [Algebra R S] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (r : R) [IsLocalization.Away r S] (f : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers r) f]

theorem symmetricProjective_principal_isPullback :
    IsPullback (Scheme.BundleCycles.symmetricProjectiveToBase S N)
      (Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Scheme.BundleCycles.symmetricProjectiveToBase R M) := by
  let := PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_isOpenImmersion (S := S) r f
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) := IsOpenImmersion.of_isLocalization r
  apply IsOpenImmersion.isPullback
  · exact Base.BundleCycles.symmetricScalarProjectiveMap_over (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f)
      (Localization.BundleCycles.localizedModule_span_range (S := S) (Submonoid.powers r) f)
  · have hS : Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := PrimeSpectrum.localization_away_comap_range S r
    have hP := PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_range (S := S) r f
    ext p
    change Scheme.BundleCycles.symmetricProjectiveToBase R M p ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔
      p ∈ Set.range (Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f)
    rw [hS, hP]
    exact SetLike.ext_iff.mp (symmetricProjectiveToBase_preimage_basicOpen R M r) p

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback.BundleCycles
