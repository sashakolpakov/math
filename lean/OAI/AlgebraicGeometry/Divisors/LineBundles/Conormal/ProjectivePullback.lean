import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ConormalLocalization

/-! # Projective Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectivePullback.BundleCycles

noncomputable section

/-! Principal localization gives a genuine pullback of augmented
conormal projective spectra over the quotient coefficient spectra. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S]

attribute [local instance] QuotientLocalization.BundleCycles.conormalQuotientAlgebra QuotientLocalization.BundleCycles.conormalQuotientModule

include r in
theorem conormalProjective_principal_isPullback (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hIJ : I ≤ J.comap (algebraMap R S))
    (hg : HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading (S ⧸ J) ((S ⧸ J) × J.Cotangent)) ≤
      (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading (R ⧸ I) ((R ⧸ I) × I.Cotangent))).map
        (Augmented.ConormalRestriction.BundleCycles.augmentedConormalGradedRestriction I J (algebraMap R S) hIJ)) :
    IsPullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase (S ⧸ J) ((S ⧸ J) × J.Cotangent))
      (Proj.map (Augmented.ConormalRestriction.BundleCycles.augmentedConormalGradedRestriction I J (algebraMap R S) hIJ) hg)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap R S) hIJ)))
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase (R ⧸ I) ((R ⧸ I) × I.Cotangent)) := by
  subst J
  let : IsLocalization.Away (Ideal.Quotient.mk I r) (S ⧸ I.map (algebraMap R S)) := by
    simpa only [Submonoid.map_powers] using QuotientLocalization.BundleCycles.quotientLocalizationMap_isLocalization (Submonoid.powers r) S I
  let : IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk I r))
      (QuotientLocalization.BundleCycles.conormalQuotientLocalizationMap I S) := by
    simpa only [Submonoid.map_powers] using
      QuotientLocalization.BundleCycles.conormalQuotientLocalizationMap_isLocalizedModule I S (Submonoid.powers r)
  exact SymmetricProjective.ProjectivePullback.BundleCycles.symmetricProjective_principal_isPullback (S := S ⧸ I.map (algebraMap R S))
    (Ideal.Quotient.mk I r)
    (Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap (S := S ⧸ I.map (algebraMap R S))
      (QuotientLocalization.BundleCycles.conormalQuotientLocalizationMap I S))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectivePullback.BundleCycles
