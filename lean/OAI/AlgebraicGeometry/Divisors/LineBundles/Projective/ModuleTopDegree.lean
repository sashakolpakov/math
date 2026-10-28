import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveChartTopDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Localization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ProjectiveProperties
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.BasisSourceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.RankCommonOpen

/-! # Module Top Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleTopDegree.BundleCycles

noncomputable section

/-! The actual augmented projective bundle of a finite projective
module has the expected top degree over an integral affine base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (n : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) n)

theorem projectiveModuleChow_top_degree (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d)
    (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
        (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) d n
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f n hp d α)) =
      (-1 : ℚ) ^ n • α := by
  obtain ⟨a, ha, κ, hκ, ⟨b⟩⟩ := ModuleLocalBasis.BundleCycles.projectiveModule_exists_localBasis M (⊥ : Ideal R)
  let := hκ
  let := Fintype.ofFinite κ
  let S := Localization.Away a
  let N := LocalizedModule.Away a M
  let m : M →ₗ[R] N := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let : IsDomain S := Localization.Away.isDomain ha
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers a) S inferInstance
  let : Module.Finite S N := Module.Finite.of_isLocalizedModule (Submonoid.powers a) m
  let p := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)
  let q := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N)
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let am : R × M →ₗ[R] S × N := Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap (S := S) m
  let j := SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers a) am
  let : IsOpenImmersion i := IsOpenImmersion.of_isLocalization a
  let : IsOpenImmersion j := SymmetricProjective.PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_isOpenImmersion (S := S) a
    am
  have hq := Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_sourceCharts b
  let : Smooth q := hq.forget.smooth
  let : GeometricallyIntegral q := Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_geometricallyIntegral b
  have hs : IsPullback q j i p := Augmented.ModuleLocalization.BundleCycles.symmetricAugmentedProjective_principal_isPullback (S := S) a m
  have hk : n = Nat.card κ :=
    AffineSource.RankCommonOpen.BundleCycles.affineSpaceSourceRank_openSquare p q i j hs.w f n (Nat.card κ) hp hq (genericPoint (Spec (.of S)))
  have hq' : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q n := hk.symm ▸ hq
  exact Free.ProjectiveChartTopDegree.BundleCycles.freeProjectiveChart_top_degree p f (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M) b i j hs
    (SymmetricInfinity.Localization.BundleCycles.symmetricInfinity_localization_idealIso a m) n hk.symm hp hq' d hd α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleTopDegree.BundleCycles
