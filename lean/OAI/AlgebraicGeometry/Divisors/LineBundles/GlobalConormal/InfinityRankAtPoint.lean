import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.RestrictedChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.FreeInfinityCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.TopDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealRestrictionBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRankOpen

/-! # Infinity Rank At Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityRankAtPoint.BundleCycles

noncomputable section

/-! At each point of positive affine conormal rank, the actual infinity
divisor has a free infinity chart of one lower rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    [GeometricallyIntegral (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker)]
    (f : s.ker.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    [GeometricallyIntegral (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker)] (r : ℕ)

include p hs in
theorem globalConormalInfinity_hasFreeChart_of_fiberRank (z : s.ker.subscheme)
    (hz : AffineBundle.FiberRank.Cycles.affineBundleFiberRank (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) f z = r + 1) :
    ∃ C : Free.ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart (Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport s.ker)
      ((InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle s.ker).pullback (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion s.ker)) z,
      C.rank = r := by
  classical
  obtain ⟨U, hU, hfinite, hprojective⟩ := Global.SectionProjectiveModuleChart.BundleCycles.globalSection_exists_projectiveModuleChart p s hs z
  let R := Γ(Y, U.1) ⧸ s.ker.ideal U
  let M := (s.ker.ideal U).Cotangent
  let : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  let : IsNoetherianRing R := inferInstance
  let : Module.Finite R M := hfinite
  let : Module.Projective R M := hprojective
  let i₁ : Spec (.of R) ⟶ s.ker.subscheme := Support.Projection.BundleCycles.supportCoefficientChart s.ker U
  have hU' : z ∈ Set.range i₁ := hU
  obtain ⟨x, hx⟩ := hU'
  let : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨a, ha, κ, hκ, ⟨basis⟩⟩ := LineBundles.Projective.ModuleLocalBasis.BundleCycles.projectiveModule_exists_localBasis M x.asIdeal
  let := hκ
  let := Fintype.ofFinite κ
  let S := Localization.Away a
  let N := LocalizedModule.Away a M
  let m : M →ₗ[R] N := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let am : R × M →ₗ[R] S × N := Augmented.ModuleLocalization.BundleCycles.augmentedModuleLocalizationMap (S := S) m
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers a) S inferInstance
  let : Module.Finite S N := Module.Finite.of_isLocalizedModule (Submonoid.powers a) m
  let i₀ : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let j₀ := SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers a) am
  let k₀ := SymmetricProjective.Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers a) m
  let j₁ : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) ⟶ Conormal.ProjectiveGluing.BundleCycles.globalConormalProjective s.ker :=
    (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover s.ker).f U
  let k₁ : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M ⟶ Conormal.InfinityGluing.BundleCycles.globalConormalInfinity s.ker :=
    (Conormal.InfinityGluing.BundleCycles.globalConormalInfinityCover s.ker).f U
  let : IsOpenImmersion i₀ := IsOpenImmersion.of_isLocalization a
  let : IsOpenImmersion j₀ := SymmetricProjective.PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_isOpenImmersion (S := S) a am
  let : IsOpenImmersion k₀ := SymmetricProjective.PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_isOpenImmersion (S := S) a m
  let : IsOpenImmersion i₁ := Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion s.ker U
  let : IsOpenImmersion j₁ := Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveCover_isOpenImmersion s.ker U
  let : IsOpenImmersion k₁ := Conormal.InfinitySupport.BundleCycles.globalConormalInfinityCover_isOpenImmersion s.ker U
  have hP : IsPullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N)) (j₀ ≫ j₁)
      (i₀ ≫ i₁) (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) :=
    (Augmented.ModuleLocalization.BundleCycles.symmetricAugmentedProjective_principal_isPullback (S := S) a m).paste_vert
      (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport_chart_isPullback s.ker U)
  have hD : IsPullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S N) (k₀ ≫ k₁)
      (i₀ ≫ i₁) (Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport s.ker) :=
    (SymmetricProjective.ProjectivePullback.BundleCycles.symmetricProjective_principal_isPullback (S := S) a m).paste_vert
      (Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport_chart_isPullback s.ker U)
  have hI : IsPullback (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion S N) (k₀ ≫ k₁)
      (j₀ ≫ j₁) (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion s.ker) :=
    (SymmetricInfinity.Localization.BundleCycles.symmetricInfinity_localization_isPullback (S := S) a m).paste_vert
      (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion_chart_isPullback s.ker U)
  have hx₀ : x ∈ Set.range i₀ := by
    have he : Set.range i₀ = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) :=
      PrimeSpectrum.localization_away_comap_range S a
    exact he.symm ▸ ha
  obtain ⟨u, hu⟩ := hx₀
  have huz : (i₀ ≫ i₁) u = z := (congrArg i₁ hu).trans hx
  have hq := Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_sourceCharts basis
  let : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N)) :=
    Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_geometricallyIntegral basis
  have hdim := AffineBundle.FiberRankOpen.Cycles.affineBundleFiberRank_commonOpen (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker)
    (Conormal.SupportCover.BundleCycles.globalConormalToSupport s.ker) (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase S (S × N))
    (Compactification.BundleCycles.globalConormalCompactification s.ker) (j₀ ≫ j₁) (i₀ ≫ i₁)
    (Conormal.ProjectiveProper.BundleCycles.globalConormalCompactification_toSupport s.ker) hP.w f (Nat.card κ) hq u
  rw [huz, hz] at hdim
  have hr : r + 1 = Nat.card κ := hdim
  have hκpos : 0 < Fintype.card κ := by rw [← Nat.card_eq_fintype_card, ← hr]; omega
  let : Nonempty κ := Fintype.card_pos_iff.mp hκpos
  let idx : κ := Classical.choice inferInstance
  let C := SymmetricInfinity.RestrictedChart.BundleCycles.symmetricInfinityRestriction_freeChart basis idx u
  let L := (InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle s.ker).pullback (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion s.ker)
  let e := Cartier.IdealRestrictionBaseChange.BundleCycles.cartierIdealRestrictionBaseChangeIso (InfinityInclusion.BundleCycles.globalConormalInfinityInclusion s.ker)
    (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion S N) (j₀ ≫ j₁) (k₀ ≫ k₁) hI
    (InfinityBundle.Cycles.globalConormalInfinity_regularPrincipalImageIdeals s.ker)
    (SymmetricInfinity.Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals S N) L (Iso.refl _)
  have H : ∃ C' : Free.ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart (Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport s.ker) L ((i₀ ≫ i₁) u),
      C'.rank = r := by
    refine ⟨C.compOpen (Conormal.InfinitySupport.BundleCycles.globalConormalInfinityToSupport s.ker) (i₀ ≫ i₁) (k₀ ≫ k₁) hD L e.symm, ?_⟩
    change C.rank = r
    dsimp only [C]
    rw [SymmetricInfinity.RestrictedChart.BundleCycles.symmetricInfinityRestriction_freeChart_rank, ← hr]
    omega
  exact huz ▸ H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.InfinityRankAtPoint.BundleCycles
