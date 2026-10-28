import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowTransportLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.Localization.Cycles

noncomputable section

/-! # LineBundleCycles: surjectivity of bundle Chow pullback glues across an actual open/closed decomposition -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem schemePullback_range {E X E' U : Scheme.{0}}
    (p : E ⟶ X) (q : E' ⟶ U) (i : U ⟶ X) (j : E' ⟶ E) (h : IsPullback q j i p) :
    Set.range j = p ⁻¹' Set.range i := by
  simpa only [Set.preimage_univ, Set.image_univ] using Scheme.image_preimage_eq_of_isPullback h Set.univ

variable {E X EU U EZ Z : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian EU] [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian EZ] [AlgebraicGeometry.IsNoetherian Z]
    (p : E ⟶ X) (qU : EU ⟶ U) (qZ : EZ ⟶ Z)
    [Smooth p] [Smooth qU] [Smooth qZ]
    [GeometricallyIntegral p] [GeometricallyIntegral qU] [GeometricallyIntegral qZ]
    (i : U ⟶ X) (j : EU ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (k : Z ⟶ X) (l : EZ ⟶ E) [IsClosedImmersion k] [IsClosedImmersion l]
    (hsU : IsPullback qU j i p) (hsZ : IsPullback qZ l k p)
    (hcomp : Set.range k = (Set.range i)ᶜ)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ)
    (hp : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r) (hU : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank qU r)
    (hZ : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank qZ r)

include hsU hsZ hcomp in
theorem affineBundleChowExtension_surjective_of_open_closed (d : ℕ)
    (sU : Function.Surjective (ChowExtension.Cycles.affineBundleChowExtension qU (i ≫ f) r hU d))
    (sZ : Function.Surjective (ChowExtension.Cycles.affineBundleChowExtension qZ (k ≫ f) r hZ d)) :
    Function.Surjective (ChowExtension.Cycles.affineBundleChowExtension p f r hp d) := by
  intro a
  obtain ⟨aU, haU⟩ := sU
    (DimensionChow.BundleCycles.dimensionChowTransport (ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p qU i j hsU f) (d + r)
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + r) a))
  obtain ⟨b, hb⟩ := Open.ChowRestriction.BundleCycles.openChowRestriction_surjective i f d aU
  have hres : Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + r) (a - ChowExtension.Cycles.affineBundleChowExtension p f r hp d b) = 0 := by
    apply DimensionChowTransportLaws.BundleCycles.dimensionChowTransport_injective (ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p qU i j hsU f) (d + r)
    simp only [map_sub, map_zero]
    rw [ChowBaseChange.Cycles.affineBundleChowExtension_openRestriction p qU i j hsU f r hp hU, hb, haU, sub_self]
  have hcompE : Set.range l = (Set.range j)ᶜ := by
    rw [schemePullback_range p qZ k l hsZ, schemePullback_range p qU i j hsU, hcomp, Set.preimage_compl]
  obtain ⟨c, hc⟩ := (ChowLocalization.BundleCycles.openChowRestriction_eq_zero_iff j l hcompE (p ≫ f) (d + r)
    (a - ChowExtension.Cycles.affineBundleChowExtension p f r hp d b)).mp hres
  obtain ⟨bZ, hbZ⟩ := sZ (DimensionChow.BundleCycles.dimensionChowTransport (ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p qZ k l hsZ f) (d + r) c)
  refine ⟨b + Closed.ChowPushforward.BundleCycles.closedChowPushforward k f d bZ, ?_⟩
  rw [map_add, ChowBaseChange.Cycles.affineBundleChowExtension_closedPushforward p qZ k l hsZ f r hp hZ,
    hbZ, DimensionChowTransportLaws.BundleCycles.closedChowPushforwardOver_transport, hc]
  exact (add_comm _ _).trans (sub_add_cancel _ _)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.Localization.Cycles
