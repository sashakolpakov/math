import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowRetraction
import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChowVanishing

/-! # Affine Source Chow Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSourceChowLocalization.BundleCycles

noncomputable section

section

/-! Chow localization for an actual affine-space open splits off
the base summand. The residual class comes from the actual closed complement. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (ι : Type) [Finite ι]
    (h : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (Nat.card ι))
    (j : AffineSpace ι X ⟶ E) [IsOpenImmersion j]
    (hj : j ≫ p = (AffineSpace ι X ↘ X))
    (k : Z ⟶ E) [IsClosedImmersion k] (hk : Set.range k = (Set.range j)ᶜ)

omit [GeometricallyIntegral p] in
theorem affineSourceChowRetraction_zero_iff (d : ℕ)
    (a : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + Nat.card ι)) :
    AffineSource.ChowRetraction.BundleCycles.affineSourceChowRetraction p f ι j hj d a = 0 ↔
      Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + Nat.card ι) a = 0 := by
  constructor
  · intro ha
    change (FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d).symm (DimensionChow.BundleCycles.dimensionChowTransport _ _
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + Nat.card ι) a)) = 0 at ha
    apply DimensionChowTransportLaws.BundleCycles.dimensionChowTransport_injective (AffineSource.ChowRetraction.BundleCycles.affineSourceChart_structureMap p f ι j hj) (d + Nat.card ι)
    apply (FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d).symm.injective
    simpa only [map_zero] using ha
  · intro ha
    change (FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d).symm (DimensionChow.BundleCycles.dimensionChowTransport _ _
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + Nat.card ι) a)) = 0
    rw [ha, map_zero, map_zero]

include hk in
omit [GeometricallyIntegral p] in
theorem affineSourceChowRetraction_closed (d : ℕ)
    (a : DimensionChow.BundleCycles.DimensionChowQ (k ≫ (p ≫ f)) (d + Nat.card ι)) :
    AffineSource.ChowRetraction.BundleCycles.affineSourceChowRetraction p f ι j hj d
      (Closed.ChowPushforward.BundleCycles.closedChowPushforward k (p ≫ f) (d + Nat.card ι) a) = 0 :=
  (affineSourceChowRetraction_zero_iff p f ι j hj d _).mpr
    (ChowLocalization.BundleCycles.openChowRestriction_closed j k hk (p ≫ f) (d + Nat.card ι) a)

include hk in
theorem affineSourceChow_decomposition (d : ℕ)
    (a : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + Nat.card ι)) :
    ∃ b : DimensionChow.BundleCycles.DimensionChowQ (k ≫ (p ≫ f)) (d + Nat.card ι),
      a = LineBundles.AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (Nat.card ι) h d
        (AffineSource.ChowRetraction.BundleCycles.affineSourceChowRetraction p f ι j hj d a) +
          Closed.ChowPushforward.BundleCycles.closedChowPushforward k (p ≫ f) (d + Nat.card ι) b := by
  let c := LineBundles.AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (Nat.card ι) h d
    (AffineSource.ChowRetraction.BundleCycles.affineSourceChowRetraction p f ι j hj d a)
  have hz : AffineSource.ChowRetraction.BundleCycles.affineSourceChowRetraction p f ι j hj d (a - c) = 0 := by
    rw [map_sub, AffineSource.ChowRetraction.BundleCycles.affineSourceChowRetraction_extension p f ι h j hj]
    exact sub_self _
  obtain ⟨b, hb⟩ := (ChowLocalization.BundleCycles.openChowRestriction_eq_zero_iff j k hk (p ≫ f) (d + Nat.card ι) (a - c)).mp
    ((affineSourceChowRetraction_zero_iff p f ι j hj d (a - c)).mp hz)
  refine ⟨b, ?_⟩
  rw [hb]
  change a = c + (a - c)
  abel

include hk in
theorem affineSourceChow_decomposition_base_unique (d : ℕ)
    (a : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + Nat.card ι)) (c : DimensionChow.BundleCycles.DimensionChowQ f d)
    (b : DimensionChow.BundleCycles.DimensionChowQ (k ≫ (p ≫ f)) (d + Nat.card ι))
    (ha : a = LineBundles.AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (Nat.card ι) h d c +
      Closed.ChowPushforward.BundleCycles.closedChowPushforward k (p ≫ f) (d + Nat.card ι) b) :
    AffineSource.ChowRetraction.BundleCycles.affineSourceChowRetraction p f ι j hj d a = c := by
  rw [ha, map_add, AffineSource.ChowRetraction.BundleCycles.affineSourceChowRetraction_extension p f ι h j hj,
    affineSourceChowRetraction_closed p f ι j hj k hk, add_zero]

omit [GeometricallyIntegral p] in
include hj hk in
theorem affineSourceChow_from_complement_below_rank (d : ℕ) (hd : d < Nat.card ι)
    (a : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :
    ∃ b : DimensionChow.BundleCycles.DimensionChowQ (k ≫ (p ≫ f)) d, Closed.ChowPushforward.BundleCycles.closedChowPushforward k (p ≫ f) d b = a := by
  apply (ChowLocalization.BundleCycles.openChowRestriction_eq_zero_iff j k hk (p ≫ f) d a).mp
  apply DimensionChowTransportLaws.BundleCycles.dimensionChowTransport_injective (AffineSource.ChowRetraction.BundleCycles.affineSourceChart_structureMap p f ι j hj) d
  rw [map_zero]
  exact LineBundles.AffineSpace.ChowVanishing.BundleCycles.affineSpace_chow_eq_zero_below_rank X f ι d hd _

end

/-! Chow localization with an explicitly identified affine rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSourceChow_decomposition_rank {E X Z : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (ι : Type) [Finite ι]
    (r : ℕ) (hr : Nat.card ι = r) (hp : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)
    (j : AffineSpace ι X ⟶ E) [IsOpenImmersion j] (hj : j ≫ p = (AffineSpace ι X ↘ X))
    (s : Z ⟶ E) [IsClosedImmersion s] (hs : Set.range s = (Set.range j)ᶜ)
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + r)) :
    ∃ (c : DimensionChow.BundleCycles.DimensionChowQ f d) (β : DimensionChow.BundleCycles.DimensionChowQ (s ≫ (p ≫ f)) (d + r)),
      α = LineBundles.AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d c + Closed.ChowPushforward.BundleCycles.closedChowPushforward s (p ≫ f) (d + r) β := by
  subst r
  obtain ⟨β, hβ⟩ := affineSourceChow_decomposition p f ι hp j hj s hs d α
  exact ⟨_, β, hβ⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSourceChowLocalization.BundleCycles
