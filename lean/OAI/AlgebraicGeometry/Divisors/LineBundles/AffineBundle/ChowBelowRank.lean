import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.Localization
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.TrivialChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ComplementInduction
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChowVanishing

/-! # Chow Below Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBelowRank.Cycles

noncomputable section

section

/-! # LineBundleCycles: Noetherian induction for actual affine-space bundle Chow surjectivity -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

/-- The induction assertion ranges over every closed scheme with the given
underlying closed image; it includes nonreduced and reducible closed schemes. -/
def AffineBundleSurjectiveOnClosed {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (r : ℕ) (S : Closeds X) : Prop :=
  ∀ (Z : Scheme.{0}) [AlgebraicGeometry.IsNoetherian Z] (i : Z ⟶ X) [IsClosedImmersion i],
    Set.range i = (S : Set X) →
    ∀ (g : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g], i ≫ f = g →
      ∀ (E : Scheme.{0}) [AlgebraicGeometry.IsNoetherian E] (p : E ⟶ Z) [Smooth p] [GeometricallyIntegral p]
        (h : LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r) (d : ℕ), Function.Surjective (ChowExtension.Cycles.affineBundleChowExtension p g r h d)

theorem affineBundleSurjectiveOnClosed_step {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (r : ℕ)
    (S : Closeds X) (ih : ∀ T : Closeds X, T < S → AffineBundleSurjectiveOnClosed f r T) :
    AffineBundleSurjectiveOnClosed f r S := by
  intro Z _ i _ hi g _ hgi E _ p _ _ hp d
  cases isEmpty_or_nonempty Z with
  | inl hz =>
    let := hz
    exact ChowExtension.Cycles.affineBundleChowExtension_surjective_of_isEmpty p g r hp d
  | inr hn =>
    let z : Z := Classical.choice hn
    obtain ⟨U, u, ι, hι, j, hu, hj, hz, hs, hr⟩ := hp z
    let := hι
    let := hu
    let := hj
    have : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian u
    let C := Open.ClosedComplement.BundleCycles.openComplementScheme u
    let k : C ⟶ Z := Open.ClosedComplement.BundleCycles.openComplementInclusion u
    have : IsClosedImmersion k := Open.ClosedComplement.BundleCycles.openComplementInclusion_isClosedImmersion u
    have : AlgebraicGeometry.IsNoetherian C := Open.ClosedComplement.BundleCycles.openComplementScheme_isNoetherian u
    let EC : Scheme := pullback p k
    let qC : EC ⟶ C := pullback.snd p k
    let l : EC ⟶ E := pullback.fst p k
    have : IsClosedImmersion l := inferInstanceAs (IsClosedImmersion (pullback.fst p k))
    have : AlgebraicGeometry.IsNoetherian EC := Open.ClosedComplement.BundleCycles.closedImmersion_isNoetherian l
    have : Smooth qC := inferInstanceAs (Smooth (pullback.snd p k))
    have : GeometricallyIntegral qC := inferInstanceAs (GeometricallyIntegral (pullback.snd p k))
    have hU : LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank (AffineSpace ι U ↘ U) r := by
      rw [← hr]
      exact TrivialChow.Cycles.affineSpaceTrivialization_hasChartsOfRank (AffineSpace ι U ↘ U) ι (Iso.refl _)
        (Category.id_comp _)
    have sU : Function.Surjective (ChowExtension.Cycles.affineBundleChowExtension (AffineSpace ι U ↘ U) (u ≫ g) r hU d) := by
      subst r
      exact (TrivialChow.Cycles.affineBundleChowExtension_trivial_bijective (AffineSpace ι U ↘ U) (u ≫ g) ι hU
        (Iso.refl _) (Category.id_comp _) d).2
    have sC : Function.Surjective (ChowExtension.Cycles.affineBundleChowExtension qC (k ≫ g) r (hp.baseChange k) d) := by
      have hc := ih (Closed.ComplementInduction.BundleCycles.openComplementImageClosed i u) (Closed.ComplementInduction.BundleCycles.openComplementImageClosed_lt i u S hi z hz)
      exact hc C (k ≫ i) rfl (k ≫ g)
        ((Category.assoc _ _ _).trans (congrArg (fun a => k ≫ a) hgi)) EC qC (hp.baseChange k) d
    exact Localization.Cycles.affineBundleChowExtension_surjective_of_open_closed p (AffineSpace ι U ↘ U) qC u j k l hs
      (IsPullback.of_hasPullback p k).flip (Open.ClosedComplement.BundleCycles.openComplementInclusion_range u) g r hp hU
      (hp.baseChange k) d sU sC

theorem affineBundleSurjectiveOnClosed_all {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (r : ℕ) (S : Closeds X) : AffineBundleSurjectiveOnClosed f r S :=
  wellFounded_lt.induction S (affineBundleSurjectiveOnClosed_step f r)

end

/-! Chow groups below the relative rank vanish for actual affine-space
bundles, by localization and Noetherian induction on their base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

def AffineBundleLowChowOnClosed {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (r : ℕ) (S : Closeds X) : Prop :=
  ∀ (Z : Scheme.{0}) [AlgebraicGeometry.IsNoetherian Z] (i : Z ⟶ X) [IsClosedImmersion i],
    Set.range i = (S : Set X) →
    ∀ (g : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g], i ≫ f = g →
      ∀ (E : Scheme.{0}) [AlgebraicGeometry.IsNoetherian E] (p : E ⟶ Z) [Smooth p] [GeometricallyIntegral p],
        LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r → ∀ (d : ℕ), d < r → ∀ α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ g) d, α = 0

theorem affineBundleLowChowOnClosed_step {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (r : ℕ)
    (S : Closeds X) (ih : ∀ T : Closeds X, T < S → AffineBundleLowChowOnClosed f r T) :
    AffineBundleLowChowOnClosed f r S := by
  intro Z _ i _ hi g _ hgi E _ p _ _ hp d hd α
  cases isEmpty_or_nonempty Z with
  | inl hz =>
    let := hz
    let : IsEmpty E := ⟨fun e => isEmptyElim (p e)⟩
    exact ChowExtension.Cycles.dimensionChow_eq_zero_of_isEmpty (p ≫ g) d α
  | inr hn =>
    let z : Z := Classical.choice hn
    obtain ⟨U, u, ι, hι, j, hu, hj, hz, hs, hr⟩ := hp z
    let := hι
    let := hu
    let := hj
    let : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian u
    let C := Open.ClosedComplement.BundleCycles.openComplementScheme u
    let k : C ⟶ Z := Open.ClosedComplement.BundleCycles.openComplementInclusion u
    let : IsClosedImmersion k := Open.ClosedComplement.BundleCycles.openComplementInclusion_isClosedImmersion u
    let : AlgebraicGeometry.IsNoetherian C := Open.ClosedComplement.BundleCycles.openComplementScheme_isNoetherian u
    let EC : Scheme := pullback p k
    let qC : EC ⟶ C := pullback.snd p k
    let l : EC ⟶ E := pullback.fst p k
    let : IsClosedImmersion l := inferInstanceAs (IsClosedImmersion (pullback.fst p k))
    let : AlgebraicGeometry.IsNoetherian EC := Open.ClosedComplement.BundleCycles.closedImmersion_isNoetherian l
    let : Smooth qC := inferInstanceAs (Smooth (pullback.snd p k))
    let : GeometricallyIntegral qC := inferInstanceAs (GeometricallyIntegral (pullback.snd p k))
    have hres : Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ g) d α = 0 := by
      apply DimensionChowTransportLaws.BundleCycles.dimensionChowTransport_injective (ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p (AffineSpace ι U ↘ U) u j hs g) d
      rw [map_zero]
      exact LineBundles.AffineSpace.ChowVanishing.BundleCycles.affineSpace_chow_eq_zero_below_rank U (u ≫ g) ι d (hr.symm ▸ hd) _
    have hcomp : Set.range l = (Set.range j)ᶜ := by
      rw [Localization.Cycles.schemePullback_range p qC k l (IsPullback.of_hasPullback p k).flip,
        Localization.Cycles.schemePullback_range p (AffineSpace ι U ↘ U) u j hs,
        Open.ClosedComplement.BundleCycles.openComplementInclusion_range u, Set.preimage_compl]
    obtain ⟨c, hc⟩ := (ChowLocalization.BundleCycles.openChowRestriction_eq_zero_iff j l hcomp (p ≫ g) d α).mp hres
    have hczero : c = 0 := by
      apply DimensionChowTransportLaws.BundleCycles.dimensionChowTransport_injective
        (ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p qC k l (IsPullback.of_hasPullback p k).flip g) d
      rw [map_zero]
      have H := ih (Closed.ComplementInduction.BundleCycles.openComplementImageClosed i u) (Closed.ComplementInduction.BundleCycles.openComplementImageClosed_lt i u S hi z hz)
      exact H C (k ≫ i) rfl (k ≫ g)
        ((Category.assoc _ _ _).trans (congrArg (fun a => k ≫ a) hgi)) EC qC (hp.baseChange k) d hd _
    rw [← hc, hczero, map_zero]

theorem affineBundleLowChowOnClosed_all {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (r : ℕ) (S : Closeds X) : AffineBundleLowChowOnClosed f r S :=
  wellFounded_lt.induction S (affineBundleLowChowOnClosed_step f r)

theorem affineBundle_chow_eq_zero_below_rank {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r)
    (d : ℕ) (hd : d < r) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) : α = 0 := by
  apply affineBundleLowChowOnClosed_all f r ⊤ X (𝟙 X) _ f (Category.id_comp f) E p h d hd α
  ext x
  simp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBelowRank.Cycles
