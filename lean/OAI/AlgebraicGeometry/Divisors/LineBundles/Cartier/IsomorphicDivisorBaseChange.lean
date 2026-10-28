import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso

/-! # Isomorphic Divisor Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IsomorphicDivisorBaseChange.BundleCycles

noncomputable section

/-! Base-changing a Cartier divisor that maps isomorphically to
the base gives another such divisor and the actual pulled ideal bundle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X D Y : Scheme.{0}} (p : E ⟶ X) (s : D ⟶ E)
    [IsClosedImmersion s] [IsIso (s ≫ p)] (b : Y ⟶ X)

def cartierIsomorphicDivisorBaseChangeInclusion :
    pullback (pullback.fst p b) s ⟶ pullback p b := pullback.fst (pullback.fst p b) s

instance cartierIsomorphicDivisorBaseChangeInclusion_isClosedImmersion :
    IsClosedImmersion (cartierIsomorphicDivisorBaseChangeInclusion p s b) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst (pullback.fst p b) s))

instance cartierIsomorphicDivisorBaseChange_over_isIso :
    IsIso (cartierIsomorphicDivisorBaseChangeInclusion p s b ≫ pullback.snd p b) :=
  ((IsPullback.of_hasPullback (pullback.fst p b) s).paste_horiz
    (IsPullback.of_hasPullback p b).flip).isIso_fst_of_isIso

theorem cartierIsomorphicDivisorBaseChange_regular
    (hs : IdealBundle.Cycles.HasRegularPrincipalImageIdeals s) :
    IdealBundle.Cycles.HasRegularPrincipalImageIdeals (cartierIsomorphicDivisorBaseChangeInclusion p s b) :=
  Relative.CartierBaseChange.BundleCycles.relativeCartier_regularPrincipalImageIdeals_baseChange p (pullback.snd p b) (pullback.fst p b) b
    (IsPullback.of_hasPullback p b) s (cartierIsomorphicDivisorBaseChangeInclusion p s b)
    (pullback.snd (pullback.fst p b) s) (IsPullback.of_hasPullback (pullback.fst p b) s) hs

def cartierIsomorphicDivisorBaseChange_idealIso (hs : IdealBundle.Cycles.HasRegularPrincipalImageIdeals s) :
    ((IdealBundle.Cycles.cartierIdealLineBundle s hs).pullback (pullback.fst p b)).sheaf ≅
      (IdealBundle.Cycles.cartierIdealLineBundle (cartierIsomorphicDivisorBaseChangeInclusion p s b)
        (cartierIsomorphicDivisorBaseChange_regular p s b hs)).sheaf :=
  IdealPullbackIso.BundleCycles.cartierIdealPullbackIso s (cartierIsomorphicDivisorBaseChangeInclusion p s b) (pullback.fst p b)
    (pullback.snd (pullback.fst p b) s) (IsPullback.of_hasPullback (pullback.fst p b) s)
    hs (cartierIsomorphicDivisorBaseChange_regular p s b hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IsomorphicDivisorBaseChange.BundleCycles
