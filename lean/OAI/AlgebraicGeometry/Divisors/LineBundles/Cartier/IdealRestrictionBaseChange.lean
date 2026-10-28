import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso

/-! # Ideal Restriction Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealRestrictionBaseChange.BundleCycles

noncomputable section

/-! Restriction of the actual Cartier ideal to its divisor is
compatible with a genuine base change of the divisor. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def cartierIdealRestrictionBaseChangeIso {E D E' D' : Scheme.{0}}
    (s : D ⟶ E) [IsClosedImmersion s] (t : D' ⟶ E') [IsClosedImmersion t]
    (u : E' ⟶ E) (v : D' ⟶ D) (h : IsPullback t v u s)
    (hs : IdealBundle.Cycles.HasRegularPrincipalImageIdeals s) (ht : IdealBundle.Cycles.HasRegularPrincipalImageIdeals t)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : ((IdealBundle.Cycles.cartierIdealLineBundle s hs).pullback s).sheaf ≅ L.sheaf) :
    ((IdealBundle.Cycles.cartierIdealLineBundle t ht).pullback t).sheaf ≅ (L.pullback v).sheaf :=
  (LineBundle.PullbackIso.Cycles.lineBundlePullbackIso (IdealPullbackIso.BundleCycles.cartierIdealPullbackIso s t u v h hs ht) t).symm ≪≫
    LineBundle.PullbackIso.Cycles.lineBundlePullbackSquareIso (IdealBundle.Cycles.cartierIdealLineBundle s hs) L u s t v h.w e

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealRestrictionBaseChange.BundleCycles
