import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.BaseChangeMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealPullbackIso

/-! # Cartier Base Change Ideal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChangeIdeal.BundleCycles

noncomputable section

/-! Base change of an actual flat relative Cartier divisor
preserves both its regular equations and its invertible ideal. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E D X Y : Scheme.{0}} (p : E ⟶ X) (q : D ⟶ X) [Flat q]
    (s : D ⟶ E) [IsClosedImmersion s] (hs : s ≫ p = q) (b : Y ⟶ X)
    (hreg : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s)

include hreg in
theorem relativeCartierBaseChangeMap_regular :
    Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals (BaseChangeMap.BundleCycles.relativeBaseChangeMap p q s hs b) := by
  let : Flat (s ≫ p) := hs.symm ▸ inferInstanceAs (Flat q)
  exact CartierBaseChange.BundleCycles.relativeCartier_regularPrincipalImageIdeals_baseChange p (pullback.snd p b)
    (pullback.fst p b) b (IsPullback.of_hasPullback p b) s
    (BaseChangeMap.BundleCycles.relativeBaseChangeMap p q s hs b) (pullback.fst q b)
    (BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p q s hs b) hreg

def relativeCartierBaseChangeMap_idealIso :
    ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg).pullback (pullback.fst p b)).sheaf ≅
      (Cartier.IdealBundle.Cycles.cartierIdealLineBundle (BaseChangeMap.BundleCycles.relativeBaseChangeMap p q s hs b)
        (relativeCartierBaseChangeMap_regular p q s hs b hreg)).sheaf :=
  Cartier.IdealPullbackIso.BundleCycles.cartierIdealPullbackIso s (BaseChangeMap.BundleCycles.relativeBaseChangeMap p q s hs b) _ _
    (BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p q s hs b) hreg
    (relativeCartierBaseChangeMap_regular p q s hs b hreg)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChangeIdeal.BundleCycles
