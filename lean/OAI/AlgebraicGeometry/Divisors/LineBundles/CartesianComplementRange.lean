import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.Localization

/-! # Cartesian Complement Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CartesianComplementRange.BundleCycles

/-! Actual cartesian inverse images preserve complementary ranges. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem cartesianComplement_range {X X' U U' Z Z' : Scheme.{0}}
    (f : X' ⟶ X) (i : U ⟶ X) (j : Z ⟶ X)
    (i' : U' ⟶ X') (j' : Z' ⟶ X') (u : U' ⟶ U) (z : Z' ⟶ Z)
    (hi : IsPullback i' u f i) (hj : IsPullback j' z f j)
    (hc : Set.range j = (Set.range i)ᶜ) : Set.range j' = (Set.range i')ᶜ := by
  rw [AffineBundle.Localization.Cycles.schemePullback_range f z j j' hj.flip, AffineBundle.Localization.Cycles.schemePullback_range f u i i' hi.flip,
    hc, Set.preimage_compl]

end OAI.AlgebraicGeometry.Divisors.LineBundles.CartesianComplementRange.BundleCycles
