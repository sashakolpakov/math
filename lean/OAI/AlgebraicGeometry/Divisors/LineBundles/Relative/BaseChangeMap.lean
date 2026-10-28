import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChartsPullback

/-! # Base Change Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.BaseChangeMap.BundleCycles

noncomputable section

/-! A morphism over a base induces an actual cartesian morphism
between its two base changes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E D X Y : Scheme.{0}} (p : E ⟶ X) (q : D ⟶ X)
    (s : D ⟶ E) (hs : s ≫ p = q) (b : Y ⟶ X)

def relativeBaseChangeMap : pullback q b ⟶ pullback p b :=
  pullback.lift (pullback.fst q b ≫ s) (pullback.snd q b)
    (by rw [Category.assoc, hs, pullback.condition])

theorem relativeBaseChangeMap_fst :
    relativeBaseChangeMap p q s hs b ≫ pullback.fst p b = pullback.fst q b ≫ s :=
  pullback.lift_fst _ _ _

theorem relativeBaseChangeMap_snd :
    relativeBaseChangeMap p q s hs b ≫ pullback.snd p b = pullback.snd q b :=
  pullback.lift_snd _ _ _

theorem relativeBaseChangeMap_isPullback :
    IsPullback (relativeBaseChangeMap p q s hs b) (pullback.fst q b) (pullback.fst p b) s := by
  have H : IsPullback (relativeBaseChangeMap p q s hs b ≫ pullback.snd p b)
      (pullback.fst q b) b (s ≫ p) := by
    rw [relativeBaseChangeMap_snd, hs]
    exact (IsPullback.of_hasPullback q b).flip
  exact H.of_right (relativeBaseChangeMap_fst p q s hs b) (IsPullback.of_hasPullback p b).flip

instance relativeBaseChangeMap_isClosedImmersion [IsClosedImmersion s] :
    IsClosedImmersion (relativeBaseChangeMap p q s hs b) :=
  MorphismProperty.of_isPullback (relativeBaseChangeMap_isPullback p q s hs b).flip inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.BaseChangeMap.BundleCycles
