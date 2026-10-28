import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedRankChartIntersections

/-! # Locus Pullback From Ambient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocusPullbackFromAmbient.Construction

/-! A closed-locus pullback is obtained by lifting first through the ambient square. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
theorem locusPullbackFromAmbient {C : Type*} [Category C]
    {K B D U V W Z : C}
    (a : K ⟶ B) (b : K ⟶ D) (l : K ⟶ U)
    (p : B ⟶ V) (q : D ⟶ W) (r : U ⟶ V) (s : U ⟶ W)
    (f : V ⟶ Z) (g : W ⟶ Z)
    [Mono a] [Mono (q ≫ g)]
    (hc : a ≫ (p ≫ f) = b ≫ (q ≫ g))
    (hp : IsPullback r s f g) (hl : IsPullback a l p r) :
    IsPullback a b (p ≫ f) (q ≫ g) := by
  apply IsPullback.mk'
  · exact hc
  · intro T v w h _
    exact (cancel_mono a).mp h
  · intro T v w h
    have ha : (v ≫ p) ≫ f = (w ≫ q) ≫ g := by
      simpa only [Category.assoc] using h
    let x := hp.lift (v ≫ p) (w ≫ q) ha
    have hx : x ≫ r = v ≫ p := hp.lift_fst _ _ ha
    let y := hl.lift v x hx.symm
    have hy : y ≫ a = v := hl.lift_fst _ _ hx.symm
    refine ⟨y, hy, ?_⟩
    apply (cancel_mono (q ≫ g)).mp
    rw [Category.assoc, ← hc, ← Category.assoc, hy]
    exact h

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocusPullbackFromAmbient.Construction
