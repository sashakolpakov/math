import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFiberIsoTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberProductOrigin

/-! # Composite Fiber Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompositeFiberTransport.Construction

noncomputable section

/-! Unfold a composite-source fiber transport through its two actual
pullback comparisons. This retains the geometric comparison square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

theorem iso_inverse_square_transport {C : Type*} [Category* C] {U V W X Y Z : C}
    (a : U ≅ V) (b : V ≅ W) (c : U ≅ X) (d : X ≅ W) (e : U ≅ Y) (f : Y ≅ Z)
    (h : a ≪≫ b = c ≪≫ d) :
    b.symm ≪≫ a.symm ≪≫ e ≪≫ f = d.symm ≪≫ c.symm ≪≫ e ≪≫ f := by
  simpa only [Iso.trans_symm, Iso.trans_assoc] using congrArg (fun v => v.symm ≪≫ e ≪≫ f) h

theorem iso_functor_inverse_square_transport {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Z : C} {V W U : D} (a : X ≅ Y) (e : X ≅ Z)
    (b : F.obj Y ≅ W) (c : F.obj X ≅ V) (d : V ≅ W) (f : F.obj Z ≅ U)
    (h : F.mapIso a ≪≫ b = c ≪≫ d) :
    b.symm ≪≫ F.mapIso (a.symm ≪≫ e) ≪≫ f = d.symm ≪≫ c.symm ≪≫ F.mapIso e ≪≫ f := by
  rw [Functor.mapIso_trans, Functor.mapIso_symm]
  simpa only [Iso.trans_assoc] using iso_inverse_square_transport (F.mapIso a) b c d (F.mapIso e) f h

set_option backward.isDefEq.respectTransparency false in
theorem globalFiberIsoTransport_eq_fiber {S : Scheme.{u}} {E Z T : Over S}
    (p q : E ⟶ Z) (L : Picard.PoincareBundle.Line.Bundles.LineBundle Z.left)
    (e : (L.pullback p.left).sheaf ≅ (L.pullback q.left).sheaf)
    (a : T ⟶ E) (x y : T ⟶ Z) (hx : a ≫ p = x) (hy : a ≫ q = y) :
    GlobalFiberIsoTransport.Construction.globalFiberIsoTransport p q L e a x y hx hy =
      (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L a p x hx).symm ≪≫ (Scheme.Modules.pullback a.left).mapIso e ≪≫
        Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L a q y hy := by
  unfold GlobalFiberIsoTransport.Construction.globalFiberIsoTransport
  rw [FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison, FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison]

theorem fiberPullbackIso_composite_square {S : Scheme.{u}} {E Z T : Over S}
    (p : E ⟶ E) (q : E ⟶ Z) (L : Picard.PoincareBundle.Line.Bundles.LineBundle Z.left)
    (a b : T ⟶ E) (x : T ⟶ Z) (hab : a ≫ p = b) (hx : b ≫ q = x)
    (hax : a ≫ (p ≫ q) = x) :
    (Scheme.Modules.pullback a.left).mapIso (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L p q (p ≫ q) rfl) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L a (p ≫ q) x hax =
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (L.pullback q.left) a p b hab ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L b q x hx := by
  have hs := Picard.PoincareBundle.GlobalFrameNaturality.comparison_pullback q L a p (p ≫ q) rfl b x hx hab hax
  rw [← FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison, ← FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison] at hs
  exact hs

set_option backward.isDefEq.respectTransparency false in
theorem globalFiberIsoTransport_composite_source {S : Scheme.{u}} {E Z T : Over S}
    (p : E ⟶ E) (q : E ⟶ Z) (L : Picard.PoincareBundle.Line.Bundles.LineBundle Z.left)
    (e : (Scheme.Modules.pullback p.left).obj (L.pullback q.left).sheaf ≅ (L.pullback q.left).sheaf)
    (a b : T ⟶ E) (x y : T ⟶ Z) (hab : a ≫ p = b) (hx : b ≫ q = x) (hy : a ≫ q = y)
    (hax : a ≫ (p ≫ q) = x) :
    GlobalFiberIsoTransport.Construction.globalFiberIsoTransport (p ≫ q) q L
      ((Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L p q (p ≫ q) rfl).symm ≪≫ e) a x y hax hy =
      (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L b q x hx).symm ≪≫
        (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (L.pullback q.left) a p b hab).symm ≪≫
          (Scheme.Modules.pullback a.left).mapIso e ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L a q y hy := by
  have hs := fiberPullbackIso_composite_square p q L a b x hab hx hax
  have he := iso_functor_inverse_square_transport (Scheme.Modules.pullback a.left)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L p q (p ≫ q) rfl) e (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L a (p ≫ q) x hax)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (L.pullback q.left) a p b hab) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L b q x hx)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L a q y hy) hs
  exact (globalFiberIsoTransport_eq_fiber (p ≫ q) q L
    ((Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L p q (p ≫ q) rfl).symm ≪≫ e) a x y hax hy).trans he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompositeFiberTransport.Construction
