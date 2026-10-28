import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms

/-! # Fiber Section Iso Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberSectionIsoTransport.Construction

noncomputable section

/-! A commuting isomorphism square transports the native pullback
law of a fiber section to the corresponding output fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

universe u

theorem fiberSection_iso_transport_natural {S : Scheme.{u}} {E T T' : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (f : T' ⟶ T)
    (x y : T ⟶ E) (x' y' : T' ⟶ E) (hx : f ≫ x = x') (hy : f ≫ y = y')
    (e : Picard.PoincareBundle.Line.Fibers.fiber L x ≅ Picard.PoincareBundle.Line.Fibers.fiber L y) (e' : Picard.PoincareBundle.Line.Fibers.fiber L x' ≅ Picard.PoincareBundle.Line.Fibers.fiber L y')
    (he : (Scheme.Modules.pullback f.left).mapIso e ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f y y' hy =
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f x x' hx ≪≫ e')
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Picard.PoincareBundle.Line.Fibers.fiber L x) (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left ⟶ Picard.PoincareBundle.Line.Fibers.fiber L x')
    (hs : Picard.PoincareBundle.Line.Fibers.pullSection L f x x' hx s = s') :
    Picard.PoincareBundle.Line.Fibers.pullSection L f y y' hy (s ≫ e.hom) = s' ≫ e'.hom := by
  have h := congrArg Iso.hom he
  unfold Picard.PoincareBundle.Line.Fibers.pullSection
  rw [Picard.PoincareBundle.Bilinear.FrameProducts.pulledSection_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => Picard.PoincareBundle.Bilinear.ContractionPullback.pulledSection f.left s ≫ a) h).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ e'.hom) hs)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberSectionIsoTransport.Construction
