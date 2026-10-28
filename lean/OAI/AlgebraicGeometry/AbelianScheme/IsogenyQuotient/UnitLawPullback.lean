import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Unit Law Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnitLawPullback.Construction

noncomputable section

/-! The actual contracted left-unit identity survives every geometric
pullback and its canonical line-fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

universe u

theorem contractedUnit_pullback {S : Scheme.{u}} {E T U : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (r : U ⟶ T)
    (a x : T ⟶ E) (a' x' : U ⟶ E) (ha : r ≫ a = a') (hx : r ≫ x = x')
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L x))
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Picard.PoincareBundle.Line.Fibers.fiber L a) (hb : Picard.PoincareBundle.Bilinear.Contraction.contractLeft b s = 𝟙 (Picard.PoincareBundle.Line.Fibers.fiber L x)) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (Picard.PoincareBundle.Line.Fibers.pullBilinear L r a x x a' x' x' ha hx hx b) (Picard.PoincareBundle.Line.Fibers.pullSection L r a a' ha s) =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber L x') := by
  have hp := Picard.PoincareBundle.Bilinear.Transport.contractLeft_pullback_transport r.left
    (Picard.PoincareBundle.Line.Fibers.fiber_isLine L a) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) b (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r a a' ha)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r x x' hx) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r x x' hx) s
  change Picard.PoincareBundle.Bilinear.Contraction.contractLeft (Picard.PoincareBundle.Line.Fibers.pullBilinear L r a x x a' x' x' ha hx hx b) (Picard.PoincareBundle.Line.Fibers.pullSection L r a a' ha s) = _ at hp
  rw [hb, (Scheme.Modules.pullback r.left).map_id, Category.id_comp, Iso.inv_hom_id] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnitLawPullback.Construction
