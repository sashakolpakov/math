import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts

/-! # Line Section -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineSection

noncomputable section

/-!
# Normalized sections of actual original fibers transfer naturally to pulled-back line fibers
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

variable {S : Scheme.{u}} {K E : Over S} (p : K ⟶ E) (L : Line.Bundles.LineBundle E.left)

/-- Transfer an actual normalized section through the canonical comparison of line fibers. -/
def transportSection {T : Over S} (x : T ⟶ K) (a : T ⟶ E) (hx : x ≫ p = a)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Line.Fibers.fiber L a) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Line.Fibers.fiber (L.pullback p.left) x :=
  s ≫ (LineBilinear.fiberComparison p L x a hx).inv

/-- Transfer of a normalized section commutes with genuine geometric change of test scheme. -/
theorem transportSection_pullback {T T' : Over S} (g : T' ⟶ T)
    (x : T ⟶ K) (a : T ⟶ E) (hx : x ≫ p = a)
    (x' : T' ⟶ K) (a' : T' ⟶ E) (hx' : x' ≫ p = a')
    (hgx : g ≫ x = x') (hga : g ≫ a = a') (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Line.Fibers.fiber L a) :
    Line.Fibers.pullSection (L.pullback p.left) g x x' hgx (transportSection p L x a hx s) =
      transportSection p L x' a' hx' (Line.Fibers.pullSection L g a a' hga s) := by
  have hs := congrArg Iso.hom (LineBilinear.comparison_inverse_square p L g x a hx x' a' hx' hgx hga)
  unfold transportSection Line.Fibers.pullSection
  rw [Bilinear.FrameProducts.pulledSection_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => Bilinear.ContractionPullback.pulledSection g.left s ≫ f) hs).trans (Category.assoc _ _ _).symm)

/-- An actual original fiber frame supplies a frame of the pulled-back line fiber. -/
def transportFrame {T : Over S} (x : T ⟶ K) (a : T ⟶ E) (hx : x ≫ p = a)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber (L.pullback p.left) x :=
  s ≪≫ (LineBilinear.fiberComparison p L x a hx).symm

/-- Naturality of an original normalized frame proves naturality of its transferred frame. -/
theorem transportFrame_natural {T T' : Over S} (g : T' ⟶ T)
    (x : T ⟶ K) (a : T ⟶ E) (hx : x ≫ p = a)
    (x' : T' ⟶ K) (a' : T' ⟶ E) (hx' : x' ≫ p = a')
    (hgx : g ≫ x = x') (hga : g ≫ a = a')
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a) (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left ≅ Line.Fibers.fiber L a')
    (hs : Line.Fibers.pullSection L g a a' hga s.hom = s'.hom) :
    Line.Fibers.pullSection (L.pullback p.left) g x x' hgx (transportFrame p L x a hx s).hom =
      (transportFrame p L x' a' hx' s').hom := by
  have he := transportSection_pullback p L g x a hx x' a' hx' hgx hga s.hom
  rw [hs] at he
  exact he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineSection
