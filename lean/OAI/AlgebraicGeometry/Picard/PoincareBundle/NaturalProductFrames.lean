import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFrameProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFrameRatios

/-! # Natural Product Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalProductFrames

noncomputable section

/-! The multiplication coefficient of actual fiber frames commutes with all geometric pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineCocycle

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
  (L : Line.Bundles.LineBundle H.left) (D : MultiplicativeLineData.MultiplicativeData L)
  (F : ∀ {T : Over S} (x : T ⟶ H), AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L x)
  {T U : Over S} (g : U ⟶ T) (a b c : T ⟶ H) (hab : a * b = c)
  (a' b' c' : U ⟶ H) (hab' : a' * b' = c')
  (ha : g ≫ a = a') (hb : g ≫ b = b') (hc : g ≫ c = c')
  (hs : Line.Fibers.pullSection L g a a' ha (F a).hom = (F a').hom)
  (ht : Line.Fibers.pullSection L g b b' hb (F b).hom = (F b').hom)

attribute [local instance] MultiplicativeLineData.MultiplicativeData.product_isIso

include hs ht

/-- Pullback of the product frame is the product of the pulled frames. -/
theorem product_natural :
    Line.Fibers.pullSection L g c c' hc (Bilinear.ProductFrames.productFrame (D.product a b c hab) (F a) (F b)).hom =
      (Bilinear.ProductFrames.productFrame (D.product a' b' c' hab') (F a') (F b')).hom := by
  have h := FiberFrameProducts.product_pullback L g a b c a' b' c' ha hb hc
    (D.product a b c hab) (F a).hom (F b).hom
    (Bilinear.ProductFrames.productFrame (D.product a b c hab) (F a) (F b)).hom
    (fun V => (Bilinear.ProductFrames.productFrame_app (D.product a b c hab) (F a) (F b) V).symm)
  rw [D.product_natural g a b c hab a' b' c' hab' ha hb hc, hs, ht] at h
  apply Line.FrameUnits.unit_hom_ext
  intro V
  exact (h V).symm.trans (Bilinear.ProductFrames.productFrame_app (D.product a' b' c' hab') (F a') (F b') V).symm

/-- The coefficient is a natural regular unit, on arbitrary nonreduced test schemes. -/
theorem coefficient_natural
    (hu : Line.Fibers.pullSection L g c c' hc (F c).hom = (F c').hom) :
    MultiplicativeLineCocycle.value L D F a' b' c' hab' = Units.map g.left.appTop.hom (MultiplicativeLineCocycle.value L D F a b c hab) :=
  FiberFrameRatios.frameRatio_naturality L g c c' hc
    (Bilinear.ProductFrames.productFrame (D.product a b c hab) (F a) (F b)) (F c)
    (Bilinear.ProductFrames.productFrame (D.product a' b' c' hab') (F a') (F b')) (F c')
    (NaturalProductFrames.product_natural L D F g a b c hab a' b' c' hab' ha hb hc hs ht) hu

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalProductFrames
