import OAI.AlgebraicGeometry.Picard.PoincareBundle.RescaledFiberFrameNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineCocycle

/-! # Multiplicative Frame Correction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCorrection

noncomputable section

/-! A regular cocycle solution corrects normalized fiber frames into multiplicative ones. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData OAI.AlgebraicGeometry.Picard.PoincareBundle.RescaledLineFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
  (L : Line.Bundles.LineBundle H.left) (D : MultiplicativeLineData.MultiplicativeData L)
  (F : ∀ {T : Over S} (a : T ⟶ H), AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a)
  (u : ∀ (T : Over S), (T ⟶ H) → Γ(T.left, ⊤)ˣ)

attribute [local instance] MultiplicativeLineData.MultiplicativeData.product_isIso

/-- Correct each frame by the inverse of the regular solution value. -/
def frame {T : Over S} (a : T ⟶ H) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a :=
  RescaledLineFrames.rescale (F a) (u T a)⁻¹

theorem frame_one (T : Over S) (hF : F (1 : T ⟶ H) = D.unitFrame) (hu : u T 1 = 1) :
    frame L F u (1 : T ⟶ H) = D.unitFrame := by
  change RescaledLineFrames.rescale (F (1 : T ⟶ H)) (u T 1)⁻¹ = _
  rw [hu, inv_one, RescaledLineFrames.rescale_one, hF]

omit [GrpObj H] in
theorem frame_natural {T U : Over S} (g : U ⟶ T) (a : T ⟶ H) (a' : U ⟶ H) (ha : g ≫ a = a')
    (hF : Line.Fibers.pullSection L g a a' ha (F a).hom = (F a').hom)
    (hu : Units.map g.left.appTop.hom (u T a) = u U a') :
    Line.Fibers.pullSection L g a a' ha (frame L F u a).hom = (frame L F u a').hom := by
  let φ : Γ(T.left, ⊤)ˣ →* Γ(U.left, ⊤)ˣ := Units.map g.left.appTop.hom
  have hi : φ (u T a)⁻¹ = (u U a')⁻¹ :=
    (φ.map_inv (u T a)).trans (congrArg (fun v : Γ(U.left, ⊤)ˣ => v⁻¹) hu)
  exact RescaledFiberFrameNaturality.rescale_natural L g a a' ha
    (F a) (F a') (u T a)⁻¹ (u U a')⁻¹ hF hi

/-- The corrected frames multiply as sections of the original line sheaves on every open set. -/
theorem frame_product {T : Over S} (a b c : T ⟶ H) (hab : a * b = c)
    (hu : MultiplicativeLineCocycle.value L D F a b c hab * u T c = u T a * u T b)
    (V : T.left.Opens) :
    (D.product a b c hab).app V ((frame L F u a).hom.app V (1 : Γ(T.left, V)))
      ((frame L F u b).hom.app V (1 : Γ(T.left, V))) =
        (frame L F u c).hom.app V (1 : Γ(T.left, V)) := by
  have h := RescaledLineFrames.product_rescale_inverse (D.product a b c hab) (F a) (F b) (F c)
    (u T a) (u T b) (u T c) hu
  have hs := congrArg (fun e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L c =>
    e.hom.app V (1 : Γ(T.left, V))) h
  exact (Bilinear.ProductFrames.productFrame_app (D.product a b c hab) (frame L F u a) (frame L F u b) V).symm.trans hs

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCorrection
