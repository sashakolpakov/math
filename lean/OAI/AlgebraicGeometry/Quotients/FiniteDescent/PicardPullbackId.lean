import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleDual
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorObj

/-! # Picard Pullback Id -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback

noncomputable section

/-! Pullback is a homomorphism on the Picard group of actual line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- Pullback along any scheme morphism commutes with the actual binary tensor sheaf. -/
def tensorIso (f : X ⟶ Y) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    ((L.tensor M).pullback f).sheaf ≅ ((L.pullback f).tensor (M.pullback f)).sheaf :=
  (SheafCohomology.Projective.PullbackTensorObj.Scheme.Modules.nonempty_pullback_tensorObj f L.sheaf M.sheaf).some

theorem map_mul (f : X ⟶ Y) (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (q * r) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f r := by
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M => exact Quotient.sound ⟨tensorIso f L M⟩

/-- The contravariant Picard-group map is induced by ordinary sheaf pullback. -/
def map (f : X ⟶ Y) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X where
  toFun := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f
  map_one' := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial f
  map_mul' := map_mul f

theorem map_id : map (𝟙 X) = MonoidHom.id _ := by
  ext q
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map f).comp (map g) := by
  ext q
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp f g q

/-- Pulling back a dual has the same class as dualizing the pullback. -/
theorem dual (f : X ⟶ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    Nonempty (((DualLine.Construction.DualLineBundle.dual L).pullback f).sheaf ≅
      (DualLine.Construction.DualLineBundle.dual (L.pullback f)).sheaf) := by
  have h := (map f).map_inv (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  exact Quotient.exact h

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback
