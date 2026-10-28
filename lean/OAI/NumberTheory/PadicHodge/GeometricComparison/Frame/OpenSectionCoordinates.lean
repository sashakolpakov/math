import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction

/-! # Open Section Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionCoordinates.FrameOpenSectionCoordinates

noncomputable section

/-! The natural frame open-section family retains the original
constant-sheaf Ext section maps and actual open restriction components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

theorem global_app_f (F : Cᵒᵖ) (i : ℕ) : ((OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation f n).app F).f i =
    (IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n)
      (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f n F.unop)
      (IntegralComparison.Bounded.RelativeSheafComplex.complex f n F.unop)
      (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f n F.unop)).f i := by
  have h := congrArg (fun a => a.f i) (ExtSectionNaturality.FrameExtSectionNaturality.transformation_app f n F)
  exact congrArg (fun a => a ≫ ((IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2} R
    (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n)).app
      ((IntegralComparison.Bounded.RelativeSheafComplex.complex f n F.unop).X i)).hom) h

theorem global_app (F : Cᵒᵖ) : (OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation f n).app F =
    IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n)
      (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f n F.unop)
      (IntegralComparison.Bounded.RelativeSheafComplex.complex f n F.unop)
      (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f n F.unop) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact global_app_f f n F i

theorem open_app_f (F : Cᵒᵖ) (V : Y.Opensᵒᵖ) (i : ℕ) :
    (((OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation f n).app F).f i).app V =
      ((OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation f n).app F).f i ≫
        ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation f n).app
          ((IntegralComparison.Bounded.RelativeSheafComplex.complex f n F.unop).X i)).app V := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionCoordinates.FrameOpenSectionCoordinates
