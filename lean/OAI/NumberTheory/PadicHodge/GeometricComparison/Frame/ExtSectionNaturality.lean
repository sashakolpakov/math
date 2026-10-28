import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SheafSectionNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantExt

/-! # Ext Section Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ExtSectionNaturality.FrameExtSectionNaturality

noncomputable section

/-! A componentwise naturality interface for the original frame Ext-section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SheafSectionNaturality.FrameSheafSectionNaturality.source (p := p) (J := J) (δ := δ) f n
local notation "E" => OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SheafSectionNaturality.FrameSheafSectionNaturality.extSections (p := p) (J := J) (δ := δ) f n

def transformation : D ⋙
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ) ⟶
      BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n ⋙ (E).mapHomologicalComplex (.up ℕ) :=
  ConstantExt.ConstantExtSectionTransformation.transformation.{u + 1, u, u + 1, u + 2, u + 1, u}
    R (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n) D
    (BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n)
    (SheafSectionNaturality.FrameSheafSectionNaturality.sheafTransformation f n)

theorem transformation_app (F : Cᵒᵖ) : (transformation f n).app F =
    IntegralComparison.BoundedFrame.DeRhamSections.sectionsMap f n F.unop := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ExtSectionNaturality.FrameExtSectionNaturality
