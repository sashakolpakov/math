import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SectionNaturalTransformation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange

/-! # Sheaf Section Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SheafSectionNaturality.FrameSheafSectionNaturality

noncomputable section

/-! The original bounded frame sheaf and Ext-section maps are natural
for actual frame morphisms, before any choice of affine coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

def source : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded f n ⋙
    (IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B)).mapHomologicalComplex (.up ℕ)

def sheafTransformation : source (p := p) (J := J) (δ := δ) f n ⋙
    (constantSheaf (IntegralComparison.BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} R)).mapHomologicalComplex (.up ℕ) ⟶
      BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n :=
  Functor.whiskerRight (SectionNaturalTransformation.FrameSectionNaturalTransformation.transformation f n)
    ((IntegralComparison.Bounded.RelativeSheafComplex.sheafification f n).mapHomologicalComplex (.up ℕ))

abbrev extSections := IntegralComparison.Ext.ModuleFunctor.functor.{u + 2, u + 1, u + 2, u + 1} R
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n) 0

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SheafSectionNaturality.FrameSheafSectionNaturality
