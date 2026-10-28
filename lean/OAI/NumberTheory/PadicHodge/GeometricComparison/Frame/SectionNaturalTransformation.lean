import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor

/-! # Section Natural Transformation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SectionNaturalTransformation.FrameSectionNaturalTransformation

noncomputable section

/-! The original frame de Rham section maps form a natural transformation
to the strict bounded relative-resolution diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n

def source : Cᵒᵖ ⥤ CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℕ :=
  Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded f n ⋙
    (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ Cᵒᵖ ⥤ ModuleCat.{u} B).mapHomologicalComplex (.up ℕ)

def transformation : source (p := p) (J := J) (δ := δ) f n ⟶
    BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor (p := p) (J := J) (δ := δ) f n where
  app F := IntegralComparison.RelativeFrame.ComplexMap.map (IntegralComparison.BoundedFrame.Diagram.productDiagram F.unop)
    (IntegralComparison.BoundedCrystalline.Site.inclusion f n) (IntegralComparison.BoundedFrame.Diagram.projection F.unop) F.unop.obj
    (IntegralComparison.BoundedFrame.Symbols.frameProjection F.unop)
  naturality F G α :=
    (IntegralComparison.RelativeFrame.ChangeNaturality.complexes
      (IntegralComparison.BoundedFrame.Diagram.productDiagram G.unop) (IntegralComparison.BoundedFrame.Diagram.productDiagram F.unop)
      (IntegralComparison.BoundedCrystalline.Site.inclusion f n) (IntegralComparison.BoundedFrame.Diagram.projection G.unop) (IntegralComparison.BoundedFrame.Diagram.projection F.unop)
      (IntegralComparison.BoundedFrame.Change.diagramMap α.unop) (IntegralComparison.BoundedFrame.Change.projection α.unop)
      F.unop.obj G.unop.obj ((IntegralComparison.BoundedCrystalline.Site.inclusion f n).map α.unop)
      (IntegralComparison.BoundedFrame.Symbols.frameProjection G.unop) (IntegralComparison.BoundedFrame.Symbols.frameProjection F.unop)
      (IntegralComparison.BoundedFrame.Change.frameProjection α.unop)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SectionNaturalTransformation.FrameSectionNaturalTransformation
