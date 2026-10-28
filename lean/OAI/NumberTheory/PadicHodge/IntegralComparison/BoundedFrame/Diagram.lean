import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Products
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex

/-! # Diagram -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram

noncomputable section

/-!
# IntegralComparison: the native product diagram for a frame at a bounded Witt level

The second projection supplies the relative coefficient ring. Both
the product and its projection are the native categorical constructions
used by the slice direct-image functor.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} [IsSeparated f]
  {n : ℕ} (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

abbrev baseDiagram := BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n

def productDiagram : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ BigCrystallineSite.Object p B J δ f :=
  (Over.star F ⋙ Over.forget F) ⋙ baseDiagram

def projection : productDiagram F ⟶ baseDiagram :=
  Functor.whiskerRight (Over.forgetAdjStar F).counit baseDiagram ≫ (Functor.leftUnitor baseDiagram).hom

theorem projection_app (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) :
    (projection F).app U = (BoundedCrystalline.Site.inclusion f n).map (prod.snd : F ⨯ U ⟶ U) := by
  change (BoundedCrystalline.Site.inclusion f n).map ((Over.forgetAdjStar F).counit.app U) ≫ 𝟙 _ = _
  rw [Category.comp_id, Over.forgetAdjStar_counit_app]
  rfl

def complex : CochainComplex ((BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤ ModuleCat.{u} B) ℕ :=
  RelativeCrystalline.ModuleComplex.complex (productDiagram F) baseDiagram (projection F)

def augmentation : (CochainComplex.single₀ _).obj
    ((BoundedCrystalline.Site.inclusion f n).op ⋙ BigCrystallineCohomology.modulePresheaf f) ⟶ complex F :=
  RelativeCrystalline.ModuleComplex.augmentation (productDiagram F) baseDiagram (projection F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram
