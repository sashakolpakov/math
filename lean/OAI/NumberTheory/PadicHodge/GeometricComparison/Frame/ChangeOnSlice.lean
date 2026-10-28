import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor

/-! # Change On Slice -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSlice.FrameChangeOnSlice

noncomputable section

/-! A frame change that becomes an isomorphism after products with objects
over a fixed frame identifies the original relative complexes on that slice. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (I F G : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (α : G ⟶ F)
  (h : ∀ (T : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (_ : T ⟶ I), IsIso (prod.map α (𝟙 T)))

local notation "t" => Over.forget I
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.baseDiagram (p := p) (J := J) (δ := δ) (f := f) (n := n)
local notation "HF" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "HG" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram G
local notation "πF" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "πG" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection G

def diagramMap : t ⋙ HG ⟶ t ⋙ HF := Functor.whiskerLeft t (IntegralComparison.BoundedFrame.Change.diagramMap α)

include h in
theorem diagramMap_app_isIso (T : Over I) : IsIso ((diagramMap f n I F G α).app T) := by
  change IsIso ((IntegralComparison.BoundedCrystalline.Site.inclusion f n).map (prod.map α (𝟙 T.left)))
  let := h T.left T.hom
  infer_instance

include h in
theorem diagramMap_isIso : IsIso (diagramMap f n I F G α) := by
  let (T : Over I) : IsIso ((diagramMap f n I F G α).app T) := diagramMap_app_isIso f n I F G α h T
  exact NatIso.isIso_of_isIso_app _

theorem projection : diagramMap f n I F G α ≫ Functor.whiskerLeft t πF = Functor.whiskerLeft t πG := by
  rw [diagramMap, ← Functor.whiskerLeft_comp, IntegralComparison.BoundedFrame.Change.projection]

def diagramIso : t ⋙ HG ≅ t ⋙ HF := by
  let := diagramMap_isIso f n I F G α h
  exact asIso (diagramMap f n I F G α)

def complexIso :
    ((IntegralComparison.Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (.up ℕ)).obj
      (IntegralComparison.BoundedFrame.Diagram.complex F) ≅
    ((IntegralComparison.Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (.up ℕ)).obj
      (IntegralComparison.BoundedFrame.Diagram.complex G) :=
  IntegralComparison.Relative.ComplexRestriction.complexIso t HF Q πF ≪≫
    IntegralComparison.Relative.ResolutionFunctor.diagramIso (t ⋙ Q) (Functor.whiskerLeft t πG) (Functor.whiskerLeft t πF)
      (diagramIso f n I F G α h) (projection f n I F G α) ≪≫
        (IntegralComparison.Relative.ComplexRestriction.complexIso t HG Q πG).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSlice.FrameChangeOnSlice
