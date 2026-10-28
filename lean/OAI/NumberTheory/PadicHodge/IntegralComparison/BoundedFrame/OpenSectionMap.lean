import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FrameRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Postcompose
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.DiagramChange

/-! # Open Section Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenSectionMap

noncomputable section

/-!
# IntegralComparison: geometric restriction preserves the actual presheaf frame section map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Postcompose.Comparison

universe u

private theorem compose_three {D : Type*} [Category D] {A B C E F G H : D}
    (a : A ⟶ B) (i₁ : B ⟶ C) (i₂ : C ⟶ E) (i₃ : E ⟶ F)
    (s₁ : A ⟶ G) (b : G ⟶ C) (c : G ⟶ E) (s₂ : G ⟶ H) (d : H ⟶ F)
    (h₁ : a ≫ i₁ = s₁ ≫ b) (h₂ : b ≫ i₂ = c) (h₃ : c ≫ i₃ = s₂ ≫ d) :
    a ≫ (i₁ ≫ i₂) ≫ i₃ = (s₁ ≫ s₂) ≫ d := by
  calc
    a ≫ (i₁ ≫ i₂) ≫ i₃ = ((a ≫ i₁) ≫ i₂) ≫ i₃ := by simp only [Category.assoc]
    _ = ((s₁ ≫ b) ≫ i₂) ≫ i₃ := congrArg (fun t => (t ≫ i₂) ≫ i₃) h₁
    _ = s₁ ≫ (b ≫ i₂) ≫ i₃ := by simp only [Category.assoc]
    _ = s₁ ≫ c ≫ i₃ := congrArg (fun t => s₁ ≫ t ≫ i₃) h₂
    _ = s₁ ≫ s₂ ≫ d := congrArg (fun t => s₁ ≫ t) h₃
    _ = (s₁ ≫ s₂) ≫ d := (Category.assoc _ _ _).symm

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction.restriction (B := B) G

def sourceIso : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (RelativeFrame.ComplexMap.constantComplex ((G).obj F).obj) ≅
      RelativeFrame.ComplexMap.constantComplex (C := BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) F.obj :=
  RelativeFrame.FrameRestriction.sourceIso G ((G).obj F).obj ≪≫
    RelativeFrame.Postcompose.sourceIso (C := BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) g hg F.obj

theorem presheaf : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (RelativeFrame.ComplexMap.map (Diagram.productDiagram ((G).obj F)) QY
      (Diagram.projection ((G).obj F)) ((G).obj F).obj
        (Symbols.frameProjection ((G).obj F))) ≫
          (OpenRestriction.presheafIso g hg n F).hom =
    (sourceIso g hg n F).hom ≫ RelativeFrame.ComplexMap.map
      (Diagram.productDiagram F) QX (Diagram.projection F) F.obj
        (Symbols.frameProjection F) := by
  have h₁ := RelativeFrame.FrameRestriction.complexes G (Diagram.productDiagram ((G).obj F)) QY
    (Diagram.projection ((G).obj F)) ((G).obj F).obj (Symbols.frameProjection ((G).obj F))
  have h₂ := RelativeFrame.DiagramChange.complexes (Postcompose.Comparison.sourceDiagram g hg n F) (Postcompose.Comparison.targetDiagram g hg n F)
    (G ⋙ QY) (Postcompose.Comparison.sourceProjection g hg n F) (Postcompose.Comparison.targetProjection g hg n F) (Postcompose.Comparison.comparison g hg n F)
    (Postcompose.Comparison.projection g hg n F) ((G).obj F).obj (Postcompose.Comparison.sourceFrameProjection g hg n F)
    (Postcompose.Comparison.targetFrameProjection g hg n F) (Postcompose.Comparison.frameProjection g hg n F)
  have h₃ := RelativeFrame.Postcompose.complexes g hg (Diagram.productDiagram F) QX
    (Diagram.projection F) F.obj (Symbols.frameProjection F)
  exact compose_three _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenSectionMap
