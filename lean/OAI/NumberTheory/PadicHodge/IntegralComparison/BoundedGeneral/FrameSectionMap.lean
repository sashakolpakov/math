import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FrameRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Postcompose
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.DiagramChange

/-! # Frame Section Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameSectionMap

noncomputable section

/-!
# IntegralComparison: geometric restriction preserves the actual presheaf frame section map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.GeneralFrameComparison

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
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
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
    (RelativeFrame.ComplexMap.map (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY
      (BoundedFrame.Diagram.projection ((G).obj F)) ((G).obj F).obj
        (BoundedFrame.Symbols.frameProjection ((G).obj F))) ≫
          FrameRestriction.presheafMap g hg n F =
    (sourceIso g hg n F).hom ≫ RelativeFrame.ComplexMap.map
      (BoundedFrame.Diagram.productDiagram F) QX (BoundedFrame.Diagram.projection F) F.obj
        (BoundedFrame.Symbols.frameProjection F) := by
  have h₁ := RelativeFrame.FrameRestriction.complexes G (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY
    (BoundedFrame.Diagram.projection ((G).obj F)) ((G).obj F).obj (BoundedFrame.Symbols.frameProjection ((G).obj F))
  have h₂ := RelativeFrame.DiagramChange.complexes (GeneralFrameComparison.sourceDiagram g hg n F) (GeneralFrameComparison.targetDiagram g hg n F)
    (G ⋙ QY) (GeneralFrameComparison.sourceProjection g hg n F) (GeneralFrameComparison.targetProjection g hg n F) (GeneralFrameComparison.comparison g hg n F)
    (GeneralFrameComparison.projection g hg n F) ((G).obj F).obj (GeneralFrameComparison.sourceFrameProjection g hg n F)
    (GeneralFrameComparison.targetFrameProjection g hg n F) (GeneralFrameComparison.frameProjection g hg n F)
  have h₃ := RelativeFrame.Postcompose.complexes g hg (BoundedFrame.Diagram.productDiagram F) QX
    (BoundedFrame.Diagram.projection F) F.obj (BoundedFrame.Symbols.frameProjection F)
  exact compose_three _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameSectionMap
