import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheaves
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections

/-! # Frame Sheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheafSections

noncomputable section

/-!
# IntegralComparison: restriction between bounded levels preserves the actual constant-sheaf frame comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

private theorem compose_square {D : Type*} [Category D] {A B C E F G : D}
    (a : A ⟶ B) (e : B ⟶ C) (s : A ⟶ E) (b : E ⟶ C) (c : C ⟶ F) (d : E ⟶ G) (a' : G ⟶ F)
    (h₁ : a ≫ e = s ≫ b) (h₂ : b ≫ c = d ≫ a') : a ≫ e ≫ c = (s ≫ d) ≫ a' :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ c) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (fun t => s ≫ t) h₂).trans (Category.assoc _ _ _).symm)))

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f m
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def sourceIso : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (((constantSheaf (BoundedCrystalline.Site.topology f m) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedFrame.DeRhamSections.frameComplex f m ((G).obj F))) ≅
    (((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedFrame.DeRhamSections.frameComplex f n F)) :=
  (NatIso.mapHomologicalComplex (FrameSheaves.sheafificationIso f n m hnm) (ComplexShape.up ℕ)).app
    (RelativeFrame.ComplexMap.constantComplex ((G).obj F).obj) ≪≫
      ((SX).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso (FrameSectionRestriction.sourceIso f n m hnm F)

theorem component (i : ℕ) : (R).map ((BoundedFrame.DeRhamSections.sheafMap f m ((G).obj F)).f i) ≫
    (FrameSheaves.complexIso f n m hnm F).hom.f i =
      (sourceIso f n m hnm F).hom.f i ≫ (BoundedFrame.DeRhamSections.sheafMap f n F).f i := by
  have h₁ := (FrameSheaves.sheafificationIso f n m hnm).hom.naturality
    ((RelativeFrame.ComplexMap.map (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY
      (BoundedFrame.Diagram.projection ((G).obj F)) ((G).obj F).obj
        (BoundedFrame.Symbols.frameProjection ((G).obj F))).f i)
  have hraw := congrArg (SX).map (congrArg (fun φ => φ.f i) (FrameSectionRestriction.presheaf f n m hnm F))
  have h₂ := ((SX).map_comp _ _).symm.trans (hraw.trans ((SX).map_comp _ _))
  exact compose_square _ _ _ _ _ _ _ h₁ h₂

theorem complexes : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (BoundedFrame.DeRhamSections.sheafMap f m ((G).obj F)) ≫
      (FrameSheaves.complexIso f n m hnm F).hom =
    (sourceIso f n m hnm F).hom ≫ BoundedFrame.DeRhamSections.sheafMap f n F := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component f n m hnm F i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheafSections
