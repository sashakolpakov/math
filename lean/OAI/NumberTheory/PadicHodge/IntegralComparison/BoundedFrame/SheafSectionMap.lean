import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenSectionMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections

/-! # Sheaf Section Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafSectionMap

noncomputable section

/-!
# IntegralComparison: geometric restriction preserves the actual constant-sheaf frame comparison
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

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) fY n
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def sourceIso : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (((constantSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (DeRhamSections.frameComplex fY n ((G).obj F))) ≅
    (((constantSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (DeRhamSections.frameComplex f n F)) :=
  (NatIso.mapHomologicalComplex (SheafRestriction.sheafificationIso g hg n) (ComplexShape.up ℕ)).app
    (RelativeFrame.ComplexMap.constantComplex ((G).obj F).obj) ≪≫
      ((SX).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso (OpenSectionMap.sourceIso g hg n F)

theorem component (i : ℕ) : (R).map ((DeRhamSections.sheafMap fY n ((G).obj F)).f i) ≫
    (SheafRestriction.complexIso g hg n F).hom.f i =
      (sourceIso g hg n F).hom.f i ≫ (DeRhamSections.sheafMap f n F).f i := by
  have h₁ := (SheafRestriction.sheafificationIso g hg n).hom.naturality
    ((RelativeFrame.ComplexMap.map (Diagram.productDiagram ((G).obj F)) QY
      (Diagram.projection ((G).obj F)) ((G).obj F).obj
        (Symbols.frameProjection ((G).obj F))).f i)
  have hraw := congrArg (SX).map (congrArg (fun φ => φ.f i) (OpenSectionMap.presheaf g hg n F))
  have h₂ := ((SX).map_comp _ _).symm.trans (hraw.trans ((SX).map_comp _ _))
  exact compose_square _ _ _ _ _ _ _ h₁ h₂

theorem complexes : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (DeRhamSections.sheafMap fY n ((G).obj F)) ≫
      (SheafRestriction.complexIso g hg n F).hom =
    (sourceIso g hg n F).hom ≫ DeRhamSections.sheafMap f n F := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component g hg n F i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafSectionMap
