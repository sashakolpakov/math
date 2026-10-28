import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

/-! # Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change

noncomputable section

/-!
# IntegralComparison: changing an actual bounded crystalline frame maps its native relative resolution
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} [IsSeparated f] {n : ℕ}
  {F G : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : G ⟶ F)

def diagramMap : Diagram.productDiagram G ⟶ Diagram.productDiagram F where
  app U := (BoundedCrystalline.Site.inclusion f n).map (prod.map α (𝟙 U))
  naturality U V β := by
    change (BoundedCrystalline.Site.inclusion f n).map (prod.map (𝟙 G) β) ≫ (BoundedCrystalline.Site.inclusion f n).map (prod.map α (𝟙 V)) =
      (BoundedCrystalline.Site.inclusion f n).map (prod.map α (𝟙 U)) ≫ (BoundedCrystalline.Site.inclusion f n).map (prod.map (𝟙 F) β)
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (BoundedCrystalline.Site.inclusion f n).map
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, prod.map_fst_assoc, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, prod.map_snd, prod.map_snd_assoc, Category.id_comp, Category.comp_id]

theorem projection : diagramMap α ≫ Diagram.projection F = Diagram.projection G := by
  apply NatTrans.ext
  funext U
  change (diagramMap α).app U ≫ (Diagram.projection F).app U =
    (Diagram.projection G).app U
  rw [Diagram.projection_app, Diagram.projection_app]
  change (BoundedCrystalline.Site.inclusion f n).map (prod.map α (𝟙 U)) ≫ (BoundedCrystalline.Site.inclusion f n).map prod.snd =
    (BoundedCrystalline.Site.inclusion f n).map prod.snd
  rw [← Functor.map_comp, prod.map_snd, Category.comp_id]

theorem frameProjection : diagramMap α ≫ Symbols.frameProjection F =
    Symbols.frameProjection G ≫ (Functor.const _).map ((BoundedCrystalline.Site.inclusion f n).map α) := by
  apply NatTrans.ext
  funext U
  change (diagramMap α).app U ≫ (Symbols.frameProjection F).app U =
    (Symbols.frameProjection G).app U ≫ (BoundedCrystalline.Site.inclusion f n).map α
  rw [Symbols.frameProjection_app, Symbols.frameProjection_app]
  change (BoundedCrystalline.Site.inclusion f n).map (prod.map α (𝟙 U)) ≫ (BoundedCrystalline.Site.inclusion f n).map prod.fst =
    (BoundedCrystalline.Site.inclusion f n).map prod.fst ≫ (BoundedCrystalline.Site.inclusion f n).map α
  rw [← Functor.map_comp, prod.map_fst, Functor.map_comp]

def presheafMap : Diagram.complex F ⟶ Diagram.complex G :=
  Relative.DiagramComplexMap.map (Diagram.productDiagram G) (Diagram.productDiagram F) Diagram.baseDiagram
    (Diagram.projection G) (Diagram.projection F) (diagramMap α) (projection α)

theorem presheaf_augmentation : Diagram.augmentation F ≫ presheafMap α =
    Diagram.augmentation G :=
  Relative.DiagramComplexMap.augmentation (Diagram.productDiagram G) (Diagram.productDiagram F) Diagram.baseDiagram
    (Diagram.projection G) (Diagram.projection F) (diagramMap α) (projection α)

def sheafMap : Bounded.RelativeSheafComplex.complex f n F ⟶ Bounded.RelativeSheafComplex.complex f n G :=
  ((Bounded.RelativeSheafComplex.sheafification f n).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (presheafMap α)

theorem sheaf_augmentation : Bounded.RelativeSheafComplex.augmentation f n F ≫ sheafMap α =
    Bounded.RelativeSheafComplex.augmentation f n G := by
  let S := (Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have h := (S.map_comp (Diagram.augmentation F) (presheafMap α)).symm.trans
    (congrArg S.map (presheaf_augmentation α))
  exact (Category.assoc (Bounded.RelativeSheafComplex.sourceIso f n).inv
    (S.map (Diagram.augmentation F)) (S.map (presheafMap α))).trans
      (congrArg (fun t => (Bounded.RelativeSheafComplex.sourceIso f n).inv ≫ t) h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change
