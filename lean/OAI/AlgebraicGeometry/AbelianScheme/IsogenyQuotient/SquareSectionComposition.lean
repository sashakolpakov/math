import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSquareComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions

/-! # Square Section Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SquareSectionComposition.Construction

noncomputable section

/-! Transport of an actual section through successive commuting
squares agrees with transport through their composite. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions

universe u

def pullbackSquareSection {X Y X' Y' : Scheme.{u}}
    (q : X ⟶ Y) (q' : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (h : j ≫ q = q' ≫ i) {M : Y.Modules}
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback q).obj M) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X' ⟶ (Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback i).obj M) :=
  AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j z ≫ (PullbackSectionSquares.Construction.sectionPullbackSquareIso q q' j i h M).hom

theorem pullbackSquareSection_comp
    {X Y X₁ Y₁ X₂ Y₂ : Scheme.{u}}
    (q : X ⟶ Y) (q₁ : X₁ ⟶ Y₁) (q₂ : X₂ ⟶ Y₂)
    (j₁ : X₁ ⟶ X) (i₁ : Y₁ ⟶ Y) (j₂ : X₂ ⟶ X₁) (i₂ : Y₂ ⟶ Y₁)
    (h₁ : j₁ ≫ q = q₁ ≫ i₁) (h₂ : j₂ ≫ q₁ = q₂ ≫ i₂)
    (hc : (j₂ ≫ j₁) ≫ q = q₂ ≫ (i₂ ≫ i₁)) {M : Y.Modules}
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback q).obj M) :
    pullbackSquareSection q₁ q₂ j₂ i₂ h₂ (pullbackSquareSection q q₁ j₁ i₁ h₁ z) ≫
        (Scheme.Modules.pullback q₂).map ((Scheme.Modules.pullbackComp i₂ i₁).hom.app M) =
      pullbackSquareSection q q₂ (j₂ ≫ j₁) (i₂ ≫ i₁) hc z := by
  have h := congrArg Iso.hom (PullbackSquareComposition.Construction.sectionPullbackSquareIso_comp q q₁ q₂ j₁ i₁ j₂ i₂ h₁ h₂ hc M)
  change (Scheme.Modules.pullback j₂).map (PullbackSectionSquares.Construction.sectionPullbackSquareIso q q₁ j₁ i₁ h₁ M).hom ≫
      (PullbackSectionSquares.Construction.sectionPullbackSquareIso q₁ q₂ j₂ i₂ h₂ ((Scheme.Modules.pullback i₁).obj M)).hom ≫
      (Scheme.Modules.pullback q₂).map ((Scheme.Modules.pullbackComp i₂ i₁).hom.app M) =
    (Scheme.Modules.pullbackComp j₂ j₁).hom.app ((Scheme.Modules.pullback q).obj M) ≫
      (PullbackSectionSquares.Construction.sectionPullbackSquareIso q q₂ (j₂ ≫ j₁) (i₂ ≫ i₁) hc M).hom at h
  simp only [pullbackSquareSection, AbelianModuli.HilbertConstruction.Power.SectionTransitions.pullbackSection_postcomp, Category.assoc]
  rw [h, ← Category.assoc, PullbackSectionSquares.Construction.pullbackSection_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SquareSectionComposition.Construction
