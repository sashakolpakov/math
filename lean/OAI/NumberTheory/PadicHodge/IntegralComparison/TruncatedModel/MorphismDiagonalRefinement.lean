import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinedResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechRefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.IsoMiddleCancellation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechReferenceRefinement

/-! # Morphism Diagonal Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinement

noncomputable section

/-! The canonical paired diagonal-to-Cech comparisons are exactly the
original chosen-cover comparisons followed by their actual refinements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Pairs" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts (Over.Hom.left u)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₂ Y₂ f₂ hp₂
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₁ Y₁ f₁ hp₁
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.targetSections p k n u f₂
local notation "S'" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.sourceSections p k n u f₁

local instance sourceCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p)
      (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y₁) n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R
    (BoundedCrystalline.Site.topology (Witt.Crystalline.wittStructureMap p k Y₁) n)

local instance targetCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p)
      (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y₂) n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R
    (BoundedCrystalline.Site.topology (Witt.Crystalline.wittStructureMap p k Y₂) n)

def sourcePullback : (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤ (Pairsᵒᵖ ⥤ ModuleCat.{2} R) :=
  (Functor.whiskeringLeft _ _ _).obj (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op
def targetPullback : (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤ (Pairsᵒᵖ ⥤ ModuleCat.{2} R) :=
  (Functor.whiskeringLeft _ _ _).obj (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op

instance sourcePullback_additive : (sourcePullback p k n u).Additive := by
  dsimp only [sourcePullback]
  infer_instance
instance targetPullback_additive : (targetPullback p k n u).Additive := by
  dsimp only [targetPullback]
  infer_instance

def sourceMap : GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source Pairs S' ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙ Q) ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj (CechSheafResolution.complex p k n X₁ Y₁ f₁ hp₁) :=
  ((sourcePullback p k n u).mapHomologicalComplex (.up ℕ)).map
    (DiagonalCech.Comparison.totalMap p k n X₁ Y₁ f₁ hp₁)

def targetMap : GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source Pairs S ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙ P) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj (CechSheafResolution.complex p k n X₂ Y₂ f₂ hp₂) :=
  ((targetPullback p k n u).mapHomologicalComplex (.up ℕ)).map
    (DiagonalCech.Comparison.totalMap p k n X₂ Y₂ f₂ hp₂)

omit [IsSeparated Y₂.hom] in
theorem source_component (q : ℕ) (I : Pairsᵒᵖ) :
    ((sourceMap p k n u f₁ hp₁).f q).app I ≫
      ((((S').mapHomologicalComplex (.up ℕ)).map
        (MorphismRefinedResolution.sourceMap p k n u f₁ hp₁)).f q).app I =
    ((MorphismDiagonalCech.sourceComparison p k n u f₁ hp₁ U).f q).app I :=
  GeometricComparison.Section.DiagonalCechReferenceRefinement.SectionDiagonalCechReferenceRefinement.component.{2, 1} Pairs X₁.left.affineOpens R
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left) (SectionBifunctor.sections p k n X₁ Y₁ f₁) Q
    (SectionRowRestriction.meet_isIso p k n X₁ Y₁ f₁ hp₁)
    (MorphismRowRestriction.source_meet_isIso p k n u f₁ hp₁)
    U (CechSliceResolution.opens p k n X₁) (MorphismRefinement.source p k n u)
    (DiagonalCech.Comparison.totalIso p k n X₁ Y₁ f₁ hp₁) q I

omit [IsSeparated Y₂.hom] in
theorem source_comparison : sourceMap p k n u f₁ hp₁ ≫
    ((S').mapHomologicalComplex (.up ℕ)).map (MorphismRefinedResolution.sourceMap p k n u f₁ hp₁) =
      MorphismDiagonalCech.sourceComparison p k n u f₁ hp₁ U := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext I
  exact source_component p k n u f₁ hp₁ q I

omit [IsSeparated Y₁.hom] in
theorem target_component (q : ℕ) (I : Pairsᵒᵖ) :
    ((targetMap p k n u f₂ hp₂).f q).app I ≫
      ((((S).mapHomologicalComplex (.up ℕ)).map
        (MorphismRefinedResolution.targetRefinement p k n u f₂ hp₂)).f q).app I =
    ((MorphismDiagonalCech.targetComparison p k n u f₂ hp₂ U).f q).app I :=
  GeometricComparison.Section.DiagonalCechReferenceRefinement.SectionDiagonalCechReferenceRefinement.component.{2, 1} Pairs X₂.left.affineOpens R
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left) (SectionBifunctor.sections p k n X₂ Y₂ f₂) P
    (SectionRowRestriction.meet_isIso p k n X₂ Y₂ f₂ hp₂)
    (MorphismRowRestriction.target_meet_isIso p k n u f₂ hp₂)
    U (CechSliceResolution.opens p k n X₂) (MorphismRefinement.target p k n u)
    (DiagonalCech.Comparison.totalIso p k n X₂ Y₂ f₂ hp₂) q I

omit [IsSeparated Y₁.hom] in
theorem target_comparison : targetMap p k n u f₂ hp₂ ≫
    ((S).mapHomologicalComplex (.up ℕ)).map (MorphismRefinedResolution.targetRefinement p k n u f₂ hp₂) =
      MorphismDiagonalCech.targetComparison p k n u f₂ hp₂ U := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext I
  exact target_component p k n u f₂ hp₂ q I

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinement
