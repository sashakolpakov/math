import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechRefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.IsoMiddleCancellation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechReferenceRefinement

/-! # Diagonal Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement

noncomputable section

/-! The canonical paired diagonal-to-Cech comparisons are exactly the
original chosen-cover comparisons followed by their actual refinements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "Pairs" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.Charts (Over.Hom.left u)
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₂ Y₂ f₂ hp₂ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₁ Y₁ f₁ hp₁ n
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n
local notation "S'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n

local instance sourceCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
      (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R
    (IntegralComparison.BoundedCrystalline.Site.topology (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n)

local instance targetCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
      (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R
    (IntegralComparison.BoundedCrystalline.Site.topology (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n)

def sourcePullback : (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤ (Pairsᵒᵖ ⥤ ModuleCat.{2} R) :=
  (Functor.whiskeringLeft _ _ _).obj (Affine.MapPairs.AffineMapPairs.source u.left).op
def targetPullback : (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤ (Pairsᵒᵖ ⥤ ModuleCat.{2} R) :=
  (Functor.whiskeringLeft _ _ _).obj (Affine.MapPairs.AffineMapPairs.target u.left).op

instance sourcePullback_additive : (sourcePullback p u).Additive := by
  dsimp only [sourcePullback]
  infer_instance
instance targetPullback_additive : (targetPullback p u).Additive := by
  dsimp only [targetPullback]
  infer_instance

def sourceMap : Section.DiagonalCone.SectionDiagonalCone.source Pairs S' ((Affine.MapPairs.AffineMapPairs.source u.left).op ⋙ Q) ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X₁ Y₁ f₁ hp₁ n) :=
  ((sourcePullback p u).mapHomologicalComplex (.up ℕ)).map
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X₁ Y₁ f₁ hp₁ n)

def targetMap : Section.DiagonalCone.SectionDiagonalCone.source Pairs S ((Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ P) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X₂ Y₂ f₂ hp₂ n) :=
  ((targetPullback p u).mapHomologicalComplex (.up ℕ)).map
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X₂ Y₂ f₂ hp₂ n)

omit [IsSeparated Y₂.hom] in
theorem source_component (q : ℕ) (I : Pairsᵒᵖ) :
    ((sourceMap p u f₁ hp₁ n).f q).app I ≫
      ((((S').mapHomologicalComplex (.up ℕ)).map
        (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.sourceMap p u f₁ hp₁ n)).f q).app I =
    ((DiagonalCech.IntrinsicPadicGeometricDiagonalCech.sourceComparison p u f₁ hp₁ n U).f q).app I :=
  Section.DiagonalCechReferenceRefinement.SectionDiagonalCechReferenceRefinement.component Pairs X₁.left.affineOpens R
    (Affine.MapPairs.AffineMapPairs.source u.left) (SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X₁ Y₁ f₁ n) Q
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X₁ Y₁ f₁ hp₁ n)
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.source_meet_isIso p u f₁ hp₁ n)
    U (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁) (Cover.IntrinsicPadicGeometricCoverRefinements.source p u)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X₁ Y₁ f₁ hp₁ n) q I

omit [IsSeparated Y₂.hom] in
theorem source_comparison : sourceMap p u f₁ hp₁ n ≫
    ((S').mapHomologicalComplex (.up ℕ)).map (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.sourceMap p u f₁ hp₁ n) =
      DiagonalCech.IntrinsicPadicGeometricDiagonalCech.sourceComparison p u f₁ hp₁ n U := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext I
  exact source_component p u f₁ hp₁ n q I

omit [IsSeparated Y₁.hom] in
theorem target_component (q : ℕ) (I : Pairsᵒᵖ) :
    ((targetMap p u f₂ hp₂ n).f q).app I ≫
      ((((S).mapHomologicalComplex (.up ℕ)).map
        (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.targetRefinement p u f₂ hp₂ n)).f q).app I =
    ((DiagonalCech.IntrinsicPadicGeometricDiagonalCech.targetComparison p u f₂ hp₂ n U).f q).app I :=
  Section.DiagonalCechReferenceRefinement.SectionDiagonalCechReferenceRefinement.component Pairs X₂.left.affineOpens R
    (Affine.MapPairs.AffineMapPairs.target u.left) (SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X₂ Y₂ f₂ n) P
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X₂ Y₂ f₂ hp₂ n)
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.target_meet_isIso p u f₂ hp₂ n)
    U (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂) (Cover.IntrinsicPadicGeometricCoverRefinements.target p u)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X₂ Y₂ f₂ hp₂ n) q I

omit [IsSeparated Y₁.hom] in
theorem target_comparison : targetMap p u f₂ hp₂ n ≫
    ((S).mapHomologicalComplex (.up ℕ)).map (RefinedResolution.IntrinsicPadicGeometricRefinedResolution.targetRefinement p u f₂ hp₂ n) =
      DiagonalCech.IntrinsicPadicGeometricDiagonalCech.targetComparison p u f₂ hp₂ n U := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext I
  exact target_component p u f₂ hp₂ n q I

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement
