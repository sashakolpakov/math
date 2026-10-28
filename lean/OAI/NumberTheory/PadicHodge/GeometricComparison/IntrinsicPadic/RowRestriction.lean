import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRowRestriction

/-! # Row Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RowRestriction.IntrinsicPadicGeometricRowRestriction

noncomputable section

/-! Each native section row over compatible affine pairs retains the
original invertible restriction to an intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [Smooth X₁.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

def sourceRows := Section.ComplexBifunctor.SectionComplexBifunctor.functor (SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n)
  ((Affine.MapPairs.AffineMapPairs.source u.left).op ⋙ PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₁ Y₁ f₁ hp₁ n)

def targetRows := Section.ComplexBifunctor.SectionComplexBifunctor.functor (SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n)
  ((Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₂ Y₂ f₂ hp₂ n)

omit [Smooth X₂.hom] [IsSeparated Y₂.hom] in
theorem source_meet_isIso (I V : Affine.MapPairs.AffineMapPairs.Charts u.left) :
    IsIso (((sourceRows p u f₁ hp₁ n).obj (op I)).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) :=
  SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X₁ Y₁ f₁ hp₁ n I.val.1 V.val.1

omit [Smooth X₁.hom] [IsSeparated Y₁.hom] in
theorem target_meet_isIso (I V : Affine.MapPairs.AffineMapPairs.Charts u.left) :
    IsIso (((targetRows p u f₂ hp₂ n).obj (op I)).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) :=
  SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X₂ Y₂ f₂ hp₂ n I.val.2 V.val.2

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RowRestriction.IntrinsicPadicGeometricRowRestriction
