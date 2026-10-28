import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionRowRestriction

/-! # Morphism Row Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRowRestriction

noncomputable section

/-! Each native section row over compatible affine pairs retains the
original invertible restriction to an intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [Smooth X₁.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

def sourceRows := GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor (MorphismSectionMap.sourceSections p k n u f₁)
  ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙ ResolutionDiagram.diagram p k n X₁ Y₁ f₁ hp₁)

def targetRows := GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor (MorphismSectionMap.targetSections p k n u f₂)
  ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙ ResolutionDiagram.diagram p k n X₂ Y₂ f₂ hp₂)

omit [Smooth X₂.hom] [IsSeparated Y₂.hom] in
theorem source_meet_isIso (I V : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    IsIso (((sourceRows p k n u f₁ hp₁).obj (op I)).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) :=
  SectionRowRestriction.meet_isIso p k n X₁ Y₁ f₁ hp₁ I.val.1 V.val.1

omit [Smooth X₁.hom] [IsSeparated Y₁.hom] in
theorem target_meet_isIso (I V : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    IsIso (((targetRows p k n u f₂ hp₂).obj (op I)).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) :=
  SectionRowRestriction.meet_isIso p k n X₂ Y₂ f₂ hp₂ I.val.2 V.val.2

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRowRestriction
