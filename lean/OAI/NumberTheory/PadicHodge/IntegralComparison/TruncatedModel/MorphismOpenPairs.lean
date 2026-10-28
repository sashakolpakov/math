import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction

/-! # Morphism Open Pairs -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOpenPairs

noncomputable section

/-! Compatible integral affine pairs give compatible special-fiber
opens and their original inverse-image restriction transformation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

def source : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left ⥤ Y₁.left.Opens :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left ⋙ SectionBifunctor.specialOpens p k n X₁ Y₁ f₁

def target : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left ⥤ Y₂.left.Opens :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left ⋙ SectionBifunctor.specialOpens p k n X₂ Y₂ f₂

def preimage : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left ⥤ Y₁.left.Opens :=
  target p k n u f₂ ⋙ TopologicalSpace.Opens.map v.left.base

def restriction : (preimage p k n u v f₂).op ⟶ (source p k n u f₁).op where
  app U := (homOfLE (GeometricComparison.Section.GeometricRestriction.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ sq
    U.unop.val.2.val U.unop.val.1.val U.unop.property)).op
  naturality _ _ _ := Subsingleton.elim _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOpenPairs
