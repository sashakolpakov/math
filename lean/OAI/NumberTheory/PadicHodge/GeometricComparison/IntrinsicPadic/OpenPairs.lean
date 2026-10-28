import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction

/-! # Open Pairs -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenPairs.IntrinsicPadicGeometricOpenPairs

noncomputable section

/-! Compatible integral affine pairs give compatible special-fiber
opens and their original inverse-image restriction transformation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)

def source : Affine.MapPairs.AffineMapPairs.Charts u.left ⥤ Y₁.left.Opens :=
  Affine.MapPairs.AffineMapPairs.source u.left ⋙ SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₁ Y₁ f₁

def target : Affine.MapPairs.AffineMapPairs.Charts u.left ⥤ Y₂.left.Opens :=
  Affine.MapPairs.AffineMapPairs.target u.left ⋙ SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₂ Y₂ f₂

def preimage : Affine.MapPairs.AffineMapPairs.Charts u.left ⥤ Y₁.left.Opens :=
  target p u f₂ ⋙ TopologicalSpace.Opens.map v.left.base

def restriction : (preimage p u v f₂).op ⟶ (source p u f₁).op where
  app U := (homOfLE (Section.GeometricRestriction.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ hsquare
    U.unop.val.2.val U.unop.val.1.val U.unop.property)).op
  naturality _ _ _ := Subsingleton.elim _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenPairs.IntrinsicPadicGeometricOpenPairs
