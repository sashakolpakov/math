import OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

/-! # Normalized Positive Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedPositiveFormula

noncomputable section

/-! The genuine normalized ample-line formula gives the exact class formula used for diagonal positivity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {A D : Over S} [GrpObj A]
  (P : Line.Bundles.LineBundle (D ⊗ A).left) (ell : A ⟶ D) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

/-- Normalization at the actual identity section trivializes the constant-family line class. -/
theorem zero_class (e : (L.pullback η[A].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) :
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (1 : A ⟶ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 := by
  have hz : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass η[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 := Quotient.sound ⟨e⟩
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((toUnit A).left ≫ η[A].left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (toUnit A).left η[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans
    ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (toUnit A).left) hz).trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial _))

/-- An actual Poincare formula isomorphism supplies the required equality of intrinsic line classes. -/
theorem formula_class
    (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine P ell).sheaf (L.pullback (fst A A).left).sheaf)
      (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf) :
    DiagonalLineClass.biextensionClass P ell * Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := Quotient.sound ⟨e⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedPositiveFormula
