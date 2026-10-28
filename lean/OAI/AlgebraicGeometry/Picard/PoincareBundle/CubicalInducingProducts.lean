import OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingPointClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Cubical Inducing Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingProducts

noncomputable section

/-! The geometric cube theorem supplies actual invertible products in both variables for the quotient inducing line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingPointClasses
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

/-- The actual difference class is multiplicative in its second test point. -/
theorem multiply_right {T : Over (Spec (.of k))} (a b c : T ⟶ A) :
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift a (b * c)).left (InducingClass.Bundle.lineClass A L) =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift a b).left (InducingClass.Bundle.lineClass A L) *
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift a c).left (InducingClass.Bundle.lineClass A L) := by
  rw [← CubicalInducingPointClasses.pairing_eq, ← CubicalInducingPointClasses.pairing_eq, ← CubicalInducingPointClasses.pairing_eq]
  exact congrArg Additive.toMul ((FormalGeometry.Completion.SchemePointPicardPairing.Construction.schemePointPicardPairing A L T (Additive.ofMul a)).map_add
    (Additive.ofMul b) (Additive.ofMul c))

/-- The actual difference class is multiplicative in its first test point. -/
theorem multiply_left {T : Over (Spec (.of k))} (a b c : T ⟶ A) :
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift (a * b) c).left (InducingClass.Bundle.lineClass A L) =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift a c).left (InducingClass.Bundle.lineClass A L) *
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift b c).left (InducingClass.Bundle.lineClass A L) := by
  rw [← CubicalInducingPointClasses.pairing_eq, ← CubicalInducingPointClasses.pairing_eq, ← CubicalInducingPointClasses.pairing_eq]
  exact congrArg (fun z => (z (Additive.ofMul c)).toMul)
    ((FormalGeometry.Completion.SchemePointPicardPairing.Construction.schemePointPicardPairing A L T).map_add (Additive.ofMul a) (Additive.ofMul b))

/-- An actual vertical product isomorphism, obtained from the proved class identity. -/
def verticalIso :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Vertical.ProductParameters.inputLeft A A))
      (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Vertical.ProductParameters.inputRight A A)) ≅
        Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Vertical.ProductParameters.outputPoint A A) := by
  have h : Homomorphisms.SchemePullback.Construction.schemePicardPullback (Vertical.ProductParameters.inputLeft A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (InducingClass.Bundle.line A L)) *
      Homomorphisms.SchemePullback.Construction.schemePicardPullback (Vertical.ProductParameters.inputRight A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (InducingClass.Bundle.line A L)) =
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (Vertical.ProductParameters.outputPoint A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (InducingClass.Bundle.line A L)) := by
    rw [InducingClass.Bundle.classOf_line]
    exact (multiply_right A L (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ fst A A)
      (snd A (A ⊗ A) ≫ snd A A)).symm
  exact Classical.choice (Quotient.exact h)

/-- An actual horizontal product isomorphism, with no product supplied as a hypothesis. -/
def horizontalIso :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Product.ParameterSchemes.inputLeft A A))
      (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Product.ParameterSchemes.inputRight A A)) ≅
        Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Product.ParameterSchemes.outputPoint A A) := by
  have h : Homomorphisms.SchemePullback.Construction.schemePicardPullback (Product.ParameterSchemes.inputLeft A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (InducingClass.Bundle.line A L)) *
      Homomorphisms.SchemePullback.Construction.schemePicardPullback (Product.ParameterSchemes.inputRight A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (InducingClass.Bundle.line A L)) =
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (Product.ParameterSchemes.outputPoint A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (InducingClass.Bundle.line A L)) := by
    rw [InducingClass.Bundle.classOf_line]
    exact (multiply_left A L (fst (A ⊗ A) A ≫ fst A A) (fst (A ⊗ A) A ≫ snd A A)
      (snd (A ⊗ A) A)).symm
  exact Classical.choice (Quotient.exact h)

/-- The vertical isomorphism as a bilinear sheaf map. -/
def vertical : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Vertical.ProductParameters.inputLeft A A))
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Vertical.ProductParameters.inputRight A A))
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Vertical.ProductParameters.outputPoint A A)) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (verticalIso A L).hom

theorem vertical_isIso : IsIso (Bilinear.BilinearPullback.toHom (vertical A L)) := by
  have h : Bilinear.BilinearPullback.toHom (vertical A L) = (verticalIso A L).hom :=
    (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm_apply_apply _
  rw [h]
  infer_instance

/-- The horizontal isomorphism as a bilinear sheaf map. -/
def horizontal : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Product.ParameterSchemes.inputLeft A A))
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Product.ParameterSchemes.inputRight A A))
    (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingClass.Bundle.line A L)) (Product.ParameterSchemes.outputPoint A A)) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (horizontalIso A L).hom

theorem horizontal_isIso : IsIso (Bilinear.BilinearPullback.toHom (horizontal A L)) := by
  have h : Bilinear.BilinearPullback.toHom (horizontal A L) = (horizontalIso A L).hom :=
    (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm_apply_apply _
  rw [h]
  infer_instance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CubicalInducingProducts
