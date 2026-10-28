import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowInducingAutomorphism
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedTensorContraction
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RightContraction

/-! # Row Contraction Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowContractionFormula

noncomputable section

/-! The neutral-row automorphism is right contraction of the actual inducing product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RightContraction.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

theorem swapped_formula {X : Scheme.{u}} {M N P : X.Modules} (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv N M P (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M ≪≫ e).hom =
      AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P e.hom) := by
  change AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv N M P ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso N M).hom ≫ e.hom) = _
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction.tensorModuleCommIso_bilinear, ← AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear_postcomp,
    ← Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp]

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) (lift (𝟙 A) (1 : A ⟶ A)))

def bilinear : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (𝟙 A)) (Line.Fibers.fiber L (1 : A ⟶ A)) (Line.Fibers.fiber L (𝟙 A)) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (RowInducingAutomorphism.productIso Q L e s).hom

theorem automorphism_hom (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Line.Fibers.fiber L (1 : A ⟶ A)) :
    (RowInducingAutomorphism.automorphism Q L e s t).hom =
      AbelianScheme.IsogenyQuotient.RightContraction.Construction.lineContractRight (bilinear Q L e s) t.hom := by
  have h := FramedTensorContraction.hom_eq
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L (1 : A ⟶ A)) (Line.Fibers.fiber L (𝟙 A)) ≪≫
      RowInducingAutomorphism.productIso Q L e s) t
  exact h.trans (congrArg (fun b => Bilinear.Contraction.contractLeft b t.hom)
    (swapped_formula (RowInducingAutomorphism.productIso Q L e s)))

variable (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over S)).left ≅ Line.Fibers.fiber L η[A])

/-- On each test fiber the actual automorphism is contraction by the naturally pulled identity frame. -/
theorem atPoint_hom {T : Over S} (x : T ⟶ A) :
    (ProperFiberAutomorphismScalar.atPoint L
      (RowInducingAutomorphism.automorphism Q L e s (NaturalOriginLineFrames.frame L o A)) x).hom =
    AbelianScheme.IsogenyQuotient.RightContraction.Construction.lineContractRight
      (Line.Fibers.pullBilinear L x (𝟙 A) (1 : A ⟶ A) (𝟙 A) x (1 : T ⟶ A) x
        (Category.comp_id x) (MonObj.comp_one x) (Category.comp_id x) (bilinear Q L e s))
      (NaturalOriginLineFrames.frame L o T).hom := by
  have hp := AbelianScheme.IsogenyQuotient.RightContraction.Construction.lineContractRight_pullback L x (𝟙 A) (1 : A ⟶ A) (𝟙 A) x (1 : T ⟶ A) x
    (Category.comp_id x) (MonObj.comp_one x) (Category.comp_id x) (bilinear Q L e s)
    (NaturalOriginLineFrames.frame L o A).hom
  have hn := NaturalOriginLineFrames.section_natural L o x
  have he := congrArg (fun f => (Line.Fibers.fiberPullbackIso L x (𝟙 A) x (Category.comp_id x)).inv ≫
    (Scheme.Modules.pullback x.left).map f ≫ (Line.Fibers.fiberPullbackIso L x (𝟙 A) x (Category.comp_id x)).hom)
    (automorphism_hom Q L e s (NaturalOriginLineFrames.frame L o A))
  exact he.trans (hp.symm.trans (congrArg (AbelianScheme.IsogenyQuotient.RightContraction.Construction.lineContractRight
    (Line.Fibers.pullBilinear L x (𝟙 A) (1 : A ⟶ A) (𝟙 A) x (1 : T ⟶ A) x
      (Category.comp_id x) (MonObj.comp_one x) (Category.comp_id x) (bilinear Q L e s))) hn))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.RowContractionFormula
