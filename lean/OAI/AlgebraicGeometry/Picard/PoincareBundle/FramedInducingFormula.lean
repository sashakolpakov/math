import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RestrictionSquare
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.InducingProductSymmetry

/-! # Framed Inducing Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedInducingFormula

noncomputable section

/-! A uniform formula for the products obtained from inducing-line formulas and Poincare frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

theorem pullback_formula {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y)
    (M N P : Line.Bundles.LineBundle Y.left) (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf ≅ P.sheaf) :
    Bilinear.BilinearPullback.pullback p.left M.isLine N.isLine (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ e.hom) =
      AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (RestrictedBilinearEquivariance.formula p M N P e).hom := by
  simp only [Bilinear.BilinearPullback.pullback, Bilinear.BilinearPullback.pulledHom, Bilinear.BilinearPullback.toHom, Equiv.symm_apply_apply,
    RestrictedBilinearEquivariance.formula, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]

theorem pullback_formula_invertible {X Y : Scheme.{u}} (p : X ⟶ Y)
    {M N P : Y.Modules} (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P) :
    IsIso (Bilinear.BilinearPullback.toHom (Bilinear.BilinearPullback.pullback p hM hN (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ e.hom))) := by
  rw [Bilinear.BilinearPullback.toHom_pullback]
  dsimp only [Bilinear.BilinearPullback.pulledHom, Bilinear.BilinearPullback.toHom]
  rw [Equiv.symm_apply_apply]
  infer_instance

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])

/-- The regrouped original formula is an actual bilinear map in its Poincare and external-line factors. -/
def bilinear : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap Q.sheaf (InducingFormulaSymmetry.factorLine A L).sheaf (InducingFormulaSymmetry.targetLine A L).sheaf :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (InducingFormulaSymmetry.regrouped A Q L e).hom

/-- Insert any actual frame on any scheme restriction of the Poincare factor. -/
def product {K : Over S} (p : K ⟶ A ⊗ A)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) p) :
    Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L)) p ⟶ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) p :=
  Bilinear.Contraction.contractLeft (Bilinear.BilinearPullback.pullback p.left Q.locallyTrivial (InducingFormulaSymmetry.factorLine A L).locallyTrivial (bilinear Q L e)) s.hom

/-- Inserting an actual frame into the inducing isomorphism gives an invertible product. -/
instance product_isIso {K : Over S} (p : K ⟶ A ⊗ A)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) p) : IsIso (product Q L e p s) := by
  have hp : IsIso (Bilinear.BilinearPullback.toHom (Bilinear.BilinearPullback.pullback p.left Q.locallyTrivial (InducingFormulaSymmetry.factorLine A L).locallyTrivial (bilinear Q L e))) :=
    pullback_formula_invertible p.left Q.locallyTrivial (InducingFormulaSymmetry.factorLine A L).locallyTrivial (InducingFormulaSymmetry.regrouped A Q L e)
  exact @Bilinear.Contraction.contractLeft_isIso _ _ _ _
    (Bilinear.BilinearPullback.pullback p.left Q.locallyTrivial (InducingFormulaSymmetry.factorLine A L).locallyTrivial (bilinear Q L e)) s.hom
    s.isIso_hom hp

/-- This formula is precisely the previously constructed actual product on an isotropic intersection. -/
theorem intersection_product {H : Over S} (i : H ⟶ A)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf) :
    product Q L e (i ⊗ₘ i) (Kernel.IntersectionFrames.horizontalFrame i i (Line.Comparison.Bundle.fromShared Q) s) =
      Isotropic.InducingProductSymmetry.product i Q L s e := by
  have hp := pullback_formula (i ⊗ₘ i) (Line.Comparison.Bundle.fromShared Q) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L))
    (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) (InducingFormulaSymmetry.regrouped A Q L e)
  exact congrArg (fun β => Bilinear.Contraction.contractLeft β (Kernel.IntersectionFrames.horizontalFrame i i (Line.Comparison.Bundle.fromShared Q) s).hom) hp

/-- The uniform framed product evaluates with the actual global frame at every lifted test point. -/
theorem evaluation {K T : Over S} (p : K ⟶ A ⊗ A)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) p)
    (a : T ⟶ K) (q : T ⟶ A ⊗ A) (h : a ≫ p = q) :
    (Scheme.Modules.pullback a.left).map (product Q L e p s) ≫
        (Line.Fibers.fiberPullbackIso (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) a p q h).hom =
      (Line.Fibers.fiberPullbackIso (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L)) a p q h).hom ≫
        product Q L e q (GlobalPullbackFrame.atPoint p (Line.Comparison.Bundle.fromShared Q) s a q h) :=
  Bilinear.RestrictionSquare.frame_evaluation p (Line.Comparison.Bundle.fromShared Q) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L))
    (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) (bilinear Q L e) s a q h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedInducingFormula
