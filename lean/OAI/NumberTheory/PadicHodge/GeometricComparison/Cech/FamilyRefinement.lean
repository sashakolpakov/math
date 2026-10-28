import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Family Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement

noncomputable section

/-! Actual refinement of formal covering families acts naturally on Čech cochains with arbitrary additive coefficients. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicTopology

universe w v u v' u'

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  (U V : FormalCoproduct.{w} C) (r : V ⟶ U)

def cosimplicialMap (P : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor U.cech).obj P ⟶
      (FormalCoproduct.cosimplicialObjectFunctor V.cech).obj P :=
  Functor.whiskerRight (FormalCoproduct.cechFunctor.map r).rightOp ((FormalCoproduct.evalOp C A).obj P)

def map (P : Cᵒᵖ ⥤ A) : (FormalCoproduct.cochainComplexFunctor U.cech).obj P ⟶
    (FormalCoproduct.cochainComplexFunctor V.cech).obj P :=
  (alternatingCofaceMapComplex A).map (cosimplicialMap U V r P)

theorem naturality {P Q : Cᵒᵖ ⥤ A} (a : P ⟶ Q) :
    (FormalCoproduct.cochainComplexFunctor U.cech).map a ≫ CechFamilyRefinement.map U V r Q =
      CechFamilyRefinement.map U V r P ≫ (FormalCoproduct.cochainComplexFunctor V.cech).map a := by
  ext n : 1
  exact (((FormalCoproduct.evalOp C A).map a).naturality
    ((FormalCoproduct.cechFunctor.map r).app (op (SimplexCategory.mk n))).op).symm

def transformation : FormalCoproduct.cochainComplexFunctor (A := A) U.cech ⟶
    FormalCoproduct.cochainComplexFunctor (A := A) V.cech where
  app P := CechFamilyRefinement.map U V r P
  naturality _ _ a := CechFamilyRefinement.naturality U V r a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement
