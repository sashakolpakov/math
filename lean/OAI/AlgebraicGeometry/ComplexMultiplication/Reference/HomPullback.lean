import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AnalyticInverseImage
import OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorMap
import OAI.AlgebraicGeometry.Cohomology.GlobalSections

/-! # Hom Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HomPullback

noncomputable section

/-! # Actual inverse image of the original Hom-complex classes

The original integer source object and the original integer-complex transport
are retained. Actual inverse image maps cocycles and cohomology classes through
the genuine constant-sheaf isomorphism.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.CochainComplex.HomComplex

variable {X Y : Over (Spec (.of ℂ))}

/-- Genuine inverse image of the original integer single-complex source object. -/
def originalIntegerSingleInverseImageIso (f : X ⟶ Y) :
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ≅
        Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapCochainComplexSingleFunctor 0).app
    ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj (AddCommGrpCat.of ℤ)) ≪≫
    (CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).mapIso
      ((AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).app (AddCommGrpCat.of ℤ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original integer-complex transport factors through the actual original single object. -/
theorem originalIntegerComplexInverseImageIso_factor (f : X ⟶ Y) :
    AnalyticInverseImage.originalIntegerComplexInverseImageIso f =
      ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle Y) ≪≫
        originalIntegerSingleInverseImageIso f ≪≫
          (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).symm := by
  unfold AnalyticInverseImage.originalIntegerComplexInverseImageIso originalIntegerSingleInverseImageIso
  rw [Iso.trans_assoc]

/-- Actual inverse image of original Hom-complex classes, with precisely the original source. -/
def originalHomComplexClassInverseImage (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ) :
    CohomologyClass (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K n →+
      CohomologyClass (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
        ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n :=
  (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompClass (originalIntegerSingleInverseImageIso f).inv
    ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n).comp
      (HomFunctorMap.HomComplex.functorMapClass (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
        (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K n)

/-- Actual inverse image on original classes is given by actual functorial mapping of cocycles. -/
theorem originalHomComplexClassInverseImage_mk (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ)
    (z : Cocycle (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K n) :
    originalHomComplexClassInverseImage f K n (CohomologyClass.mk z) =
      CohomologyClass.mk
        ((HomFunctorMap.HomComplex.functorMapCocycle (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
          (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K n z).precomp
            (originalIntegerSingleInverseImageIso f).inv) := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HomPullback
