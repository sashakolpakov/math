import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalSheafPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HomPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorSingle

/-! # Global Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalPullback

noncomputable section

/-! # Genuine pullback of the original global-section complexes

Actual global pullback and actual Hom-complex pullback commute under the
original evaluation-at-one isomorphism of complexes.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.CochainComplex.HomComplex

variable {X Y : Over (Spec (.of ℂ))}

/-- Actual inverse image, followed by original integer source transport, on Hom complexes. -/
def originalHomComplexInverseImageMap (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) :
    CochainComplex.HomComplex
        (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K ⟶
      CochainComplex.HomComplex
        (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) :=
  HomFunctorMap.HomComplex.functorMap (AnalyticInverseImage.originalAnalyticSheafInverseImage f) _ K ≫
    Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap (HomPullback.originalIntegerSingleInverseImageIso f).inv _

/-- The genuine adjunction-unit map on actual original global-section complexes. -/
def originalGlobalSectionsComplexInverseImage (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) :
    Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) K ⟶
      Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) :=
  (NatTrans.mapHomologicalComplex (GlobalSheafPullback.originalGlobalSectionsInverseImageNat f)
    (ComplexShape.up ℤ)).app K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original evaluation-at-one complex iso commutes with genuine inverse image. -/
theorem originalHomComplexGlobalSections_inverseImage (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) :
    originalHomComplexInverseImageMap f K ≫
        (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
          ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K)).hom =
      (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) K).hom ≫
        originalGlobalSectionsComplexInverseImage f K := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  apply AddCommGrpCat.hom_ext
  ext z
  change Cohomology.GlobalSections.TopCat.Sheaf.integerConstantHomAddEquivGlobalSections
      ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).obj (K.X n))
      (Cochain.fromSingleEquiv (zero_add n)
        ((Cochain.ofHom ((CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).map
            ((AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).inv.app (AddCommGrpCat.of ℤ)) ≫
              ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapCochainComplexSingleFunctor 0).inv.app
                ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj
                  (AddCommGrpCat.of ℤ)))).comp (z.map (AnalyticInverseImage.originalAnalyticSheafInverseImage f))
                    (zero_add n))) =
    (GlobalSheafPullback.originalGlobalSectionsInverseImageNat f).app (K.X n)
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantHomAddEquivGlobalSections (K.X n)
        (Cochain.fromSingleEquiv (zero_add n) z))
  rw [HomFunctorSingle.HomComplex.fromSingleEquiv_functorMap_precomp]
  exact GlobalSheafPullback.originalIntegerConstantHomGlobalSections_inverseImage f (K.X n) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine pullback on Hom-complex homology is the original transported class pullback. -/
theorem homologyAddEquiv_originalHomComplexInverseImage (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ)
    (z : (CochainComplex.HomComplex
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K).homology n) :
    homologyAddEquiv _ ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n
        (HomologicalComplex.homologyMap (originalHomComplexInverseImageMap f K) n z) =
      HomPullback.originalHomComplexClassInverseImage f K n (homologyAddEquiv _ K n z) := by
  let g := HomFunctorMap.HomComplex.functorMap (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
    (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K
  let h := Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap (HomPullback.originalIntegerSingleInverseImageIso f).inv
    ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K)
  have hc := ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp g h n) z
  have hp := Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.homologyAddEquiv_precompMap (HomPullback.originalIntegerSingleInverseImageIso f).inv
    ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n
      (HomologicalComplex.homologyMap g n z)
  have hf := HomFunctorMap.HomComplex.homologyAddEquiv_functorMap (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
    (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K n z
  exact (congrArg (homologyAddEquiv _ _ n) hc).trans
    (hp.trans (congrArg (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompClass (HomPullback.originalIntegerSingleInverseImageIso f).inv
      ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n) hf))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalPullback
