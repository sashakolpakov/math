import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalDerived
import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality
import OAI.AlgebraicGeometry.Cohomology.WithSupport

/-! # Supported Global Hyper Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedGlobalHyperNormalization

noncomputable section

open scoped OAI.AlgebraicGeometry.Cohomology.WithSupport.ComplexPoint

/-! # The concrete supported Ext class in global hypercohomology -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace
open _root_.AlgebraicGeometry ComplexPoint _root_.TopCat.Sheaf _root_.CochainComplex.HomComplex _root_.HomologicalComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf TopCat.Sheaf.instAbelian
variable (X : Over (Spec (.of ℂ))) (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))
local instance CMOriginalSupportedGlobalHyperNormalization.localInstance1 : Category (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  inferInstanceAs (Category (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat))
local instance CMOriginalSupportedGlobalHyperNormalization.localInstance2 : HasDerivedCategory (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) :=
  HasDerivedCategory.standard _
local instance CMOriginalSupportedGlobalHyperNormalization.localInstance3 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

theorem originalSupportedGlobalHyperNormalization (n : ℕ) (b : H_[S]^n(X; ℚ)) :
    Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
      (GlobalNaturality.globalSectionsToHypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X) (n : ℤ)
        (homologyMap (SupportedToGlobalHom.supportedToGlobalSectionComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
          (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)) (n : ℤ)
          (ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X S n b))) =
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (SupportedToGlobalHom.integerToSupportPairSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl)) ≫
      Ext.homAddEquiv b ≫
        (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X))⟦(n : ℤ)⟧' := by
  have hg := @SupportedInjectiveGlobalDerived.supportedInjectiveGlobalDerivedClass (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
    (HasExt.standard _) ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj
      (AddCommGrpCat.of ℚ)) (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_isKInjective X)
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X)
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation_quasiIso X) n b
  have hc := GlobalNaturality.homComplexClassToHypercohomology_equiv X (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)
    (n : ℤ) (GlobalNaturality.globalSectionsToHomComplexClass X (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X) (n : ℤ)
      (homologyMap (SupportedToGlobalHom.supportedToGlobalSectionComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
        (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)) (n : ℤ)
        (ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X S n b)))
  simpa only [Category.assoc] using! hc.trans
    (congrArg (fun z => DerivedCategory.Q.map
      (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫ z) hg)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedGlobalHyperNormalization
