import OAI.AlgebraicGeometry.ComplexMultiplication.ConstantHypercohomologyExt
import OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedDerivedAugmentation
import OAI.AlgebraicGeometry.ComplexMultiplication.ExtPrecompositionNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveDerivedClass
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalDerived
import OAI.AlgebraicGeometry.Cohomology.WithSupport

/-! # Forget Support Derived Morphism -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportDerivedMorphism

noncomputable section

open scoped OAI.AlgebraicGeometry.Cohomology.WithSupport.ComplexPoint

/-! # Forgetting support is the literal inclusion into global injective cohomology -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace
open _root_.AlgebraicGeometry ComplexPoint _root_.TopCat.Sheaf _root_.CochainComplex.HomComplex _root_.HomologicalComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf

variable (X : Over (Spec (.of ℂ))) (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))

local instance CMForgetSupportDerivedMorphism.localInstance1 : HasDerivedCategory (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) :=
  HasDerivedCategory.standard _

local instance CMForgetSupportDerivedMorphism.localInstance2 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

theorem constantHypercohomologyExt_augmentation (n : ℕ)
    (a : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X) (n : ℤ)) :
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
      Ext.homAddEquiv (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n a) ≫
        (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X))⟦(n : ℤ)⟧' =
    Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q a ≫
      (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X))⟦(n : ℤ)⟧' := by
  rw [ConstantHypercohomologyExt.constantHypercohomologyExt]
  exact ShiftedDerivedAugmentation.shiftedDerivedAugmentation_normalization
    (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X)
    (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle ℚ X) (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X)
    (n : ℤ) _

theorem forgetSupportExt_hom (n : ℕ) (b : H_[S]^n(X; ℚ)) :
    Ext.homAddEquiv (ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n b) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafTerminalIso
          (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) isTerminalTop).inv) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (cokernel.π ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).map
          (homOfLE (le_top : S.compl ≤ ⊤))))) ≫ Ext.homAddEquiv b := by
  exact ExtPrecompositionNormalization.extPrecomposition_normalization
    (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafTerminalIso
      (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) isTerminalTop).symm
    (cokernel.π ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).map
        (homOfLE (le_top : S.compl ≤ ⊤)))) n b

theorem supportPairSourceComparison :
    (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
      (CochainComplex.singleFunctor _ 0).map
        ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafTerminalIso
          (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) isTerminalTop).inv ≫
          cokernel.π ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).map
            (homOfLE (le_top : S.compl ≤ ⊤)))) =
    (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫
      (CochainComplex.singleFunctor _ 0).map
        (SupportedToGlobalHom.integerToSupportPairSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl) := by
  simp only [SupportedToGlobalHom.integerToSupportPairSheaf, SupportedToGlobalHom.integerToTerminalFreeSheafIso,
    ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift, ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.map_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportDerivedMorphism
