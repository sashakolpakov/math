import OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportDerivedMorphism
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedGlobalHyperNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HypercohomologyMapDerived
import OAI.AlgebraicGeometry.ComplexMultiplication.CompositionSquare
import OAI.AlgebraicGeometry.ComplexMultiplication.FunctorCompositionSquare
import OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportSourceSquare
import OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedDerivedAugmentation
import OAI.AlgebraicGeometry.ComplexMultiplication.ExtPrecompositionNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveDerivedClass
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalDerived
import OAI.AlgebraicGeometry.Cohomology.WithSupport

/-! # Forget Support Derived Square -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportDerivedSquare

noncomputable section

open scoped OAI.AlgebraicGeometry.Cohomology.WithSupport.ComplexPoint

/-! # Forgetting support is the literal inclusion into global injective cohomology -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace
open _root_.AlgebraicGeometry ComplexPoint _root_.TopCat.Sheaf _root_.CochainComplex.HomComplex _root_.HomologicalComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf TopCat.Sheaf.instAbelian

variable (X : Over (Spec (.of ℂ))) (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))

local instance CMForgetSupportDerivedSquare.localInstance1 : Category (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  inferInstanceAs (Category (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat))

local instance CMForgetSupportDerivedSquare.localInstance2 : HasDerivedCategory (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) :=
  HasDerivedCategory.standard _

local instance CMForgetSupportDerivedSquare.localInstance3 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

theorem forgetSupportDerivedSquare (n : ℕ) (b : H_[S]^n(X; ℚ)) :
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
      (      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafTerminalIso
        (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) isTerminalTop).inv) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (cokernel.π ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).map
        (homOfLE (le_top : S.compl ≤ ⊤))))) ≫ Ext.homAddEquiv b) ≫
        (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X))⟦(n : ℤ)⟧' =
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (SupportedToGlobalHom.integerToSupportPairSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl)) ≫
      Ext.homAddEquiv b ≫ (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X))⟦(n : ℤ)⟧' := by
  simpa only using! CompositionSquare.compositionSquare_postcomp _ _ _ _ _
    (Ext.homAddEquiv b)
    ((DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X))⟦(n : ℤ)⟧')
    (ForgetSupportSourceSquare.forgetSupportSourceSquare X S)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportDerivedSquare
