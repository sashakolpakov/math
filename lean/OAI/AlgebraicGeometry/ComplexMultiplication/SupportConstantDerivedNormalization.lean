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

/-! # Support Constant Derived Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SupportConstantDerivedNormalization

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Cohomology.WithSupport.ComplexPoint

/-! # Forgetting support is the literal inclusion into global injective cohomology -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace
open _root_.AlgebraicGeometry ComplexPoint _root_.TopCat.Sheaf _root_.CochainComplex.HomComplex _root_.HomologicalComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf TopCat.Sheaf.instAbelian

variable (X : Over (Spec (.of ℂ))) (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))

local instance CMForgetSupportConstantDerivedNormalization.localInstance1 : Category (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  inferInstanceAs (Category (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat))

local instance CMForgetSupportConstantDerivedNormalization.localInstance2 : HasDerivedCategory (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) :=
  HasDerivedCategory.standard _

local instance CMForgetSupportConstantDerivedNormalization.localInstance3 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

theorem forgetSupportConstantDerivedNormalization (n : ℕ) (b : H_[S]^n(X; ℚ)) :
    Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm (ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n b)) ≫
      (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X))⟦(n : ℤ)⟧' =
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
      (      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafTerminalIso
        (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) isTerminalTop).inv) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (cokernel.π ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).map
        (homOfLE (le_top : S.compl ≤ ⊤))))) ≫ Ext.homAddEquiv b) ≫
        (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X))⟦(n : ℤ)⟧' := by
  have ha := ForgetSupportDerivedMorphism.constantHypercohomologyExt_augmentation X n
    ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm (ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n b))
  have he := (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).apply_symm_apply
    (ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n b)
  have hh := congrArg (fun z : H^n(X; ℚ) =>
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
      Ext.homAddEquiv z ≫
        (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X))⟦(n : ℤ)⟧') he
  have hb := ForgetSupportDerivedMorphism.forgetSupportExt_hom X S n b
  have ht := congrArg (fun z =>
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom ≫ z ≫
      (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X))⟦(n : ℤ)⟧') hb
  simpa only using! ha.symm.trans (hh.trans ht)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SupportConstantDerivedNormalization
