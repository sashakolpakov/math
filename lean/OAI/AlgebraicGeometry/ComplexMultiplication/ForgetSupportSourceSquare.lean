import OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportDerivedMorphism
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedGlobalHyperNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HypercohomologyMapDerived
import OAI.AlgebraicGeometry.ComplexMultiplication.FunctorCompositionSquare
import OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedDerivedAugmentation
import OAI.AlgebraicGeometry.ComplexMultiplication.ExtPrecompositionNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveDerivedClass
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalDerived
import OAI.AlgebraicGeometry.Cohomology.WithSupport

/-! # Forget Support Source Square -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportSourceSquare

noncomputable section

/-! # Forgetting support is the literal inclusion into global injective cohomology -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace
open _root_.AlgebraicGeometry ComplexPoint _root_.TopCat.Sheaf _root_.CochainComplex.HomComplex _root_.HomologicalComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf TopCat.Sheaf.instAbelian

variable (X : Over (Spec (.of ℂ))) (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))

local instance CMForgetSupportSourceSquare.localInstance1 : Category (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  inferInstanceAs (Category (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat))

local instance CMForgetSupportSourceSquare.localInstance2 : HasDerivedCategory (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) :=
  HasDerivedCategory.standard _

local instance CMForgetSupportSourceSquare.localInstance3 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

theorem forgetSupportSourceSquare :
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafTerminalIso
        (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) isTerminalTop).inv) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (cokernel.π ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).map
        (homOfLE (le_top : S.compl ≤ ⊤))))) =
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (SupportedToGlobalHom.integerToSupportPairSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl)) := by
  let H := CochainComplex.singleFunctor (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) 0
  let Q := @DerivedCategory.Q.{1, 0, 1} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat)
    inferInstance inferInstance (HasDerivedCategory.standard _)
  let v := (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafTerminalIso
    (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) isTerminalTop).inv
  let w := cokernel.π ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).map
      (homOfLE (le_top : S.compl ≤ ⊤)))
  have hs := FunctorCompositionSquare.mapFunctorCompositionSquare H Q
    (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).hom v w
    (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom
    (H.map (SupportedToGlobalHom.integerToSupportPairSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl))
    (ForgetSupportDerivedMorphism.supportPairSourceComparison X S)
  exact hs

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportSourceSquare
