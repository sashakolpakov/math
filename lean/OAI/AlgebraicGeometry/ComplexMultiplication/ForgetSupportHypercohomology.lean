import OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportDerivedMorphism
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedGlobalHyperNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HypercohomologyMapDerived
import OAI.AlgebraicGeometry.ComplexMultiplication.CompositionSquare
import OAI.AlgebraicGeometry.ComplexMultiplication.FunctorCompositionSquare
import OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportSourceSquare
import OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportDerivedSquare
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportConstantDerivedNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedDerivedAugmentation
import OAI.AlgebraicGeometry.ComplexMultiplication.ExtPrecompositionNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveDerivedClass
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalDerived
import OAI.AlgebraicGeometry.Cohomology.WithSupport

/-! # Forget Support Hypercohomology -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportHypercohomology

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

local instance CMForgetSupportHypercohomology.localInstance1 : Category (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  inferInstanceAs (Category (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat))

local instance CMForgetSupportHypercohomology.localInstance2 : HasDerivedCategory (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) :=
  HasDerivedCategory.standard _

local instance CMForgetSupportHypercohomology.localInstance3 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

theorem forgetSupport_hypercohomology (n : ℕ) (b : H_[S]^n(X; ℚ)) :
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X) (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm (ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n b)) =
    GlobalNaturality.globalSectionsToHypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X) (n : ℤ)
      (homologyMap (SupportedToGlobalHom.supportedToGlobalSectionComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
        (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)) (n : ℤ)
        (ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X S n b)) := by
  apply (Localization.SmallShiftedHom.equiv
    (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  have hr := Reference.SupportedGlobalHyperNormalization.originalSupportedGlobalHyperNormalization X S n b
  have hl := HypercohomologyMapDerived.hypercohomologyMap_derived X (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X) (n : ℤ)
    ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm (ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n b))
  have hc := SupportConstantDerivedNormalization.forgetSupportConstantDerivedNormalization X S n b
  have hs := ForgetSupportDerivedSquare.forgetSupportDerivedSquare X S n b
  simpa only using! hl.trans (hc.trans (hs.trans hr.symm))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportHypercohomology
