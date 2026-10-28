import OAI.AlgebraicGeometry.ComplexMultiplication.ExtSmallComparison

/-! # Constant Hypercohomology Ext -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ConstantHypercohomologyExt

noncomputable section

/-! # The literal constant-sheaf comparison as a morphism in the derived category -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Abelian _root_.AlgebraicGeometry ComplexPoint

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf

variable (R : Type) [Field R] (X : Over (Spec (.of ℂ)))

local instance CMConstantHypercohomologyExt.localInstance1 : Category (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  inferInstanceAs (Category (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat))

local instance CMConstantHypercohomologyExt.localInstance2 : HasDerivedCategory (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) :=
  HasDerivedCategory.standard _

local instance CMConstantHypercohomologyExt.localInstance3 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

theorem constantHypercohomologyExt (n : ℕ)
    (a : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt R X) (n : ℤ)) :
    Ext.homAddEquiv (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n a) =
      DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X).inv ≫
        Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q a ≫
          (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle R X).hom)⟦(n : ℤ)⟧' := by
  have he := @ExtSmallComparison.extSmallShiftedHom_normalization.{1, 0, 1, 1}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat) inferInstance inferInstance
    (HasDerivedCategory.standard _) (HasExt.standard _) _ _ n
    (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n a)
  rw [he]
  dsimp only [ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology]
  exact ShiftedHomIsoNormalization.smallShiftedHomIso_normalization
    (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingleULift X)
    (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle R X) (n : ℤ) a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ConstantHypercohomologyExt
