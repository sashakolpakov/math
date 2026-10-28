import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality

/-! # Hypercohomology Map Derived -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HypercohomologyMapDerived

noncomputable section

/-! # The actual hypercohomology map as composition in the derived category -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf
variable (X : Over (Spec (.of ℂ)))
local instance CMHypercohomologyMapDerived.localInstance1 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _

theorem hypercohomologyMap_derived {K L : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (n : ℤ) (a : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n) :
    Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f n a) =
    Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q a ≫
      (DerivedCategory.Q.map f)⟦n⟧' := by
  simp only [ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.comp_mk₀]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HypercohomologyMapDerived
