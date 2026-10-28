import OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepExt
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionClasses

/-! # Two Step Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TwoStepBoundary

noncomputable section

/-! Actual two-step connecting maps into ordinary sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

def sheafTwoStepBoundary (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (hS : S.Exact) [Mono S.f] :
    (cokernel (TwoStepQuotient.firstQuotientDifferential S)).obj.obj (op (⊤ : Opens X)) →+
      CategoryTheory.Sheaf.H S.X₁ 2 :=
  ((TwoStepExt.twoStepQuotientExtClass S hS).postcomp (ResolutionClasses.sheafCohomologySource X) (zero_add 2)).comp
    (CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop).symm.toAddMonoidHom

theorem sheafTwoStepBoundary_naturality {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.Exact) (hT : T.Exact) [Mono S.f] [Mono T.f] (φ : S ⟶ T)
    (t : (cokernel (TwoStepQuotient.firstQuotientDifferential S)).obj.obj (op (⊤ : Opens X))) :
    CategoryTheory.Sheaf.H.map φ.τ₁ 2 (sheafTwoStepBoundary S hS t) =
      sheafTwoStepBoundary T hT ((TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (⊤ : Opens X)) t) := by
  change (((CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop).symm t).comp
    (TwoStepExt.twoStepQuotientExtClass S hS) (zero_add 2)).comp (Ext.mk₀ φ.τ₁) (add_zero 2) = _
  rw [Ext.comp_assoc_of_third_deg_zero, TwoStepExt.twoStepQuotientExtClass_naturality hS hT φ,
    ← Ext.comp_assoc_of_second_deg_zero]
  have hn := CategoryTheory.Sheaf.H.equiv₀_symm_naturality
    (f := TwoStepQuotientNaturality.secondQuotientMap φ) isTerminalTop t
  exact congrArg (fun z : CategoryTheory.Sheaf.H (cokernel (TwoStepQuotient.firstQuotientDifferential T)) 0 =>
    z.comp (TwoStepExt.twoStepQuotientExtClass T hT) (zero_add 2)) hn

theorem sheafTwoStepBoundary_image_eq_zero
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.Exact) (hT : T.Exact) [Mono S.f] [Mono T.f] (φ : S ⟶ T)
    (t : (cokernel (TwoStepQuotient.firstQuotientDifferential S)).obj.obj (op (⊤ : Opens X)))
    (ht : (TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (⊤ : Opens X)) t = 0) :
    CategoryTheory.Sheaf.H.map φ.τ₁ 2 (sheafTwoStepBoundary S hS t) = 0 := by
  rw [sheafTwoStepBoundary_naturality hS hT φ t, ht, map_zero]

theorem sheafTwoStepBoundary_of_section_eq_zero
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.Exact) [Mono S.f]
    (a : S.X₃.obj.obj (op (⊤ : Opens X))) :
    sheafTwoStepBoundary S hS ((cokernel.π (TwoStepQuotient.firstQuotientDifferential S)).hom.app
      (op (⊤ : Opens X)) a) = 0 := by
  change ((CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop).symm
    ((cokernel.π (TwoStepQuotient.firstQuotientDifferential S)).hom.app (op (⊤ : Opens X)) a)).comp
    (TwoStepExt.twoStepQuotientExtClass S hS) (zero_add 2) = 0
  rw [← CategoryTheory.Sheaf.H.equiv₀_symm_naturality]
  change (((CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm a).comp
    (Ext.mk₀ (cokernel.π (TwoStepQuotient.firstQuotientDifferential S))) (add_zero 0)).comp
      ((TwoStepQuotient.secondQuotientSequence_shortExact S hS).extClass.comp
        (TwoStepQuotient.firstQuotientSequence_shortExact S).extClass (rfl : 1 + 1 = 2)) (zero_add 2) = 0
  rw [Ext.comp_assoc_of_second_deg_zero, ← Ext.comp_assoc _ _ _ (zero_add 1)
    (rfl : 1 + 1 = 2) (rfl : 0 + 1 + 1 = 2)]
  have hz : (Ext.mk₀ (cokernel.π (TwoStepQuotient.firstQuotientDifferential S))).comp
      (TwoStepQuotient.secondQuotientSequence_shortExact S hS).extClass (zero_add 1) = 0 :=
    (TwoStepQuotient.secondQuotientSequence_shortExact S hS).comp_extClass
  rw [hz, Ext.zero_comp, Ext.comp_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TwoStepBoundary
