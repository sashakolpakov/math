import OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepQuotientNaturality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # Two Step Ext -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepExt

noncomputable section

/-! The actual product of the two connecting extension classes and its naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

def twoStepQuotientExtClass (S : ShortComplex C) (hS : S.Exact) [Mono S.f] :
    Ext (cokernel (TwoStepQuotient.firstQuotientDifferential S)) S.X₁ 2 :=
  (TwoStepQuotient.secondQuotientSequence_shortExact S hS).extClass.comp
    (TwoStepQuotient.firstQuotientSequence_shortExact S).extClass (rfl : 1 + 1 = 2)

theorem twoStepQuotientExtClass_naturality {S T : ShortComplex C}
    (hS : S.Exact) (hT : T.Exact) [Mono S.f] [Mono T.f] (φ : S ⟶ T) :
    (twoStepQuotientExtClass S hS).comp (Ext.mk₀ φ.τ₁) (add_zero 2) =
      (Ext.mk₀ (TwoStepQuotientNaturality.secondQuotientMap φ)).comp (twoStepQuotientExtClass T hT) (zero_add 2) := by
  have h₀ := ShortComplex.ShortExact.extClass_naturality
    (TwoStepQuotient.firstQuotientSequence_shortExact S) (TwoStepQuotient.firstQuotientSequence_shortExact T)
    (TwoStepQuotientNaturality.firstQuotientSequenceMap φ)
  have h₁ := ShortComplex.ShortExact.extClass_naturality
    (TwoStepQuotient.secondQuotientSequence_shortExact S hS) (TwoStepQuotient.secondQuotientSequence_shortExact T hT)
    (TwoStepQuotientNaturality.secondQuotientSequenceMap φ)
  change (TwoStepQuotient.firstQuotientSequence_shortExact S).extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) =
    (Ext.mk₀ (TwoStepQuotientNaturality.firstQuotientMap φ)).comp (TwoStepQuotient.firstQuotientSequence_shortExact T).extClass (zero_add 1) at h₀
  change (TwoStepQuotient.secondQuotientSequence_shortExact S hS).extClass.comp (Ext.mk₀ (TwoStepQuotientNaturality.firstQuotientMap φ)) (add_zero 1) =
    (Ext.mk₀ (TwoStepQuotientNaturality.secondQuotientMap φ)).comp (TwoStepQuotient.secondQuotientSequence_shortExact T hT).extClass (zero_add 1) at h₁
  unfold twoStepQuotientExtClass
  rw [Ext.comp_assoc_of_third_deg_zero, h₀, ← Ext.comp_assoc_of_second_deg_zero, h₁]
  exact Ext.comp_assoc _ _ _ (zero_add 1) (rfl : 1 + 1 = 2) (rfl : 0 + 1 + 1 = 2)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepExt
