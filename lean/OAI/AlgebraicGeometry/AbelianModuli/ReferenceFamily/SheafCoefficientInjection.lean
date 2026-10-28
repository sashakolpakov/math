import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Sheaf Coefficient Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafCoefficientInjection

noncomputable section

/-! Degree-one coefficient lifting kills the connecting obstruction and
makes the degree-two coefficient map injective in actual sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace

theorem ext_two_kernel_zero_of_ext_one_surjective
    {C : Type*} [Category C] [Abelian C] [HasExt.{0} C]
    {T : C} {D : ShortComplex C} (hD : D.ShortExact)
    (h1 : ∀ u : Ext T D.X₃ 1, ∃ v : Ext T D.X₂ 1,
      v.comp (Ext.mk₀ D.g) (add_zero 1) = u)
    (a : Ext T D.X₁ 2) (ha : a.comp (Ext.mk₀ D.f) (add_zero 2) = 0) : a = 0 := by
  obtain ⟨u, hu⟩ := Ext.covariant_sequence_exact₁ T hD a ha (rfl : 1 + 1 = 2)
  obtain ⟨v, hv⟩ := h1 u
  have hd : u.comp hD.extClass (rfl : 1 + 1 = 2) = 0 := by
    rw [← hv]
    simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
  exact hu.symm.trans hd

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact)

local instance coefficientInjectionHasExt : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  hasExt_of_enoughInjectives _

include hS in
theorem sheafH2_injective_of_H1_surjective
    (h1 : Function.Surjective ((Sheaf.functorH (Opens.grothendieckTopology X) 1).map S.g)) :
    Function.Injective ((Sheaf.functorH (Opens.grothendieckTopology X) 2).map S.f) := by
  intro a b hab
  have hz : (Sheaf.functorH (Opens.grothendieckTopology X) 2).map S.f (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hd : a - b = 0 := ext_two_kernel_zero_of_ext_one_surjective
    (C := TopCat.Sheaf AddCommGrpCat.{0} X)
    (T := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift.{0, 0} ℤ))) hS h1 (a - b) hz
  exact sub_eq_zero.mp hd

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafCoefficientInjection
