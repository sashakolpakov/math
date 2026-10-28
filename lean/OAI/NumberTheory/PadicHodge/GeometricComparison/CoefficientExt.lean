import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-! # Coefficient Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientExt.CoefficientExtIso

noncomputable section

/-! Coefficient Ext vanishing transports through an actual isomorphism of coefficient objects. -/

open _root_.CategoryTheory Abelian Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem subsingleton {A B : C} (e : A ≅ B) (M : C) (n : ℕ)
    [Subsingleton (Ext.{w} B M n)] : Subsingleton (Ext.{w} A M n) := by
  let E : Ext.{w} A M n ≃ Ext.{w} B M n :=
    (((extFunctor.{w} n).mapIso e.op).app M).addCommGroupIsoToAddEquiv.symm.toEquiv
  exact E.subsingleton

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientExt.CoefficientExtIso
