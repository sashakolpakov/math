import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Ext Left -/

namespace OAI.AlgebraicGeometry.SheafCohomology.ExtLeft.Projective

noncomputable section

/-! Contravariant transport of Ext along source isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

universe u v w

def extLeftIso {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {X Y : C} (e : X ≅ Y) (Z : C) (n : ℕ) : Ext X Z n ≃+ Ext Y Z n :=
  (((extFunctor n).mapIso e.op).app Z).symm.addCommGroupIsoToAddEquiv

end

end OAI.AlgebraicGeometry.SheafCohomology.ExtLeft.Projective
