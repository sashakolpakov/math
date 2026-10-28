import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne

/-! # Adjunction Ext Coefficient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdjunctionExtCoefficient

noncomputable section

/-! The direct-image coefficient morphism and the counit combine to
the original adjoint coefficient map inside actual Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w w' u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

theorem adjunctionExtMap_coefficient {P F : C} {G : D} (a : F ⟶ R.obj G)
    (n : ℕ) (x : Ext P F n) :
    ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne.Construction.adjunctionExtMap adj P G n
        (x.comp (Ext.mk₀ a) (add_zero n)) =
      (x.mapExactFunctor L).comp (Ext.mk₀ ((adj.homEquiv F G).symm a)) (add_zero n) := by
  change ((x.comp (Ext.mk₀ a) (add_zero n)).mapExactFunctor L).comp
      (Ext.mk₀ (adj.counit.app G)) (add_zero n) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdjunctionExtCoefficient
