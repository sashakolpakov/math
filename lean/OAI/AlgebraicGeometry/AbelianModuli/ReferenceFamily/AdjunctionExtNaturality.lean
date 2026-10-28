import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne

/-! # Adjunction Ext Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdjunctionExtNaturality

noncomputable section

/-! The proved Ext map of an exact adjunction is natural in its
coefficient object. This controls coefficient actions on native sheaf
cohomology after pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

theorem adjunctionExtMap_natural (P : C) {F G : D} (f : F ⟶ G) (n : ℕ)
    (x : Ext P (R.obj F) n) :
    ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne.Construction.adjunctionExtMap adj P G n (x.comp (Ext.mk₀ (R.map f)) (add_zero n)) =
      (ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne.Construction.adjunctionExtMap adj P F n x).comp (Ext.mk₀ f) (add_zero n) := by
  change ((x.comp (Ext.mk₀ (R.map f)) (add_zero n)).mapExactFunctor L).comp
      (Ext.mk₀ (adj.counit.app G)) (add_zero n) =
    ((x.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app F)) (add_zero n)).comp (Ext.mk₀ f) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg (fun q => (x.mapExactFunctor L).comp (Ext.mk₀ q) (add_zero n)) (adj.counit.naturality f)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdjunctionExtNaturality
