import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtExactFunctorComposition

/-! # Ext Cohomology Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtCohomologyTransport

noncomputable section

/-! Ext cohomology transport along an exact functor with a specified map of source objects. The construction satisfies explicit composition and natural-transformation laws. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
universe u v u' v' u'' v'' w w' w''

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E]

def extCohomologyTransport
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {C₀ : C} {D₀ : D} (u₀ : D₀ ⟶ F.obj C₀) (M : C) (n : ℕ) :
    Ext C₀ M n →+ Ext D₀ (F.obj M) n :=
  ((Ext.mk₀ u₀).precomp (F.obj M) (zero_add n)).comp (F.mapExtAddHom C₀ M n)

theorem extCohomologyTransport_naturality [EnoughInjectives C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⟶ G) {C₀ : C} {D₀ : D} (uF : D₀ ⟶ F.obj C₀) (uG : D₀ ⟶ G.obj C₀)
    (hu : uF ≫ a.app C₀ = uG) (M : C) (n : ℕ) (x : Ext C₀ M n) :
    (extCohomologyTransport F uF M n x).comp (Ext.mk₀ (a.app M)) (add_zero n) =
      extCohomologyTransport G uG M n x := by
  change ((Ext.mk₀ uF).comp (x.mapExactFunctor F) (zero_add n)).comp
      (Ext.mk₀ (a.app M)) (add_zero n) =
    (Ext.mk₀ uG).comp (x.mapExactFunctor G) (zero_add n)
  rw [Ext.comp_assoc_of_third_deg_zero,
    ← ExtExactFunctorNaturality.ext_mapExactFunctor_naturality F G a C₀ M n x,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hu]

theorem extCohomologyTransport_comp [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {C₀ : C} {D₀ : D} {E₀ : E} (uF : D₀ ⟶ F.obj C₀) (uG : E₀ ⟶ G.obj D₀)
    (M : C) (n : ℕ) (x : Ext C₀ M n) :
    extCohomologyTransport G uG (F.obj M) n (extCohomologyTransport F uF M n x) =
      extCohomologyTransport (F ⋙ G) (uG ≫ G.map uF) M n x := by
  change (Ext.mk₀ uG).comp
      (((Ext.mk₀ uF).comp (x.mapExactFunctor F) (zero_add n)).mapExactFunctor G) (zero_add n) =
    (Ext.mk₀ (uG ≫ G.map uF)).comp (x.mapExactFunctor (F ⋙ G)) (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ExtExactFunctorComposition.ext_mapExactFunctor_comp,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

theorem extCohomologyTransport_id [EnoughInjectives C]
    (C₀ M : C) (n : ℕ) (x : Ext C₀ M n) :
    extCohomologyTransport (𝟭 C) (𝟙 C₀) M n x = x := by
  change (Ext.mk₀ (𝟙 C₀)).comp (x.mapExactFunctor (𝟭 C)) (zero_add n) = x
  rw [ExtExactFunctorComposition.ext_mapExactFunctor_id, Ext.mk₀_id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtCohomologyTransport
