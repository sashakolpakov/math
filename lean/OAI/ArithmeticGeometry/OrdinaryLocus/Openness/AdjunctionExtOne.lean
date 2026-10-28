import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ExtOneExtensions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Adjunction Ext One -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne.Construction

noncomputable section

/-! An exact left adjoint gives an injection from first Ext into the corresponding source Ext group. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Abelian

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

def adjunctionExtMap (P : C) (F : D) (n : ℕ) : Ext P (R.obj F) n →+ Ext (L.obj P) F n :=
  ((Ext.mk₀ (adj.counit.app F)).postcomp (L.obj P) (add_zero n)).comp
    (L.mapExtAddHom P (R.obj F) n)

theorem adjunctionExtMap_one_injective [EnoughInjectives C] (P : C) (F : D) :
    Function.Injective (adjunctionExtMap adj P F 1) := by
  have hzero (e : Ext P (R.obj F) 1) (he : adjunctionExtMap adj P F 1 e = 0) : e = 0 := by
    obtain ⟨E, a, b, hab, hS, rfl⟩ := ExtOneExtensions.Construction.ext_one_has_extension P (R.obj F) e
    change (hS.extClass.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app F)) (add_zero 1) = 0 at he
    rw [Ext.mapExactFunctor_extClass] at he
    obtain ⟨t, ht⟩ := (ExtOneExtensions.Construction.extClass_comp_zero_iff_extends _ (hS.map_of_exact L) (adj.counit.app F)).mp he
    have ha : a ≫ adj.homEquiv E F t = 𝟙 (R.obj F) := by
      calc
        _ = adj.homEquiv (R.obj F) F (L.map a ≫ t) := (adj.homEquiv_naturality_left a t).symm
        _ = adj.homEquiv (R.obj F) F (adj.counit.app F) := congrArg (adj.homEquiv _ _) ht
        _ = 𝟙 _ := by rw [← adj.homEquiv_symm_id, Equiv.apply_symm_apply]
    have hz := (ExtOneExtensions.Construction.extClass_comp_zero_iff_extends _ hS (𝟙 (R.obj F))).mpr ⟨_, ha⟩
    rw [Ext.comp_mk₀_id] at hz
    exact hz
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  exact (map_sub (adjunctionExtMap adj P F 1) x y).trans
    ((congrArg (fun t ↦ t - adjunctionExtMap adj P F 1 y) hxy).trans (sub_self _))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne.Construction
