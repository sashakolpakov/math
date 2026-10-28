import Mathlib

/-! # Sheaf Coefficients -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafCoefficients

noncomputable section

/-!
# Changing the coefficients of module sheaves

Restriction by a ring automorphism is an exact equivalence on sheaves.
Its effect on scalar multiples is the inverse automorphism, as required
when constructing semilinear operators on Ext cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

section Equivalence

variable {C A D : Type*} [Category C] [Category A] [Category D]
  (J : GrothendieckTopology C) (e : A ≌ D)

instance compose_essSurj : (sheafCompose J e.functor).EssSurj where
  mem_essImage P := ⟨(sheafCompose J e.inverse).obj P,
    ⟨ObjectProperty.isoMk _ ((e.congrRight).counitIso.app P.obj)⟩⟩

instance compose_equivalence : (sheafCompose J e.functor).IsEquivalence where

end Equivalence

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R : Type w} [CommRing R] (e : R ≃+* R)

def changeCoefficients : Sheaf J (ModuleCat.{max u v w} R) ⥤
    Sheaf J (ModuleCat.{max u v w} R) :=
  sheafCompose J (ModuleCat.restrictScalars e.toRingHom)

instance changeCoefficients_equivalence : (changeCoefficients J e).IsEquivalence :=
  compose_equivalence J (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e)

instance changeCoefficients_additive : (changeCoefficients J e).Additive where
  map_add := by intros; rfl

instance changeCoefficients_preservesFiniteLimits :
    PreservesFiniteLimits (changeCoefficients J e) := by infer_instance

instance changeCoefficients_preservesFiniteColimits :
    PreservesFiniteColimits (changeCoefficients J e) := by infer_instance

theorem changeCoefficients_map_smul {P Q : Sheaf J (ModuleCat.{max u v w} R)}
    (a : P ⟶ Q) (r : R) :
    (changeCoefficients J e).map (r • a) = e.symm r • (changeCoefficients J e).map a := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change r • a.hom.app U x = e (e.symm r) • a.hom.app U x
  rw [e.apply_symm_apply]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafCoefficients
