import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtFunctoriality

/-! # Linear Transport Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.LinearTransportComposition

noncomputable section

/-! Composition of actual linear Ext pullbacks with their prescribed coefficient identifications. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u v w

variable (R : Type*) [CommRing R]
  {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E]
  [Linear R C] [Linear R D] [Linear R E] [HasExt.{u} C] [HasExt.{v} D] [HasExt.{w} E]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Linear R]

def map {A B : C} {A' B' : D} (eA : F.obj A ≅ A') (eB : F.obj B ≅ B') (n : ℕ) :
    Ext A B n →ₗ[R] Ext A' B' n :=
  (Etale.Frobenius.extIsoCongr R eA eB n).toLinearMap.comp (F.mapExtLinearMap R A B n)

theorem apply {A B : C} {A' B' : D} (eA : F.obj A ≅ A') (eB : F.obj B ≅ B')
    {n : ℕ} (x : Ext A B n) : map R F eA eB n x =
      ((Ext.mk₀ eA.inv).comp (x.mapExactFunctor F) (Nat.zero_add n)).comp
        (Ext.mk₀ eB.hom) (Nat.add_zero n) := rfl

variable (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.Linear R]
  [EnoughInjectives C]

theorem composition {A B : C} {A' B' : D} {A'' B'' : E}
    (eA : F.obj A ≅ A') (eB : F.obj B ≅ B') (dA : G.obj A' ≅ A'') (dB : G.obj B' ≅ B'')
    {n : ℕ} (x : Ext A B n) :
    map R G dA dB n (map R F eA eB n x) =
      map R (F ⋙ G) (G.mapIso eA ≪≫ dA) (G.mapIso eB ≪≫ dB) n x := by
  simp only [apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    PeriodInvariants.ExtFunctoriality.mapExactFunctor_compFunctor]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.LinearTransportComposition
