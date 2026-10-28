import Mathlib

/-! # Semilinear Ext -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearExt

noncomputable section

/-!
# Semilinear maps on Ext induced by exact functors

The scalar action on Ext is composition with a scalar multiple of the
identity. Thus an exact additive functor that changes scalars by a ring
homomorphism induces a semilinear map on all Ext groups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w w'

variable {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [Linear R C] [Linear S D] [HasExt.{w} C] [HasExt.{w'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem mapExactFunctor_smul
    (h : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y))
    {X Y : C} {n : ℕ} (r : R) (x : Ext.{w} X Y n) :
    (r • x).mapExactFunctor F = σ r • x.mapExactFunctor F := by
  rw [Ext.smul_eq_comp_mk₀, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, h]
  exact (Ext.smul_eq_comp_mk₀ (x.mapExactFunctor F) (σ r)).symm

def mapExt (h : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y))
    (X Y : C) (n : ℕ) : Ext.{w} X Y n →ₛₗ[σ] Ext.{w'} (F.obj X) (F.obj Y) n where
  __ := F.mapExtAddHom X Y n
  map_smul' r x := mapExactFunctor_smul σ F h r x

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearExt
