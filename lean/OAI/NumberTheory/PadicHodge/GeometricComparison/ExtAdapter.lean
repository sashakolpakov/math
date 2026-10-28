import Mathlib

/-! # Ext Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExtAdapter

noncomputable section

/-! Exact linear transport of Ext along a categorical equivalence. -/

open _root_.CategoryTheory

universe w w' v v' u u'

def extEquiv (R : Type*) [CommRing R]
    {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasExt.{w} C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D] [HasExt.{w'} D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] (A B : C) (n : ℕ) :
    Abelian.Ext A B n ≃ₗ[R] Abelian.Ext (e.functor.obj A) (e.functor.obj B) n :=
  LinearEquiv.ofBijective (e.functor.mapExtLinearMap R A B n)
    (e.functor.mapExt_bijective_of_preservesInjectiveObjects A B n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExtAdapter
