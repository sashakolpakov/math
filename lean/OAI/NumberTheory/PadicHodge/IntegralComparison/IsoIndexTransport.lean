import Mathlib.CategoryTheory.EqToHom

/-! # Iso Index Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IsoIndexTransport

/-! Reindexing a family of isomorphisms preserves a naturality square.
The proof is independent of the objects represented by the indices. -/

open _root_.CategoryTheory

universe u v w t

variable {C : Type u} [Category.{v} C] {I : Type w} {J : Type t}

def iso {A : I → C} {B : J → C} {i i' : I} {j j' : J}
    (hi : i = i') (hj : j' = j) (e : A i' ≅ B j') : A i ≅ B j :=
  eqToIso (congrArg A hi) ≪≫ e ≪≫ eqToIso (congrArg B hj)

@[reassoc]
theorem naturality {A₁ A₂ : I → C} {B₁ B₂ : J → C}
    (a : ∀ i, A₁ i ⟶ A₂ i) (b : ∀ j, B₁ j ⟶ B₂ j)
    {i i' : I} {j j' : J} (hi : i = i') (hj : j' = j)
    (e₁ : A₁ i' ≅ B₁ j') (e₂ : A₂ i' ≅ B₂ j')
    (h : a i' ≫ e₂.hom = e₁.hom ≫ b j') :
    a i ≫ (iso hi hj e₂).hom = (iso hi hj e₁).hom ≫ b j := by
  subst i'
  subst j'
  simpa only [iso, eqToIso_refl, Iso.refl_trans, Iso.trans_refl] using h

end OAI.NumberTheory.PadicHodge.IntegralComparison.IsoIndexTransport
