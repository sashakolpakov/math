import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import Mathlib.Algebra.Homology.TotalComplex

/-! # Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Bicomplex

noncomputable section

/-! The genuine mixed Hom bicomplex for a source chain resolution and a
coefficient cochain complex. Its entries are the original degree-zero Ext
modules, and both differentials are induced by the actual differentials. -/

open _root_.CategoryTheory

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (P : ChainComplex C ℕ)

def functor : C ⥤ CochainComplex (ModuleCat.{z} R) ℕ where
  obj Y := Acyclic.ChainCohomology.complex R Y P
  map g := Acyclic.ChainCoefficientNaturality.complexMap R g P
  map_id Y := by
    apply HomologicalComplex.Hom.ext
    funext a
    exact (IntegralComparison.Ext.ModuleFunctor.functor R (P.X a) 0).map_id Y
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext a
    exact (IntegralComparison.Ext.ModuleFunctor.functor R (P.X a) 0).map_comp f g

instance additive : (functor R P).Additive where
  map_add := by
    intros Y Y' f g
    apply HomologicalComplex.Hom.ext
    funext a
    exact (IntegralComparison.Ext.ModuleFunctor.functor R (P.X a) 0).map_add (f := f) (g := g)

def bicomplex (K : CochainComplex C ℕ) : HomologicalComplex₂ (ModuleCat.{z} R) (.up ℕ) (.up ℕ) :=
  ((functor R P).mapHomologicalComplex (.up ℕ)).obj K

theorem coefficient_differential (K : CochainComplex C ℕ) (b b' a : ℕ) :
    ((bicomplex R P K).d b b').f a =
      ModuleCat.ofHom ((Abelian.Ext.mk₀ (K.d b b')).postcompOfLinear R (P.X a) (Nat.add_zero 0)) := rfl

theorem source_differential (K : CochainComplex C ℕ) (b a a' : ℕ) :
    ((bicomplex R P K).X b).d a a' =
      (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (K.X b) 0).map (P.d a' a).op := rfl

def map {K L : CochainComplex C ℕ} (g : K ⟶ L) : bicomplex R P K ⟶ bicomplex R P L :=
  ((functor R P).mapHomologicalComplex (.up ℕ)).map g

theorem map_component {K L : CochainComplex C ℕ} (g : K ⟶ L) (b a : ℕ) :
    ((Bicomplex.map R P g).f b).f a =
      ModuleCat.ofHom ((Abelian.Ext.mk₀ (g.f b)).postcompOfLinear R (P.X a) (Nat.add_zero 0)) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Bicomplex
