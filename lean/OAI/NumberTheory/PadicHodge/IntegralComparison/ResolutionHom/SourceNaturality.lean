import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge

/-! # Source Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.SourceNaturality

noncomputable section

/-! Source augmentation in the genuine mixed Hom total commutes with
all coefficient cochain maps, without an injectivity premise. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C]
  (P : ChainComplex C ℕ) {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)
  {K L : CochainComplex C ℕ} (g : K ⟶ L)

local instance coproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun T => (ModuleCat.hasColimitsOfSize.{z,t,0,0} R).has_colimits_of_shape (Discrete T)

def sectionsMap : Total.sections R (Z := Z) K ⟶ Total.sections R (Z := Z) L :=
  ((Ext.ModuleFunctor.functor R Z 0).mapHomologicalComplex (.up ℕ)).map g

def totalMap := HomologicalComplex₂.total.map (Bicomplex.map R P g) (.up ℕ)

theorem component (q : ℕ) : Total.component R P ε K q ≫
    ((Bicomplex.map R P g).f q).f 0 =
      (sectionsMap R (Z := Z) g).f q ≫ Total.component R P ε L q :=
  Ext.CoefficientNaturality.naturality R (g.f q) 0 (ε.f 0).op

theorem square : Total.edge R P ε K ≫ totalMap R P g =
    sectionsMap R (Z := Z) g ≫ Total.edge R P ε L :=
  BicomplexHorizontalEdge.naturality _ _
    (Total.component R P ε K) (Total.vertical R P ε K)
    (Total.horizontal R P ε K) _ _
    (Total.component R P ε L) (Total.vertical R P ε L)
    (Total.horizontal R P ε L)
    (Bicomplex.map R P g) (sectionsMap R (Z := Z) g)
    (component R P ε g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.SourceNaturality
