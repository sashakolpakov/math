import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Total
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge

/-! # Coefficient Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientEdge

noncomputable section

/-! The genuine coefficient augmentation into the mixed Hom total.
Its components are exactly coefficient postcomposition followed by the
zeroth-row inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (P : ChainComplex C ℕ)
  (K : CochainComplex C ℕ) {Y : C} (ι : (CochainComplex.single₀ C).obj Y ⟶ K)

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun I => (ModuleCat.hasColimitsOfSize.{z, t, 0, 0} R).has_colimits_of_shape (Discrete I)

def rowMap : Acyclic.ChainCohomology.complex R Y P ⟶
    (Bicomplex.bicomplex R P K).X 0 :=
  Acyclic.ChainCoefficientNaturality.complexMap R (ι.f 0) P

theorem horizontal (a a' : ℕ) (_ : (ComplexShape.up ℕ).Rel a a') :
    (rowMap R P K ι).f a ≫ ((Bicomplex.bicomplex R P K).X 0).d a a' =
      (Acyclic.ChainCohomology.complex R Y P).d a a' ≫ (rowMap R P K ι).f a' :=
  (rowMap R P K ι).comm a a'

theorem closed : rowMap R P K ι ≫ (Bicomplex.bicomplex R P K).d 0 1 = 0 := by
  change (Bicomplex.functor R P).map (ι.f 0) ≫
    (Bicomplex.functor R P).map (K.d 0 1) = 0
  exact ((Bicomplex.functor R P).map_comp _ _).symm.trans
    ((congrArg (Bicomplex.functor R P).map
      (Augmented.ResolutionCycles.augmentation_condition K ι)).trans
        ((Bicomplex.functor R P).map_zero _ _))

theorem vertical (a : ℕ) : (rowMap R P K ι).f a ≫
    ((Bicomplex.bicomplex R P K).d 0 1).f a = 0 :=
  congrArg (fun f => f.f a) (closed R P K ι)

def edge : Acyclic.ChainCohomology.complex R Y P ⟶ Total.total R P K :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge (Bicomplex.bicomplex R P K))
    (Acyclic.ChainCohomology.complex R Y P)
    (fun a => (rowMap R P K ι).f a) (horizontal R P K ι) (vertical R P K ι)

theorem edge_component (a : ℕ) : (edge R P K ι).f a =
    ModuleCat.ofHom ((Abelian.Ext.mk₀ (ι.f 0)).postcompOfLinear R (P.X a) (Nat.add_zero 0)) ≫
      (Bicomplex.bicomplex R P K).ιTotal (.up ℕ) 0 a a (Nat.zero_add a) :=
  AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge_f _ _ _ _ _ a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientEdge
