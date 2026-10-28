import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift

/-! # Ext Source -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtSource.ExtSourceSections

noncomputable section

/-! # Changing the source of the original Ext section functor -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (u : X' ⟶ X)

def transformation (n : ℕ) : NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X n ⟶ NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X' n where
  app Z := ModuleCat.ofHom ((Ext.mk₀ u).precompOfLinear R Z (zero_add n))
  naturality {Y Z} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change Ext.{z} X Y n at α
    change (Ext.mk₀ u).comp (α.comp (Ext.mk₀ f) (add_zero n)) (zero_add n) =
      ((Ext.mk₀ u).comp α (zero_add n)).comp (Ext.mk₀ f) (add_zero n)
    exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

def complexMap (K : CochainComplex C ℕ) :
    ((NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X' 0).mapHomologicalComplex (.up ℕ)).obj K :=
  (NatTrans.mapHomologicalComplex (transformation R u 0) (.up ℕ)).app K

omit [Linear R C] in
theorem connecting {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) (α : Ext.{z} X S.X₃ n) :
    NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.connecting X' hS n ((Ext.mk₀ u).precomp S.X₃ (zero_add n) α) =
      (Ext.mk₀ u).precomp S.X₁ (zero_add (n + 1)) (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.connecting X hS n α) := by
  change ((Ext.mk₀ u).comp α (zero_add n)).comp hS.extClass rfl =
    (Ext.mk₀ u).comp (α.comp hS.extClass rfl) (zero_add (n + 1))
  exact Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtSource.ExtSourceSections
