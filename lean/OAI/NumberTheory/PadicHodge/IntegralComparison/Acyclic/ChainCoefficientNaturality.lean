import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCohomology

/-! # Chain Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCoefficientNaturality

noncomputable section

/-! The original chain-resolution Ext comparison is natural under actual
coefficient morphisms, in particular the canonical structure-sheaf isomorphisms. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {Y Y' : C} (g : Y ⟶ Y')
  (P : ChainComplex C ℕ)

def complexMap : ChainCohomology.complex R Y P ⟶
    ChainCohomology.complex R Y' P :=
  IntegralComparison.Ext.CoefficientNaturality.complexMap R g P.op

theorem complexMap_f (a : ℕ) : (complexMap R g P).f a =
    ModuleCat.ofHom ((Ext.mk₀ g).postcompOfLinear R (P.X a) (Nat.add_zero 0)) := rfl

variable {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε]
  (hP : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y (q + 1)))
  (hP' : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y' (q + 1)))

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (complexMap R g P) i ≫
    (ChainCohomology.homologyIso R Y' P ε hP' i).hom =
      (ChainCohomology.homologyIso R Y P ε hP i).hom ≫
        ModuleCat.ofHom ((Ext.mk₀ g).postcompOfLinear R Z (Nat.add_zero i)) := by
  let ι := ChainResolutionOpposite.augmentation P ε
  let : QuasiIso ι := ChainResolutionOpposite.augmentation_quasiIso P ε
  exact Resolution.CoefficientNaturality.homology R g P.op ι hP hP' i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCoefficientNaturality
