import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Ideal.Maps

/-! # Ideal Quotient Eq -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientEq.IdealQuotientRestriction

noncomputable section

/-! Coefficient-ideal quotients commute naturally with restriction of scalars
when the ideal on the larger ring is the extended ideal. -/

open _root_.CategoryTheory

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

local notation "G" => ModuleCat.restrictScalars (algebraMap R S)
local notation "J" => I.map (algebraMap R S)
local instance restrictedModule (M : ModuleCat.{w} S) : Module R M := Module.compHom M (algebraMap R S)
local instance tower (M : ModuleCat.{w} S) : IsScalarTower R S M where
  smul_assoc r s m := by
    rw [Algebra.smul_def]
    exact mul_smul _ _ _

theorem submodule_eq (M : ModuleCat.{w} S) :
    (I • ⊤ : Submodule R M) = (J • (⊤ : Submodule S M)).restrictScalars R := by
  rw [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

def component (M : ModuleCat.{w} S) :
    (IntegralComparison.Module.IdealQuotient.functor R I).obj ((G).obj M) ≅
      (G).obj ((IntegralComparison.Module.IdealQuotient.functor S J).obj M) :=
  ((Submodule.quotEquivOfEq _ _ (submodule_eq R S I M)).trans
    (Submodule.Quotient.restrictScalarsEquiv R (J • (⊤ : Submodule S M)))).toModuleIso

theorem component_mk (M : ModuleCat.{w} S) (x : M) :
    (component R S I M).hom (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

def iso : G ⋙ IntegralComparison.Module.IdealQuotient.functor R I ≅
    IntegralComparison.Module.IdealQuotient.functor S J ⋙ G :=
  NatIso.ofComponents (component R S I) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
    rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientEq.IdealQuotientRestriction
