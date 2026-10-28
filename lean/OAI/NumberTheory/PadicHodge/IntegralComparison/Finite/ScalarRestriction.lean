import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.RingHom.Finite

/-! # Scalar Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ScalarRestriction

noncomputable section

/-!
# IntegralComparison: finite scalar restriction preserves finite generation of actual module objects
-/

open _root_.CategoryTheory

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : f.Finite) (M : ModuleCat.{w} S) [Module.Finite S M]

include hf in
theorem finite : Module.Finite R ((ModuleCat.restrictScalars f).obj M) := by
  let : Algebra R S := f.toAlgebra
  let mR : Module R M := Module.compHom M f
  let hTower : IsScalarTower R S M := ⟨fun r s m => by
    change (f r * s) • m = f r • s • m
    exact mul_smul (f r) s m⟩
  let : Module.Finite R S := hf
  exact @Module.Finite.trans R S M inferInstance inferInstance inferInstance inferInstance
    mR M.isModule hTower hf inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ScalarRestriction
