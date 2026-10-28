import OAI.AlgebraicGeometry.CycleClass.Thom.RetractModuleLength
import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalLength

/-! # Retract Local Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RetractLocalLength.Constructions

noncomputable section

/-! Local length on an algebra retraction is preserved at the prime
and its inverse image for modules killed by the retraction kernel. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RetractModuleLength.Constructions

set_option backward.isDefEq.respectTransparency false

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (μ : A →ₐ[R] R) (M : ModuleCat.{u} A)

attribute [local instance] RetractModuleLength.Constructions.restrictedAlgebraModule

theorem localLength_eq (h : RingHom.ker μ.toRingHom ≤ Module.annihilator A M)
    (q : PrimeSpectrum R) :
    LocalizedModuleLength.Constructions.localLength A M (PrimeSpectrum.comap μ.toRingHom q) =
      LocalizedModuleLength.Constructions.localLength R ((ModuleCat.restrictScalars (algebraMap R A)).obj M) q := by
  let : Algebra A R := μ.toRingHom.toAlgebra
  let : IsScalarTower A R ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
    IsScalarTower.of_algebraMap_smul (fun a x => (RetractModuleLength.Constructions.factor_smul R A μ M h a x).symm)
  apply SurjectiveLocalLength.Constructions.localLength_eq A R
    ((ModuleCat.restrictScalars (algebraMap R A)).obj M) q
  intro r
  exact ⟨algebraMap R A r, μ.commutes r⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RetractLocalLength.Constructions
