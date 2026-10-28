import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalRingMap
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Surjective Local Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalLength.Constructions

noncomputable section

/-! Local module length is unchanged by a surjective change of base
ring, at the actual prime and its inverse image. -/

open OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalRingMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions

set_option backward.isDefEq.respectTransparency false

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (q : PrimeSpectrum S)

local instance : Algebra (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (Localization.AtPrime q.asIdeal) := Localization.AtPrime.algebraOfLiesOver _ _

local instance : IsScalarTower R
    (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (Localization.AtPrime q.asIdeal) := inferInstance

local instance : Module (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (LocalizedModule q.asIdeal.primeCompl M) :=
  Module.compHom _ (algebraMap (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (Localization.AtPrime q.asIdeal))

local instance : IsScalarTower (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

local instance : IsScalarTower R (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (LocalizedModule q.asIdeal.primeCompl M) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change algebraMap (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (Localization.AtPrime q.asIdeal)
    (algebraMap R (Localization.AtPrime (q.asIdeal.comap (algebraMap R S))) r) • x = r • x
  rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
    (Localization.AtPrime q.asIdeal), algebraMap_smul]

theorem localLength_eq (hs : Function.Surjective (algebraMap R S)) :
    LocalizedModuleLength.Constructions.localLength R M (PrimeSpectrum.comap (algebraMap R S) q) = LocalizedModuleLength.Constructions.localLength S M q := by
  have hmap : Algebra.algebraMapSubmonoid S (q.asIdeal.comap (algebraMap R S)).primeCompl =
      q.asIdeal.primeCompl := SurjectiveLocalRingMap.Constructions.primeCompl_map R S q hs
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid S (q.asIdeal.comap (algebraMap R S)).primeCompl)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) := by
    rw [hmap]
    infer_instance
  let : IsLocalizedModule (q.asIdeal.comap (algebraMap R S)).primeCompl
      ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl M).restrictScalars R) :=
    IsLocalizedModule.restrictScalars _ _
  let e := (IsLocalizedModule.linearEquiv (q.asIdeal.comap (algebraMap R S)).primeCompl
    (LocalizedModule.mkLinearMap (q.asIdeal.comap (algebraMap R S)).primeCompl M)
    ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl M).restrictScalars R)).extendScalarsOfIsLocalization
      (q.asIdeal.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
  exact e.length_eq.trans
    (Module.length_eq_of_surjective (R := Localization.AtPrime q.asIdeal)
      (S := Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
      (M := LocalizedModule q.asIdeal.primeCompl M) (SurjectiveLocalRingMap.Constructions.localMap_surjective R S q hs))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalLength.Constructions
