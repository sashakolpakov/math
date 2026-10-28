import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveModuleDimension
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Surjective Module Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveModuleSupport.Constructions

noncomputable section

/-! Actual module supports and isolated ideal intersections are
preserved under surjective local change of scalars. -/

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [Module.Finite R M] (hs : Function.Surjective (algebraMap R S))

include hs

theorem comap_mem_support_iff (q : PrimeSpectrum S) :
    PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M ↔ q ∈ Module.support S M := by
  let : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite]
  change Module.annihilator R M ≤ q.asIdeal.comap (algebraMap R S) ↔ Module.annihilator S M ≤ q.asIdeal
  rw [← Module.comap_annihilator (R := S) (R₀ := R)]
  exact Ideal.comap_le_comap_iff_of_surjective (algebraMap R S) hs _ _

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

theorem isolated_ideal_intersection (I : Ideal R)
    (hi : PrimeSpectrum.zeroLocus (I : Set R) ∩ Module.support R M ⊆ {IsLocalRing.closedPoint R}) :
    PrimeSpectrum.zeroLocus (I.map (algebraMap R S) : Set S) ∩ Module.support S M ⊆
      {IsLocalRing.closedPoint S} := by
  intro q hq
  have hI : I ≤ q.asIdeal.comap (algebraMap R S) := Ideal.map_le_iff_le_comap.mp hq.1
  have hM : PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M :=
    (comap_mem_support_iff R S M hs q).mpr hq.2
  have he := Set.mem_singleton_iff.mp (hi ⟨hI, hM⟩)
  apply Set.mem_singleton_iff.mpr
  apply PrimeSpectrum.comap_injective_of_surjective (algebraMap R S) hs
  exact he.trans (IsLocalRing.comap_closedPoint (algebraMap R S)).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveModuleSupport.Constructions
