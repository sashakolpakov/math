import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Surjective Local Ring Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalRingMap.Constructions

noncomputable section

/-! A surjective algebra map induces a surjection of the actual local
rings at a prime and its inverse-image prime. -/

universe u v
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (q : PrimeSpectrum S)

def localMap : Localization.AtPrime (q.asIdeal.comap (algebraMap R S)) →+*
    Localization.AtPrime q.asIdeal :=
  Localization.localRingHom _ _ (algebraMap R S) rfl

theorem primeCompl_map (hs : Function.Surjective (algebraMap R S)) :
    (q.asIdeal.comap (algebraMap R S)).primeCompl.map (algebraMap R S) = q.asIdeal.primeCompl := by
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact hr
  · intro hx
    obtain ⟨r, rfl⟩ := hs s
    exact ⟨r, hx, rfl⟩

theorem localMap_surjective (hs : Function.Surjective (algebraMap R S)) :
    Function.Surjective (localMap R S q) := by
  intro z
  obtain ⟨x, t, rfl⟩ := IsLocalization.exists_mk'_eq q.asIdeal.primeCompl z
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, hb⟩ := hs t.val
  let b' : (q.asIdeal.comap (algebraMap R S)).primeCompl := ⟨b, by
    change algebraMap R S b ∉ q.asIdeal
    rw [hb]
    exact t.property⟩
  refine ⟨IsLocalization.mk' _ a b', ?_⟩
  rw [localMap, Localization.localRingHom_mk']
  congr 1
  exact Subtype.ext hb

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalRingMap.Constructions
