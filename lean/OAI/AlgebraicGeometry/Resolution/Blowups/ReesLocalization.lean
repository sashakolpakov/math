import OAI.AlgebraicGeometry.Resolution.Blowups.ReesMap

/-! # Rees Localization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReesLocalization.Construction

noncomputable section

/-! Localization of the Rees algebra for the affine gluing in Blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) (s : R) [IsLocalization.Away s S]

/-- Every element of the extended Rees algebra has a common denominator
which is a power of the localized base element. -/
theorem reesRingMap_clears_denominators
    (p : reesAlgebra (I.map (algebraMap R S))) :
    ∃ (n : ℕ) (q : reesAlgebra I),
      p * ReesMap.Construction.reesRingMap I (algebraMap R S) (algebraMap R (reesAlgebra I) s) ^ n =
        ReesMap.Construction.reesRingMap I (algebraMap R S) q := by
  let F := ReesMap.Construction.reesRingMap I (algebraMap R S)
  let x := algebraMap R (reesAlgebra I) s
  change ∃ (n : ℕ) (q : reesAlgebra I), p * F x ^ n = F q
  have hp : p ∈ Algebra.adjoin S
      (Set.range (fun a : I => ReesMap.Construction.reesRingMap I (algebraMap R S) (Blowup.Charts.Construction.reesGenerator I a))) := by
    rw [ReesMap.Construction.reesMappedGenerators_adjoin]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨0, Blowup.Charts.Construction.reesGenerator I a, by simp [F]⟩
  | algebraMap c =>
    obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (S := S) s c
    refine ⟨n, algebraMap R (reesAlgebra I) r, ?_⟩
    dsimp only [F, x]
    simpa only [ReesMap.Construction.reesRingMap_constants, map_mul, map_pow] using
      congrArg (algebraMap S (reesAlgebra (I.map (algebraMap R S)))) hr
  | add p q _ _ hp hq =>
    obtain ⟨n, p₀, hp₀⟩ := hp
    obtain ⟨m, q₀, hq₀⟩ := hq
    refine ⟨n + m, p₀ * x ^ m + q₀ * x ^ n, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hp₀, ← hq₀, pow_add]
    ring
  | mul p q _ _ hp hq =>
    obtain ⟨n, p₀, hp₀⟩ := hp
    obtain ⟨m, q₀, hq₀⟩ := hq
    refine ⟨n + m, p₀ * q₀, ?_⟩
    rw [map_mul, ← hp₀, ← hq₀, pow_add]
    ring

/-- For a domain, localizing the base at a nonzero element localizes the
actual Rees algebra at the corresponding degree-zero element. -/
theorem reesRingMap_isLocalization [IsDomain R] (hs : s ≠ 0) :
    letI : Algebra (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) :=
      (ReesMap.Construction.reesRingMap I (algebraMap R S)).toAlgebra
    IsLocalization.Away (algebraMap R (reesAlgebra I) s)
      (reesAlgebra (I.map (algebraMap R S))) := by
  let : Algebra (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) :=
    (ReesMap.Construction.reesRingMap I (algebraMap R S)).toAlgebra
  refine IsLocalization.Away.mk (algebraMap R (reesAlgebra I) s) ?_ ?_ ?_
  · change IsUnit (ReesMap.Construction.reesRingMap I (algebraMap R S) (algebraMap R (reesAlgebra I) s))
    rw [ReesMap.Construction.reesRingMap_constants]
    exact (IsLocalization.Away.algebraMap_isUnit (S := S) s).map
      (algebraMap S (reesAlgebra (I.map (algebraMap R S))))
  · exact reesRingMap_clears_denominators I s
  · intro p q hpq
    have hRS : Function.Injective (algebraMap R S) :=
      IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
    have h : p = q := ReesMap.Construction.reesRingMap_injective I (algebraMap R S) hRS hpq
    exact ⟨0, by simpa using h⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReesLocalization.Construction
