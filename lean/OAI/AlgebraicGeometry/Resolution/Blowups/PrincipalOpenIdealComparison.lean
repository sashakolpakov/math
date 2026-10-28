import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! # Principal Open Ideal Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalOpenIdealComparison.Construction

noncomputable section

/-! Combining ideal comparisons on principal opens without finiteness assumptions. -/

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ideal_map_le_of_principal_localization (J K : Ideal R) (s : R)
    (φ : R →+* S) (hs : IsUnit (φ s))
    (h : J.map (algebraMap R (Localization.Away s)) ≤
      K.map (algebraMap R (Localization.Away s))) : J.map φ ≤ K.map φ := by
  let ψ : Localization.Away s →+* S := IsLocalization.Away.lift s hs
  have he : ψ.comp (algebraMap R (Localization.Away s)) = φ :=
    IsLocalization.Away.lift_comp s hs
  have hm := Ideal.map_mono (f := ψ) h
  rw [Ideal.map_map, Ideal.map_map, he] at hm
  exact hm

/-- Opposite ideal comparisons on two neighborhoods give equality on their
intersection, which is still a principal open containing the chosen prime. -/
theorem exists_common_principal_ideal_equality (J K q : Ideal R) [q.IsPrime]
    (hJK : ∃ s : R, s ∉ q ∧ J.map (algebraMap R (Localization.Away s)) ≤
      K.map (algebraMap R (Localization.Away s)))
    (hKJ : ∃ s : R, s ∉ q ∧ K.map (algebraMap R (Localization.Away s)) ≤
      J.map (algebraMap R (Localization.Away s))) :
    ∃ s : R, s ∉ q ∧ J.map (algebraMap R (Localization.Away s)) =
      K.map (algebraMap R (Localization.Away s)) := by
  obtain ⟨u, hu, hJK⟩ := hJK
  obtain ⟨v, hv, hKJ⟩ := hKJ
  let φ := algebraMap R (Localization.Away (u * v))
  have hunit : IsUnit (φ u * φ v) := by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (u * v)
  have hunitu := isUnit_of_mul_isUnit_left hunit
  have hunitv := isUnit_of_mul_isUnit_right hunit
  refine ⟨u * v, q.primeCompl.mul_mem hu hv, le_antisymm ?_ ?_⟩
  · exact ideal_map_le_of_principal_localization J K u φ hunitu hJK
  · exact ideal_map_le_of_principal_localization K J v φ hunitv hKJ

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalOpenIdealComparison.Construction
