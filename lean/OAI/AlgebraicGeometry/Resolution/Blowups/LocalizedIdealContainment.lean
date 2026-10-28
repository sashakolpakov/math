import Mathlib.RingTheory.Localization.Ideal

/-! # Localized Ideal Containment -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedIdealContainment.Construction

noncomputable section

/-! Descent of ideal containment from an arbitrary principal open cover. -/

variable {R : Type*} [CommRing R]

/-- Containment on a principal open cover is containment in the original
ring; the proof clears the actual localization denominators. -/
theorem ideal_le_of_localized_away_cover (I J : Ideal R) (s : Set R)
    (hs : Ideal.span s = ⊤)
    (hlocal : ∀ r ∈ s, I.map (algebraMap R (Localization.Away r)) ≤
      J.map (algebraMap R (Localization.Away r))) : I ≤ J := by
  intro x hx
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem J s hs x
  rintro ⟨r, hr⟩
  have h := hlocal r hr (Ideal.mem_map_of_mem _ hx)
  obtain ⟨m, hm, hmx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r) (Localization.Away r) J x).mp h
  obtain ⟨n, rfl⟩ := hm
  exact ⟨n, hmx⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedIdealContainment.Construction
