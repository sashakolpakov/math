import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Maximal

/-! # Nontrivial Basic Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NontrivialBasicLocalization

noncomputable section

/-! A basic-open cover of a nonzero ring contains a nonzero localization. -/

universe u

theorem exists_nontrivial_away_of_span_top (R : Type u) [CommRing R] [Nontrivial R]
    (s : Set R) (hs : Ideal.span s = ⊤) : ∃ r ∈ s, Nontrivial (Localization.Away r) := by
  classical
  obtain ⟨p, hp⟩ := Ideal.exists_maximal R
  have he : ∃ r ∈ s, r ∉ p := by
    by_contra! h
    have ht : (⊤ : Ideal R) ≤ p := by
      rw [← hs]
      exact Ideal.span_le.mpr h
    exact hp.ne_top (top_le_iff.mp ht)
  obtain ⟨r, hr, hrp⟩ := he
  refine ⟨r, hr, (IsLocalization.toLocalizationMap (Submonoid.powers r) (Localization.Away r)).nontrivial ?_⟩
  rintro ⟨n, hn⟩
  have hpow : r ^ n ∈ p := Eq.mpr (congrArg (fun a : R => a ∈ p) hn) p.zero_mem
  exact hrp (hp.isPrime.mem_of_pow_mem n hpow)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NontrivialBasicLocalization
