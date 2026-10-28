import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! # Base Localization Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.BaseLocalizationDetection.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual coefficient localizations detect zero in any algebra -/

variable {R A : Type} [CommRing R] [CommRing A]

theorem ringElement_eq_zero_of_base_localizations (β : R →+* A)
    (Aₚ : ∀ (p : Ideal R) [p.IsMaximal], Type)
    [∀ (p : Ideal R) [p.IsMaximal], CommRing (Aₚ p)]
    (ρ : ∀ (p : Ideal R) [p.IsMaximal], A →+* Aₚ p)
    (hL : ∀ (p : Ideal R) [p.IsMaximal],
      letI := (ρ p).toAlgebra
      IsLocalization (p.primeCompl.map β) (Aₚ p))
    (x : A) (hx : ∀ (p : Ideal R) [p.IsMaximal], ρ p x = 0) : x = 0 := by
  let : Algebra R A := β.toAlgebra
  let K : Ideal R := (LinearMap.toSpanSingleton R A x).ker
  by_contra hne
  have hK : K ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ K := h ▸ Submodule.mem_top
    change (1 : R) • x = 0 at h1
    exact hne (by simpa only [one_smul] using h1)
  obtain ⟨p, hp, hKp⟩ := K.exists_le_maximal hK
  let : p.IsMaximal := hp
  let : Algebra A (Aₚ p) := (ρ p).toAlgebra
  have : IsLocalization (p.primeCompl.map β) (Aₚ p) := hL p
  obtain ⟨d, hd⟩ := (IsLocalization.map_eq_zero_iff (p.primeCompl.map β) (Aₚ p) x).mp (hx p)
  obtain ⟨r, hr, he⟩ := d.property
  apply hr
  apply hKp
  change r • x = 0
  change β r * x = 0
  exact he ▸ hd

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.BaseLocalizationDetection.BundleCycles
