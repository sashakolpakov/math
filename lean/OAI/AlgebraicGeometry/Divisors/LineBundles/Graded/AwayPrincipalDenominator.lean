import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs

/-! # Away Principal Denominator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayPrincipalDenominator.BundleCycles

noncomputable section

/-! A single degree-zero localization element gives the corresponding
single scalar denominator on every homogeneous affine chart. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (r : A) (hr : r ∈ 𝒜 0)

include hr in
theorem gradedPowersDegreeZero (d : Submonoid.powers r) : d.val ∈ 𝒜 0 := by
  obtain ⟨n, hn⟩ := d.property
  rw [← hn]
  exact (show r ^ n ∈ 𝒜 (n • 0) from SetLike.pow_mem_graded n hr)

theorem gradedAwayDenominators_powers (s : A) :
    AwayIs.BundleCycles.gradedAwayDenominators 𝒜 (Submonoid.powers r) (gradedPowersDegreeZero 𝒜 r hr) s =
      Submonoid.powers (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩) := by
  let d₀ : Submonoid.powers r := ⟨r, ⟨1, pow_one r⟩⟩
  let φ := AwayIs.BundleCycles.gradedAwayDenominatorHom 𝒜 (Submonoid.powers r) (gradedPowersDegreeZero 𝒜 r hr) s
  have hφ : φ d₀ = fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩ := rfl
  ext a
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨n, hn⟩ := d.property
    have hd : d₀ ^ n = d := Subtype.ext hn
    refine ⟨n, ?_⟩
    change (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩) ^ n = φ d
    rw [← hφ, ← map_pow, hd]
  · rintro ⟨n, rfl⟩
    refine ⟨d₀ ^ n, ?_⟩
    change φ (d₀ ^ n) = (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩) ^ n
    rw [map_pow, hφ]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayPrincipalDenominator.BundleCycles
