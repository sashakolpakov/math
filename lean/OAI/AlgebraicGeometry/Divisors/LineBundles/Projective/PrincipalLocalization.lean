import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayPrincipalDenominator
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Principal Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalLocalization.BundleCycles

noncomputable section

/-! The actual Proj map associated to localization at one degree-zero
element is an open immersion. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

theorem projectiveLocalization_injective (D : Submonoid A)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B) :
    Function.Injective (Proj.map f hf) := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  intro p q hpq
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  let p' : PrimeSpectrum B := ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
  let q' : PrimeSpectrum B := ⟨q.asHomogeneousIdeal.toIdeal, q.isPrime⟩
  have he : PrimeSpectrum.comap (algebraMap A B) p' = PrimeSpectrum.comap (algebraMap A B) q' := by
    apply PrimeSpectrum.ext
    exact congrArg (fun z : Proj 𝒜 => z.asHomogeneousIdeal.toIdeal) hpq
  exact congrArg PrimeSpectrum.asIdeal (PrimeSpectrum.localization_comap_injective B D he)

theorem gradedAway_principal_isOpenImmersion (r : A) (hr : r ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization.Away r B)
    (s : A) (k : ℕ) (hs : s ∈ 𝒜 k) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Away.map f s))) := by
  let := (Away.map f s).toAlgebra
  have h := Graded.AwayIs.BundleCycles.gradedAway_isLocalization 𝒜 ℬ f (Submonoid.powers r)
    (Graded.AwayPrincipalDenominator.BundleCycles.gradedPowersDegreeZero 𝒜 r hr) hlocal hs
  rw [Graded.AwayPrincipalDenominator.BundleCycles.gradedAwayDenominators_powers] at h
  let := h
  exact IsOpenImmersion.of_isLocalization (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩)

theorem projectivePrincipalLocalization_isOpenImmersion (r : A) (hr : r ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization.Away r B) : IsOpenImmersion (Proj.map f hf) := by
  apply IsOpenImmersion.of_openCover_source (Proj.map f hf) (Proj.mapAffineOpenCover f hf).openCover
    (projectiveLocalization_injective 𝒜 ℬ f hf (Submonoid.powers r) hlocal)
  intro t
  let n : ℕ := t.1.val
  let a : A := t.2.val
  have hn : 0 < n := t.1.property
  have ha : a ∈ 𝒜 n := t.2.property
  have he := Proj.awayι_comp_map f hf hn a ha
  change IsOpenImmersion (Proj.awayι ℬ (f a) (f.map_mem ha) hn ≫ Proj.map f hf)
  rw [he]
  let := gradedAway_principal_isOpenImmersion 𝒜 ℬ f r hr hlocal a n ha
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalLocalization.BundleCycles
