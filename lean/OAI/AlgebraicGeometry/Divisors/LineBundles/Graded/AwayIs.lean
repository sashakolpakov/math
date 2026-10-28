import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ZeroUnits
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.LocalizationNumerator
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase

/-! # Away Is -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs.BundleCycles

noncomputable section

section

/-! The genuine degree-zero denominators on each homogeneous affine chart
become units after the corresponding coefficient localization. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (D : Submonoid A) (hD : ∀ d : D, d.val ∈ 𝒜 0)

def gradedZeroDenominatorHom : D →* 𝒜 0 where
  toFun d := ⟨d.val, hD d⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def gradedAwayDenominatorHom (s : A) : D →* Away 𝒜 s :=
  (fromZeroRingHom 𝒜 (Submonoid.powers s)).toMonoidHom.comp (gradedZeroDenominatorHom 𝒜 D hD)

def gradedAwayDenominators (s : A) : Submonoid (Away 𝒜 s) :=
  MonoidHom.mrange (gradedAwayDenominatorHom 𝒜 D hD s)

theorem gradedAwayDenominatorHom_apply (s : A) (d : D) :
    gradedAwayDenominatorHom 𝒜 D hD s d = fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨d.val, hD d⟩ := rfl

variable {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ℕ → τ) [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hlocal in
theorem gradedAwayDenominator_image_isUnit (s : A) (d : D) :
    IsUnit (Away.map f s (gradedAwayDenominatorHom 𝒜 D hD s d)) := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  rw [gradedAwayDenominatorHom_apply, Projective.MapBase.BundleCycles.gradedAwayMap_fromZero]
  have hu : IsUnit (f.gradedZeroRingHom ⟨d.val, hD d⟩) :=
    ZeroUnits.BundleCycles.gradedZero_isUnit ℬ _ (IsLocalization.map_units B d)
  exact hu.map (fromZeroRingHom ℬ (Submonoid.powers (f s)))

end

section

/-! Homogeneous affine-chart fractions admit common denominators from
the actual degree-zero coefficient localization. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedFromZero_val (s : A) (c : 𝒜 0) :
    (fromZeroRingHom 𝒜 (Submonoid.powers s) c).val = Localization.mk c.val 1 := rfl

theorem gradedAway_mk_mul_degreeZero {s : A} {k : ℕ} (hs : s ∈ 𝒜 k)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • k)) (c : 𝒜 0) :
    Away.mk 𝒜 hs n a ha * fromZeroRingHom 𝒜 (Submonoid.powers s) c =
      Away.mk 𝒜 hs n (a * c.val)
        (show a * c.val ∈ 𝒜 (n • k + 0) from SetLike.mul_mem_graded ha c.property) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, Away.val_mk, gradedFromZero_val, Localization.mk_mul, Away.val_mk]
  simp only [mul_one]

variable {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ℕ → τ) [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (D : Submonoid A) (hD : ∀ d : D, d.val ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hlocal in
theorem gradedAway_localized_fraction {s : A} {k : ℕ} (hs : s ∈ 𝒜 k)
    (z : Away ℬ (f s)) : ∃ x : Away 𝒜 s, ∃ d : D,
      z * Away.map f s (gradedAwayDenominatorHom 𝒜 D hD s d) = Away.map f s x := by
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a, ha, d, hd⟩ := LocalizationNumerator.BundleCycles.gradedLocalization_homogeneousNumerator f D hD hlocal (n • k) b hb
  refine ⟨Away.mk 𝒜 hs n a ha, d, ?_⟩
  rw [gradedAwayDenominatorHom_apply, Projective.MapBase.BundleCycles.gradedAwayMap_fromZero]
  refine (gradedAway_mk_mul_degreeZero ℬ (f.map_mem hs) n b hb
    (f.gradedZeroRingHom ⟨d.val, hD d⟩)).trans ?_
  rw [Away.map_mk]
  congr 1

end

section

/-! Equality on a localized homogeneous affine chart is detected after
multiplication by an actual degree-zero denominator. -/

open _root_.HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (D : Submonoid A) (hD : ∀ d : D, d.val ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hlocal in
theorem gradedAway_clear_equality {s : A} {k : ℕ} (hs : s ∈ 𝒜 k)
    (x y : Away 𝒜 s) (hxy : Away.map f s x = Away.map f s y) :
    ∃ d : D, gradedAwayDenominatorHom 𝒜 D hD s d * x =
      gradedAwayDenominatorHom 𝒜 D hD s d * y := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hs y
  rw [Away.map_mk, Away.map_mk] at hxy
  have he := congrArg HomogeneousLocalization.val hxy
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at he
  obtain ⟨⟨t, ht⟩, he⟩ := he
  obtain ⟨l, rfl⟩ := ht
  have hcoeff : f (s ^ l * (s ^ m * a)) = f (s ^ l * (s ^ n * b)) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow]
    exact he
  obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := D) hcoeff
  refine ⟨d, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_mul, gradedAwayDenominatorHom_apply, gradedFromZero_val,
    Away.val_mk, Away.val_mk, Localization.mk_mul, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨s ^ l, ⟨l, rfl⟩⟩, ?_⟩
  change s ^ l * ((1 * s ^ m) * (d.val * a)) = s ^ l * ((1 * s ^ n) * (d.val * b))
  calc
    _ = d.val * (s ^ l * (s ^ m * a)) := by ring
    _ = d.val * (s ^ l * (s ^ n * b)) := hd
    _ = _ := by ring

end

/-! Localizing a graded ring at degree-zero elements localizes each
actual homogeneous affine chart at the corresponding scalar denominators. -/

open _root_.HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (D : Submonoid A) (hD : ∀ d : D, d.val ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hlocal in
theorem gradedAway_isLocalization {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) :
    letI := (Away.map f s).toAlgebra
    IsLocalization (gradedAwayDenominators 𝒜 D hD s) (Away ℬ (f s)) := by
  let := (Away.map f s).toAlgebra
  apply (isLocalization_iff (gradedAwayDenominators 𝒜 D hD s) (Away ℬ (f s))).mpr
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨d, hd⟩
    obtain ⟨a, rfl⟩ := hd
    exact gradedAwayDenominator_image_isUnit 𝒜 D hD ℬ f hlocal s a
  · intro z
    obtain ⟨x, d, hd⟩ := gradedAway_localized_fraction 𝒜 ℬ f D hD hlocal hs z
    exact ⟨⟨x, ⟨gradedAwayDenominatorHom 𝒜 D hD s d, ⟨d, rfl⟩⟩⟩, hd⟩
  · intro x y hxy
    obtain ⟨d, hd⟩ := gradedAway_clear_equality 𝒜 ℬ f D hD hlocal hs x y hxy
    exact ⟨⟨gradedAwayDenominatorHom 𝒜 D hD s d, ⟨d, rfl⟩⟩, hd⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs.BundleCycles
