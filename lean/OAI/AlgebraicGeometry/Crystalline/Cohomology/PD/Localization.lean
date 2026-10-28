import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.LocalizationOperations

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Localization.PDLocalization

noncomputable section

/-!
# Actual divided powers after localization

The fraction operations satisfy all divided-power axioms. The proof clears
denominators inside the original PD ideal and uses the already checked
independence of fraction representatives. The localization map preserves
the resulting divided powers over arbitrary commutative coefficient rings.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.LocalizationOperations.PDLocalizationOperations

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S] (I : Ideal R) (δ : DividedPowers I)

local notation "J" => I.map (algebraMap R S)
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.LocalizationOperations.PDLocalizationOperations.dpow R S M I δ

theorem fraction_add_same (a b : R) (s : M) :
    IsLocalization.mk' S (a + b) s = IsLocalization.mk' S a s + IsLocalization.mk' S b s := by
  rw [IsLocalization.mk'_eq_mul_mk'_one (S := S) (a + b) s,
    IsLocalization.mk'_eq_mul_mk'_one (S := S) a s,
    IsLocalization.mk'_eq_mul_mk'_one (S := S) b s, map_add, add_mul]

theorem common_denominator (z w : S) (hz : z ∈ J) (hw : w ∈ J) :
    ∃ (a b : I) (s : M), z = IsLocalization.mk' S (a : R) s ∧ w = IsLocalization.mk' S (b : R) s := by
  let a := LocalizationOperations.PDLocalizationOperations.representative R S M I z hz
  let b := LocalizationOperations.PDLocalizationOperations.representative R S M I w hw
  refine ⟨⟨(a.1 : R) * b.2, (I).mul_mem_right (b.2 : R) a.1.property⟩,
    ⟨(b.1 : R) * a.2, (I).mul_mem_right (a.2 : R) b.1.property⟩, a.2 * b.2, ?_, ?_⟩
  · exact (LocalizationOperations.PDLocalizationOperations.representative_spec R S M I z hz).trans (IsLocalization.mk'_cancel (S := S) (a.1 : R) a.2 b.2).symm
  · have hc := (IsLocalization.mk'_cancel (S := S) (b.1 : R) b.2 a.2).symm
    rw [mul_comm b.2 a.2] at hc
    exact (LocalizationOperations.PDLocalizationOperations.representative_spec R S M I w hw).trans hc

theorem fraction_formula (n : ℕ) (a : R) (ha : a ∈ I) (s : M) :
    γ n (IsLocalization.mk' S a s) = algebraMap R S (δ.dpow n a) * (IsLocalization.mk' S 1 s) ^ n := by
  rw [LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ n a ha, IsLocalization.mk'_eq_mul_mk'_one,
    ← IsLocalization.mk'_pow, one_pow]

theorem dpow_add (n : ℕ) (z w : S) (hz : z ∈ J) (hw : w ∈ J) :
    γ n (z + w) = (Finset.antidiagonal n).sum (fun q => γ q.1 z * γ q.2 w) := by
  obtain ⟨a, b, s, rfl, rfl⟩ := common_denominator R S M I z w hz hw
  rw [← fraction_add_same, fraction_formula R S M I δ n _ ((I).add_mem a.property b.property),
    δ.dpow_add a.property b.property, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [fraction_formula R S M I δ q.1 a a.property,
    fraction_formula R S M I δ q.2 b b.property, map_mul]
  have hp : (IsLocalization.mk' S 1 s) ^ q.1 * (IsLocalization.mk' S 1 s) ^ q.2 =
      (IsLocalization.mk' S 1 s) ^ n := by
    rw [← pow_add, Finset.mem_antidiagonal.mp hq]
  rw [← hp]
  ring

theorem dpow_mul (n : ℕ) (a z : S) (hz : z ∈ J) : γ n (a * z) = a ^ n * γ n z := by
  obtain ⟨c, t, rfl⟩ := IsLocalization.exists_mk'_eq M a
  rw [LocalizationOperations.PDLocalizationOperations.representative_spec R S M I z hz]
  let v := LocalizationOperations.PDLocalizationOperations.representative R S M I z hz
  change γ n (IsLocalization.mk' S c t * IsLocalization.mk' S (v.1 : R) v.2) =
    (IsLocalization.mk' S c t) ^ n * γ n (IsLocalization.mk' S (v.1 : R) v.2)
  rw [← IsLocalization.mk'_mul, LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ n _ ((I).mul_mem_left c v.1.property),
    δ.dpow_mul v.1.property, mul_pow, LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ n _ v.1.property,
    ← IsLocalization.mk'_pow, ← IsLocalization.mk'_mul]

theorem mul_dpow (m n : ℕ) (z : S) (hz : z ∈ J) :
    γ m z * γ n z = (Nat.choose (m + n) m : S) * γ (m + n) z := by
  rw [LocalizationOperations.PDLocalizationOperations.representative_spec R S M I z hz]
  let v := LocalizationOperations.PDLocalizationOperations.representative R S M I z hz
  change γ m (IsLocalization.mk' S (v.1 : R) v.2) * γ n (IsLocalization.mk' S (v.1 : R) v.2) = _
  rw [LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ m _ v.1.property, LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ n _ v.1.property,
    ← IsLocalization.mk'_mul, δ.mul_dpow v.1.property, ← pow_add,
    LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ (m + n) _ v.1.property,
    ← IsLocalization.mul_mk'_eq_mk'_of_mul, map_natCast]

theorem dpow_comp (m n : ℕ) (hn : n ≠ 0) (z : S) (hz : z ∈ J) :
    γ m (γ n z) = (Nat.uniformBell m n : S) * γ (m * n) z := by
  rw [LocalizationOperations.PDLocalizationOperations.representative_spec R S M I z hz]
  let v := LocalizationOperations.PDLocalizationOperations.representative R S M I z hz
  have hp : (v.2 ^ n) ^ m = v.2 ^ (m * n) := by rw [← pow_mul, Nat.mul_comm n m]
  rw [LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ n _ v.1.property,
    LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ m _ (δ.dpow_mem hn v.1.property), δ.dpow_comp hn v.1.property,
    hp, LocalizationOperations.PDLocalizationOperations.dpow_fraction R S M I δ (m * n) _ v.1.property,
    ← IsLocalization.mul_mk'_eq_mk'_of_mul, map_natCast]

/-- Divided powers on the actual image ideal in the localization. -/
def dividedPowers : DividedPowers J where
  dpow := γ
  dpow_null hz := LocalizationOperations.PDLocalizationOperations.dpow_null R S M I δ _ _ hz
  dpow_zero hz := LocalizationOperations.PDLocalizationOperations.dpow_zero R S M I δ _ hz
  dpow_one hz := LocalizationOperations.PDLocalizationOperations.dpow_one R S M I δ _ hz
  dpow_mem hn hz := LocalizationOperations.PDLocalizationOperations.dpow_mem R S M I δ _ hn _ hz
  dpow_add hz hw := PDLocalization.dpow_add R S M I δ _ _ _ hz hw
  dpow_mul hz := PDLocalization.dpow_mul R S M I δ _ _ _ hz
  mul_dpow hz := PDLocalization.mul_dpow R S M I δ _ _ _ hz
  dpow_comp hn hz := PDLocalization.dpow_comp R S M I δ _ _ hn _ hz

theorem base_isDPMorphism : DividedPowers.IsDPMorphism δ (dividedPowers R S M I δ) (algebraMap R S) where
  ideal_comp := le_refl _
  dpow_comp x hx := LocalizationOperations.PDLocalizationOperations.dpow_algebraMap R S M I δ _ x hx

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Localization.PDLocalization
