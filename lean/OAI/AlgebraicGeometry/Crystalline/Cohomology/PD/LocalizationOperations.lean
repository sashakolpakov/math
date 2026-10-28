import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.RingTheory.Localization.Ideal

/-! # Localization Operations -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.LocalizationOperations.PDLocalizationOperations

noncomputable section

/-!
# Divided-power operations on a localized ideal

The localized operation sends a fraction x/s with x in the original PD
ideal to gamma_n(x)/s^n. Homogeneity of divided powers proves that this
formula is independent of the fraction representation, even when the
coefficient ring has torsion or the localization map is not injective.
-/

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S] (I : Ideal R) (δ : DividedPowers I)

local notation "J" => I.map (algebraMap R S)

theorem fraction_congr (n : ℕ) (x y : R) (hx : x ∈ I) (hy : y ∈ I) (s t : M)
    (h : IsLocalization.mk' S x s = IsLocalization.mk' S y t) :
    IsLocalization.mk' S (δ.dpow n x) (s ^ n) = IsLocalization.mk' S (δ.dpow n y) (t ^ n) := by
  obtain ⟨c, hc⟩ := (IsLocalization.eq (S := S)).mp h
  apply (IsLocalization.eq (S := S)).mpr
  refine ⟨c ^ n, ?_⟩
  have hd := congrArg (δ.dpow n) hc
  rw [← mul_assoc, δ.dpow_mul hx, ← mul_assoc, δ.dpow_mul hy, mul_pow, mul_pow,
    mul_assoc, mul_assoc] at hd
  exact hd

def representative (z : S) (hz : z ∈ J) : I × M :=
  ((IsLocalization.mem_map_algebraMap_iff M S).mp hz).choose

theorem representative_spec (z : S) (hz : z ∈ J) :
    z = IsLocalization.mk' S ((representative R S M I z hz).1 : R) (representative R S M I z hz).2 :=
  IsLocalization.eq_mk'_iff_mul_eq.mpr ((IsLocalization.mem_map_algebraMap_iff M S).mp hz).choose_spec

def dpow (n : ℕ) (z : S) : S := by
  classical
  exact if hz : z ∈ J then IsLocalization.mk' S (δ.dpow n (representative R S M I z hz).1)
    ((representative R S M I z hz).2 ^ n) else 0

theorem fraction_mem (x : R) (hx : x ∈ I) (s : M) : IsLocalization.mk' S x s ∈ J :=
  IsLocalization.mk'_mem_iff.mpr (Ideal.mem_map_of_mem (algebraMap R S) hx)

theorem dpow_fraction (n : ℕ) (x : R) (hx : x ∈ I) (s : M) :
    PDLocalizationOperations.dpow R S M I δ n (IsLocalization.mk' S x s) = IsLocalization.mk' S (δ.dpow n x) (s ^ n) := by
  rw [PDLocalizationOperations.dpow, dite_eq_left (fraction_mem R S M I x hx s)]
  apply fraction_congr R S M I δ n _ x
    (representative R S M I _ (fraction_mem R S M I x hx s)).1.property hx
  exact (representative_spec R S M I _ (fraction_mem R S M I x hx s)).symm

theorem dpow_algebraMap (n : ℕ) (x : R) (hx : x ∈ I) :
    PDLocalizationOperations.dpow R S M I δ n (algebraMap R S x) = algebraMap R S (δ.dpow n x) := by
  rw [← IsLocalization.mk'_one (M := M) S x, dpow_fraction R S M I δ n x hx,
    one_pow, IsLocalization.mk'_one]

theorem dpow_null (n : ℕ) (z : S) (hz : z ∉ J) : PDLocalizationOperations.dpow R S M I δ n z = 0 := by
  rw [PDLocalizationOperations.dpow, dite_eq_right hz]

theorem dpow_zero (z : S) (hz : z ∈ J) : PDLocalizationOperations.dpow R S M I δ 0 z = 1 := by
  rw [representative_spec R S M I z hz, dpow_fraction R S M I δ 0 _
    (representative R S M I z hz).1.property, δ.dpow_zero (representative R S M I z hz).1.property,
    pow_zero, IsLocalization.mk'_one, map_one]

theorem dpow_one (z : S) (hz : z ∈ J) : PDLocalizationOperations.dpow R S M I δ 1 z = z := by
  rw [representative_spec R S M I z hz, dpow_fraction R S M I δ 1 _
    (representative R S M I z hz).1.property, δ.dpow_one (representative R S M I z hz).1.property, pow_one]

theorem dpow_mem (n : ℕ) (hn : n ≠ 0) (z : S) (hz : z ∈ J) : PDLocalizationOperations.dpow R S M I δ n z ∈ J := by
  rw [representative_spec R S M I z hz, dpow_fraction R S M I δ n _
    (representative R S M I z hz).1.property]
  exact fraction_mem R S M I _ (δ.dpow_mem hn (representative R S M I z hz).1.property) _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.LocalizationOperations.PDLocalizationOperations
