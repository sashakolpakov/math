import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Extension.Presentation.Core

/-! # Algebra -/

namespace OAI.ArithmeticGeometry.Models.Algebra.Constructions.Foundations

/-! Algebraic foundations for Foundations. This file imports no graph statements. -/

open scoped _root_.NumberField nonZeroDivisors TensorProduct

universe u v

variable (K : Type u) [Field K] [NumberField K]

/-- A nonzero natural denominator defines the canonical map into the number field. -/
noncomputable def integersAwayToField (N : ℕ) (hN : N ≠ 0) :
    Localization.Away (N : 𝓞 K) →+* K :=
  IsLocalization.Away.lift (N : 𝓞 K)
    (show IsUnit (algebraMap (𝓞 K) K (N : 𝓞 K)) from
      by simpa using (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hN) : IsUnit (N : K)))

@[simp]
theorem integersAwayToField_algebraMap (N : ℕ) (hN : N ≠ 0) (a : 𝓞 K) :
    integersAwayToField K N hN (algebraMap (𝓞 K) (Localization.Away (N : 𝓞 K)) a) =
      algebraMap (𝓞 K) K a :=
  IsLocalization.Away.lift_eq _ _ _

theorem integersAwayToField_comp (N : ℕ) (hN : N ≠ 0) :
    (integersAwayToField K N hN).comp
        (algebraMap (𝓞 K) (Localization.Away (N : 𝓞 K))) =
      algebraMap (𝓞 K) K := by
  ext a
  exact integersAwayToField_algebraMap K N hN a

/-- A common natural denominator can also contain prescribed prime factors. -/
theorem exists_common_natural_denominator
    {ι : Type v} [Finite ι] (x : ι → K) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧ N₀ ∣ N ∧
      ∀ i, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (N : K) * x i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) x
  obtain ⟨m, hm, hmb⟩ := b.property
  have hm0 : m ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hm
  let N := N₀ * m.natAbs
  have hN : N ≠ 0 := mul_ne_zero hN₀ (Int.natAbs_ne_zero.mpr hm0)
  refine ⟨N, hN, dvd_mul_right N₀ m.natAbs, ?_⟩
  have hmN : m ∣ (N : ℤ) := Int.dvd_natCast.mpr (dvd_mul_left m.natAbs N₀)
  obtain ⟨c, hc⟩ := hmN
  intro i
  obtain ⟨a, ha⟩ := hb i
  refine ⟨(c : 𝓞 K) * a, ?_⟩
  have ha' : algebraMap (𝓞 K) K a = (m : K) * x i := by
    simpa [Algebra.smul_def, ← hmb] using ha
  have hc' : (N : K) = (m : K) * (c : K) := by
    exact_mod_cast hc
  simp only [map_mul, map_intCast, ha', hc']
  rw [← mul_assoc, mul_comm (c : K) (m : K)]

/-- Every element with denominator `N` belongs to the canonical localization image. -/
theorem mem_range_integersAwayToField
    (N : ℕ) (hN : N ≠ 0) (x : K)
    (hx : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (N : K) * x) :
    x ∈ (integersAwayToField K N hN).range := by
  obtain ⟨a, ha⟩ := hx
  let L := Localization.Away (N : 𝓞 K)
  let j := integersAwayToField K N hN
  let z : L := IsLocalization.Away.invSelf (N : 𝓞 K)
  have hz : (N : K) * j z = 1 := by
    have H := congrArg j (IsLocalization.Away.mul_invSelf (S := L) (N : 𝓞 K))
    simpa [j] using H
  refine ⟨algebraMap (𝓞 K) L a * z, ?_⟩
  change j (algebraMap (𝓞 K) L a * z) = x
  rw [map_mul, integersAwayToField_algebraMap, ha]
  calc
    (N : K) * x * j z = x * ((N : K) * j z) := by ac_rfl
    _ = x := by rw [hz, mul_one]

/-- A finite family of coefficients is contained in one localization of the integers. -/
theorem finite_coefficients_in_localized_integers
    {ι : Type v} [Finite ι] (x : ι → K) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ (N : ℕ) (hN : N ≠ 0), N₀ ∣ N ∧
      ∀ i, x i ∈ (integersAwayToField K N hN).range := by
  obtain ⟨N, hN, hd, h⟩ := exists_common_natural_denominator K x N₀ hN₀
  exact ⟨N, hN, hd, fun i ↦ mem_range_integersAwayToField K N hN (x i) (h i)⟩

/-- A finitely presented algebra over a number field has an integral model,
with the base-change isomorphism included in the conclusion. -/
theorem finitely_presented_algebra_has_integral_model
    (A : Type v) [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A]
    (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ (N : ℕ) (hN : N ≠ 0), N₀ ∣ N ∧
      let L := Localization.Away (N : 𝓞 K)
      letI : Algebra L K := (integersAwayToField K N hN).toAlgebra
      ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra L A₀),
        Algebra.FinitePresentation L A₀ ∧ Nonempty (K ⊗[L] A₀ ≃ₐ[K] A) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation K A
  let : Finite P.coeffs := P.finite_coeffs.to_subtype
  obtain ⟨N, hN, hd, hcoeff⟩ := finite_coefficients_in_localized_integers K
    (fun c : P.coeffs ↦ (c : K)) N₀ hN₀
  refine ⟨N, hN, hd, ?_⟩
  let L := Localization.Away (N : 𝓞 K)
  let : Algebra L K := (integersAwayToField K N hN).toAlgebra
  let : Algebra L A := ((algebraMap K A).comp (integersAwayToField K N hN)).toAlgebra
  let : IsScalarTower L K A := IsScalarTower.of_algebraMap_eq' rfl
  let : P.HasCoeffs L := ⟨fun c hc ↦ hcoeff ⟨c, hc⟩⟩
  exact ⟨P.ModelOfHasCoeffs L, inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv L⟩⟩

end OAI.ArithmeticGeometry.Models.Algebra.Constructions.Foundations
