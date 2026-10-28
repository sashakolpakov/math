import OAI.ArithmeticGeometry.Models.IntegerBase
import Mathlib.RingTheory.FiniteType

/-! # Type Integer Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeIntegerFactorization

noncomputable section

section

/-! Every homomorphism from a finite-type integer algebra to a number
field factors through an actual localization of its ring of integers. -/

open scoped _root_.NumberField

open OAI.ArithmeticGeometry.Models.IntegerBase.Constructions.Foundations

theorem finiteType_ringHom_factors_through_integers
    {S L : Type} [CommRing S] [Field L] [NumberField L] [Algebra.FiniteType ℤ S]
    (j : S →+* L) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ (N : ℕ) (hN : N ≠ 0), N₀ ∣ N ∧
      ∃ φ : S →+* Localization.Away (N : NumberField.RingOfIntegers L),
        (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField L N hN).comp φ = j := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ S).FG)
  obtain ⟨N, hN, hdiv, hcoeff⟩ := ArithmeticGeometry.Models.Algebra.Constructions.Foundations.finite_coefficients_in_localized_integers L
    (fun x : s => j x.val) N₀ hN₀
  let : Algebra ℤ (Localization.Away (N : NumberField.RingOfIntegers L)) := Ring.toIntAlgebra _
  let J := j.toIntAlgHom
  let F := (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField L N hN).toIntAlgHom
  have hle : Algebra.adjoin ℤ (s : Set S) ≤ F.range.comap J := by
    apply Algebra.adjoin_le
    intro x hx
    exact hcoeff ⟨x, hx⟩
  have hJ : ∀ x : S, J x ∈ F.range := by
    rw [hs] at hle
    exact fun x => hle (show x ∈ (⊤ : Subalgebra ℤ S) from trivial)
  let e := AlgEquiv.ofInjective F (ArithmeticGeometry.Models.IntegerBase.Constructions.Foundations.integersAwayToField_injective L N hN)
  let φ := e.symm.toAlgHom.comp (J.codRestrict F.range hJ)
  refine ⟨N, hN, hdiv, φ.toRingHom, ?_⟩
  ext x
  change ((e (e.symm (J.codRestrict F.range hJ x))) : L) = j x
  rw [e.apply_symm_apply]
  rfl

end

/-! Arithmetic coefficient factorization can retain a chosen nonzero
coefficient as a unit by factoring its actual principal localization. -/

open OAI.ArithmeticGeometry.Models.IntegerBase.Constructions.Foundations

theorem finiteType_ringHom_unit_factors_through_integers
    {S L : Type} [CommRing S] [Field L] [NumberField L] [Algebra.FiniteType ℤ S]
    (j : S →+* L) (r : S) (hr : j r ≠ 0) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ (N : ℕ) (hN : N ≠ 0), N₀ ∣ N ∧
      ∃ φ : S →+* Localization.Away (N : NumberField.RingOfIntegers L),
        (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField L N hN).comp φ = j ∧ IsUnit (φ r) := by
  let A := Localization.Away r
  let : Algebra ℤ A := Ring.toIntAlgebra A
  have : IsScalarTower ℤ S A := IsScalarTower.of_algebraMap_eq (fun z => by simp)
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (R := ℤ) (S := S) (A := A)
    (inferInstanceAs (Algebra.FiniteType ℤ S)) (inferInstanceAs (Algebra.FiniteType S A))
  let j' : A →+* L := IsLocalization.Away.lift r (isUnit_iff_ne_zero.mpr hr)
  obtain ⟨N, hN, hdiv, ψ, hψ⟩ := finiteType_ringHom_factors_through_integers j' N₀ hN₀
  let φ := ψ.comp (algebraMap S A)
  refine ⟨N, hN, hdiv, φ, ?_, ?_⟩
  · ext x
    exact (RingHom.congr_fun hψ (algebraMap S A x)).trans (IsLocalization.Away.lift_eq r _ x)
  · exact (IsLocalization.Away.algebraMap_isUnit (S := A) r).map ψ

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeIntegerFactorization
