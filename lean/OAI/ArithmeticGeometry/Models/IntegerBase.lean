import OAI.ArithmeticGeometry.Models.CoefficientSystem

/-! # Integer Base -/

namespace OAI.ArithmeticGeometry.Models.IntegerBase.Constructions.Foundations

/-! Passage from finite coefficient rings to localized rings of integers. -/

open scoped _root_.NumberField nonZeroDivisors

universe u

variable (K : Type u) [Field K] [NumberField K]

theorem integersAwayToField_injective (N : ℕ) (hN : N ≠ 0) :
    Function.Injective (Models.Algebra.Constructions.Foundations.integersAwayToField K N hN) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (N : 𝓞 K))
  intro a ha
  rw [Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap] at ha
  have ha0 : a = 0 := (IsFractionRing.injective (𝓞 K) K) (ha.trans (map_zero _).symm)
  rw [ha0, map_zero]

noncomputable def integersAwayAlgHom (N : ℕ) (hN : N ≠ 0) :
    Localization.Away (N : 𝓞 K) →ₐ[𝓞 K] K where
  toRingHom := Models.Algebra.Constructions.Foundations.integersAwayToField K N hN
  commutes' := Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap K N hN

/-- Every finite coefficient ring maps compatibly into a localization of the
ring of integers, with any previously specified denominators also inverted. -/
theorem finite_coefficient_ring_factors_through_integers
    (s : Finset K) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ (N : ℕ) (hN : N ≠ 0), N₀ ∣ N ∧
      ∃ φ : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s →ₐ[𝓞 K] Localization.Away (N : 𝓞 K),
        (Models.Algebra.Constructions.Foundations.integersAwayToField K N hN).comp φ.toRingHom =
          (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s).val.toRingHom := by
  classical
  obtain ⟨N, hN, hd, hcoeff⟩ := Models.Algebra.Constructions.Foundations.finite_coefficients_in_localized_integers K
    (fun c : s ↦ (c : K)) N₀ hN₀
  let F := integersAwayAlgHom K N hN
  have hs : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s ≤ F.range := by
    apply Algebra.adjoin_le
    intro c hc
    exact hcoeff ⟨c, hc⟩
  let e := AlgEquiv.ofInjective F (integersAwayToField_injective K N hN)
  let φ := e.symm.toAlgHom.comp (Subalgebra.inclusion hs)
  refine ⟨N, hN, hd, φ, ?_⟩
  ext a
  change ((e (e.symm (Subalgebra.inclusion hs a))) : K) = (a : K)
  rw [e.apply_symm_apply]
  rfl

end OAI.ArithmeticGeometry.Models.IntegerBase.Constructions.Foundations
