import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialSaturationComponents
import OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientPermissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Component -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Component.Construction

noncomputable section

/-! The canonical coefficient component center is smooth and permissible in every dimension. -/

open _root_.CategoryTheory

universe u

variable (k : Type u) {R : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing R] [Algebra k R]

theorem coefficientComponentCenter_smooth (z : R) (J : Ideal R) (b : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] :
    Algebra.Smooth k (R ⧸ ComponentNaturality.Construction.coefficientComponentCenter k z J b) := by
  let I := ComponentNaturality.Construction.coefficientComponentCenter k z J b
  have hm := ComponentNaturality.Construction.coefficientComponentCenter_quotient k z J b
  have hsm := DifferentialSaturationComponents.Construction.relativeDifferentialSaturation_quotient_smooth k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b)
  let : Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {z}))) :=
    hm.symm ▸ hsm
  let : Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ I.map (Ideal.Quotient.mkₐ k (Ideal.span {z}))) := by
    change Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {z})))
    infer_instance
  exact Algebra.Smooth.of_equiv (DoubleQuot.quotQuotEquivQuotOfLEₐ k
    ((Ideal.span_singleton_le_iff_mem I).mpr (ComponentNaturality.Construction.coefficientComponentCenter_normal_mem k z J b)))

theorem coefficientComponentCenter_generators (z : R) (J : Ideal R) (b : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] :
    ∃ r ∈ ComponentNaturality.Construction.coefficientComponentCenter k z J b,
      ComponentNaturality.Construction.coefficientComponentCenter k z J b = Ideal.span {r} ⊔ Ideal.span {z} ∧
        r * (1 - r) ∈ Ideal.span {z} := by
  apply IdempotentQuotientPermissibility.Construction.idempotent_hypersurface_center_generators z _ (ComponentNaturality.Construction.coefficientComponentCenter_normal_mem k z J b)
  rw [ComponentNaturality.Construction.coefficientComponentCenter_quotient]
  exact DifferentialSaturationComponents.Construction.relativeDifferentialSaturation_idempotent_generator k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b)

theorem tangent_le_coefficientComponentCenter (z : R) (J : Ideal R) (n : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ ComponentNaturality.Construction.coefficientComponentCenter k z J (n + 1) := by
  let C := Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1)
  let K := DifferentialSaturation.Construction.relativeDifferentialSaturation k C
  let : Algebra.Smooth k ((R ⧸ Ideal.span {z}) ⧸ K) := DifferentialSaturationComponents.Construction.relativeDifferentialSaturation_quotient_smooth k C
  have hrad : K.IsRadical := (Ideal.isRadical_iff_quotient_reduced K).mpr (Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k)
  let i : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hterm := le_iSup (fun j : Fin (n + 1) =>
    ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
      WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) j) i
  change ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
    WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) i ≤ C at hterm
  intro x hx
  change Ideal.Quotient.mk (Ideal.span {z}) x ∈ K
  apply hrad
  refine ⟨WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) i, ?_⟩
  exact DifferentialSaturation.Construction.le_relativeDifferentialSaturation k C (hterm (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hx) _))

theorem coefficientComponentCenter_permissible [Algebra ℚ R]
    (E : Derivation k R R) (z : R) (hz : E z = 1) (J : Ideal R) (b : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] : J ≤ (ComponentNaturality.Construction.coefficientComponentCenter k z J b) ^ b := by
  cases b with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
  | succ n =>
      obtain ⟨r, hr, hI, hrel⟩ := coefficientComponentCenter_generators k z J (n + 1)
      exact IdempotentQuotientPermissibility.Construction.idempotent_quotient_center_permissible E z hz _ J r hr hI hrel n
        (tangent_le_coefficientComponentCenter k z J n)

theorem coefficientComponentCenter_blowup_isIso (z : R) (hz : IsRegular z) (J : Ideal R) (b : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] :
    IsIso (ReesGrading.Construction.affineBlowupToSpec (ComponentNaturality.Construction.coefficientComponentCenter k z J b)) := by
  obtain ⟨r, _, hI, hrel⟩ := coefficientComponentCenter_generators k z J b
  exact Locally.PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_idempotent_quotient _ r z hI hrel hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Component.Construction
