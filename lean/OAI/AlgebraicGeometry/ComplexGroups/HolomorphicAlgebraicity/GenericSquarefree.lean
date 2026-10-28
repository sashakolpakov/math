import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericPolynomialGCD
import Mathlib.RingTheory.Radical.Basic
import Mathlib.FieldTheory.Perfect

/-! # Generic Squarefree -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericSquarefree.Constructions.GenericGCD

noncomputable section

/-!
# Removing repeated roots over a coefficient domain

Take the radical over the fraction field, then clear denominators in its
divisibility and Bezout identities. These finite identities preserve the
root set and certify separability wherever their scalar denominators are
nonzero.
-/

open Set _root_.Polynomial UniqueFactorizationMonoid
open scoped nonZeroDivisors

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

theorem exists_squarefree_certificate (P : A[X]) (hP : P ≠ 0) :
    ∃ (Q : A[X]) (n : ℕ) (a b c : A) (H J U V : A[X]),
      Q ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      C a * P = Q * H ∧ C b * Q ^ (n + 1) = P * J ∧
      U * Q + V * derivative Q = C c := by
  classical
  let K := FractionRing A
  let : CharZero K := ⟨fun m n h => Nat.cast_injective (R := A)
    (IsFractionRing.injective A K (by simpa only [map_natCast] using h))⟩
  let φ : A[X] →+* K[X] := Polynomial.mapRingHom (algebraMap A K)
  have hφ : Function.Injective φ :=
    Polynomial.map_injective (algebraMap A K) (IsFractionRing.injective A K)
  have hφP : φ P ≠ 0 := by
    intro h
    exact hP (hφ (by simpa only [map_zero] using h))
  let q : K[X] := radical (φ P)
  have hq : q ≠ 0 := radical_ne_zero
  have hqsep : q.Separable := PerfectField.separable_iff_squarefree.mpr squarefree_radical
  let Q := IsLocalization.integerNormalization A⁰ q
  obtain ⟨s, hs, hQs⟩ := IsLocalization.integerNormalization_spec A⁰ q
  have hQmap : φ Q = C (algebraMap A K s) * q := by
    simpa only [φ, Polynomial.coe_mapRingHom, ← algebraMap_smul, Algebra.smul_def,
      Polynomial.algebraMap_apply] using hQs
  have hsu : IsUnit (C (algebraMap A K s) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr ((IsFractionRing.to_map_eq_zero_iff
      (R := A) (K := K)).not.mpr (nonZeroDivisors.ne_zero hs)))
  have hassoc : Associated (φ Q) q := by
    rw [hQmap]
    exact associated_unit_mul_left _ _ hsu
  have hQ : Q ≠ 0 := by
    intro h
    have hz : φ Q = 0 := by rw [h, map_zero]
    exact hq ((hassoc.eq_zero_iff).mp hz)
  have hQsep : (φ Q).Separable := by
    rw [hQmap]
    exact Separable.unit_mul hsu hqsep
  have hdiv : φ Q ∣ φ P := hassoc.dvd.trans radical_dvd_self
  obtain ⟨a, ha, H, hH⟩ := GenericPolynomialGCD.Constructions.GenericGCD.clear_mapped_divisibility (K := K) Q P hdiv
  obtain ⟨n, hn⟩ := exists_dvd_radical_self_pow hφP
  have hpow : φ P ∣ φ (Q ^ (n + 1)) := by
    rw [map_pow]
    exact (hn.trans (pow_dvd_pow_of_dvd hassoc.dvd' n)).trans
      (pow_dvd_pow _ (Nat.le_succ n))
  obtain ⟨b, hb, J, hJ⟩ := GenericPolynomialGCD.Constructions.GenericGCD.clear_mapped_divisibility (K := K) P (Q ^ (n + 1)) hpow
  let I := Ideal.span ({Q, derivative Q} : Set A[X])
  have hone : (1 : K[X]) ∈ I.map φ := by
    rw [Ideal.map_span, Set.image_pair]
    change (1 : K[X]) ∈ Ideal.span ({φ Q, (derivative Q).map (algebraMap A K)} : Set K[X])
    rw [← derivative_map]
    exact Ideal.mem_span_pair.mpr hQsep
  obtain ⟨c, hc, hmem⟩ := GenericPolynomialGCD.Constructions.GenericGCD.clear_mapped_ideal_membership (K := K) I 1
    (by simpa only [Polynomial.map_one] using hone)
  obtain ⟨U, V, hUV⟩ := Ideal.mem_span_pair.mp hmem
  exact ⟨Q, n, a, b, c, H, J, U, V, hQ, ha, hb, hc, hH, hJ,
    by simpa only [mul_one] using hUV⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericSquarefree.Constructions.GenericGCD
