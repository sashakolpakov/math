import OAI.AlgebraicGeometry.Resolution.Blowups.NilpotentTaylorMap
import Mathlib.RingTheory.Unramified.Basic

/-! # Taylor Congruence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TaylorCongruence.Construction

noncomputable section

/-! Taylor congruences and uniqueness on formally unramified coordinate charts. -/

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra ℚ R] [Algebra ℚ S]

theorem nilpotentTaylorMap_sub_mem (D : Derivation k R R) (f : R →ₐ[k] S)
    (t : S) (n : ℕ) (ht : t ^ (n + 1) = 0) (I : Ideal S) (hI : t ∈ I) (x : R) :
    NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht x - f x ∈ I := by
  rw [NilpotentTaylorMap.Construction.nilpotentTaylorMap_apply, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
    Module.End.one_apply, one_mul, add_sub_cancel_right]
  apply Ideal.sum_mem
  intro j _
  have hp : t ^ (j + 1) ∈ I := by
    rw [pow_succ]
    exact I.mul_mem_left _ hI
  have hm := I.mul_mem_right (f ((D.toLinearMap ^ (j + 1)) x)) hp
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ hm

/-- A Taylor map agreeing with a second map on the coordinate algebra and
modulo the displacement is that second map on a formally unramified chart. -/
theorem formallyUnramified_nilpotentTaylor_eq
    {P : Type*} [CommRing P] [Algebra P R] [Algebra.FormallyUnramified P R]
    (D : Derivation k R R) (f g : R →ₐ[k] S) (t : S) (n : ℕ)
    (ht : t ^ (n + 1) = 0)
    (hbase : ∀ p : P, NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht (algebraMap P R p) =
      g (algebraMap P R p))
    (hred : ∀ x : R, g x - f x ∈ Ideal.span {t}) :
    NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht = g := by
  let : Algebra P S := (g.toRingHom.comp (algebraMap P R)).toAlgebra
  let gP : R →ₐ[P] S := { g.toRingHom with commutes' := fun _ => rfl }
  let τP : R →ₐ[P] S :=
    { (NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht).toRingHom with commutes' := hbase }
  have hnil : IsNilpotent (Ideal.span {t} : Ideal S) := by
    refine ⟨n + 1, ?_⟩
    change (Ideal.span {t} : Ideal S) ^ (n + 1) = ⊥
    rw [Ideal.span_singleton_pow, ht, Ideal.span_singleton_zero]
  have he : τP = gP := by
    apply Algebra.FormallyUnramified.ext (Ideal.span {t}) hnil
    intro x
    apply Ideal.Quotient.eq.mpr
    have hτ := nilpotentTaylorMap_sub_mem D f t n ht (Ideal.span {t})
      (Ideal.mem_span_singleton_self t) x
    have h := (Ideal.span {t}).sub_mem hτ (hred x)
    change NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht x - g x ∈ _
    convert h using 1
    ring
  exact AlgHom.ext fun x => AlgHom.congr_fun he x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TaylorCongruence.Construction
