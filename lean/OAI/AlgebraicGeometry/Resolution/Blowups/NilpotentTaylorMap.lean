import OAI.AlgebraicGeometry.Resolution.Blowups.TruncatedTaylor

/-! # Nilpotent Taylor Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NilpotentTaylorMap.Construction

noncomputable section

/-! Finite Taylor maps with arbitrary nilpotent displacement in the target. -/

open _root_.Polynomial

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

/-- Evaluate the universal nilpotent parameter at any nilpotent displacement.
No derivation on the target is required. -/
def truncatedTaylorEval (f : R →ₐ[k] S) (t : S) (n : ℕ) (ht : t ^ n = 0) :
    TruncatedTaylor.Construction.TruncatedTaylorAlgebra R n →ₐ[k] S :=
  Ideal.Quotient.liftₐ _ (Polynomial.eval₂AlgHom f t (fun _ => Commute.all _ _)) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    rw [map_mul, map_pow]
    change (Polynomial.eval₂ f.toRingHom t X) ^ n * _ = 0
    rw [Polynomial.eval₂_X, ht, zero_mul])

theorem truncatedTaylorEval_parameter (f : R →ₐ[k] S) (t : S) (n : ℕ)
    (ht : t ^ n = 0) :
    truncatedTaylorEval f t n ht (TruncatedTaylor.Construction.truncatedTaylorParameter n) = t := by
  change Polynomial.eval₂ f.toRingHom t X = t
  exact Polynomial.eval₂_X _ _

theorem truncatedTaylorEval_constants (f : R →ₐ[k] S) (t : S) (n : ℕ)
    (ht : t ^ n = 0) (x : R) :
    truncatedTaylorEval f t n ht (TruncatedTaylor.Construction.truncatedTaylorConstants (k := k) n x) = f x := by
  change Polynomial.eval₂ f.toRingHom t (C x) = f x
  exact Polynomial.eval₂_C _ _

variable [Algebra ℚ R] [Algebra ℚ S]

/-- The finite Taylor expression is an algebra map even when the displacement
is not fixed by any derivation on the target. -/
def nilpotentTaylorMap (D : Derivation k R R) (f : R →ₐ[k] S) (t : S)
    (n : ℕ) (ht : t ^ n = 0) : R →ₐ[k] S :=
  (truncatedTaylorEval f t n ht).comp (TruncatedTaylor.Construction.truncatedTaylor D n)

theorem nilpotentTaylorMap_apply (D : Derivation k R R) (f : R →ₐ[k] S) (t : S)
    (n : ℕ) (ht : t ^ n = 0) (x : R) :
    nilpotentTaylorMap D f t n ht x =
      ∑ j ∈ Finset.range n, (j.factorial : ℚ)⁻¹ •
        (t ^ j * f ((D.toLinearMap ^ j) x)) := by
  unfold nilpotentTaylorMap
  rw [AlgHom.comp_apply, TruncatedTaylor.Construction.truncatedTaylor_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_rat_smul, map_mul, map_pow, truncatedTaylorEval_parameter,
    truncatedTaylorEval_constants]

theorem nilpotentTaylorMap_apply_short (D : Derivation k R R) (f : R →ₐ[k] S) (t : S)
    (n : ℕ) (ht : t ^ n = 0) (m : ℕ) (x : R) (hx : (D.toLinearMap ^ m) x = 0) :
    nilpotentTaylorMap D f t n ht x =
      ∑ j ∈ Finset.range m, (j.factorial : ℚ)⁻¹ •
        (t ^ j * f ((D.toLinearMap ^ j) x)) := by
  unfold nilpotentTaylorMap
  rw [AlgHom.comp_apply, TruncatedTaylor.Construction.truncatedTaylor_apply_short D n m x hx, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_rat_smul, map_mul, map_pow, truncatedTaylorEval_parameter,
    truncatedTaylorEval_constants]

theorem nilpotentTaylorMap_fixed (D : Derivation k R R) (f : R →ₐ[k] S) (t : S)
    (n : ℕ) (ht : t ^ n = 0) (x : R) (hx : D x = 0) :
    nilpotentTaylorMap D f t n ht x = f x := by
  rw [nilpotentTaylorMap_apply_short D f t n ht 1 x (by simpa using hx)]
  simp

theorem nilpotentTaylorMap_linear (D : Derivation k R R) (f : R →ₐ[k] S) (t : S)
    (n : ℕ) (ht : t ^ n = 0) (x : R) (hx : D (D x) = 0) :
    nilpotentTaylorMap D f t n ht x = f x + t * f (D x) := by
  have h : (D.toLinearMap ^ 2) x = 0 := by
    rw [pow_two, Module.End.mul_apply]
    exact hx
  rw [nilpotentTaylorMap_apply_short D f t n ht 2 x h]
  simp [Finset.sum_range_succ]

theorem nilpotentTaylorMap_coordinate (D : Derivation k R R) (f : R →ₐ[k] S) (t : S)
    (n : ℕ) (ht : t ^ n = 0) (x : R) (hx : D x = 1) :
    nilpotentTaylorMap D f t n ht x = f x + t := by
  rw [nilpotentTaylorMap_linear D f t n ht x (by rw [hx, D.map_one_eq_zero]), hx,
    map_one, mul_one]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NilpotentTaylorMap.Construction
