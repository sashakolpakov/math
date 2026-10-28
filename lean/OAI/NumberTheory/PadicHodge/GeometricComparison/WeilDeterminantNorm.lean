import OAI.NumberTheory.PadicHodge.GeometricComparison.WeilRoot
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Weil Determinant Norm -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeilDeterminantNorm.WeilDeterminant

noncomputable section

/-! Uniform complex root weights determine the valuation of the determinant of the original operator. -/

private theorem norm_multiset_prod (s : Multiset ℂ) (r : ℝ)
    (h : ∀ z ∈ s, ‖z‖ = r) : ‖s.prod‖ = r ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    rw [Multiset.prod_cons, norm_mul, h z (Multiset.mem_cons_self _ _),
      ih (fun a ha => h a (Multiset.mem_cons_of_mem ha)), Multiset.card_cons, pow_succ]
    exact mul_comm _ _

theorem norm_constant (P : Polynomial ℤ) (hP : P.Monic) (r : ℝ)
    (h : ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ = r) :
    ‖(P.coeff 0 : ℂ)‖ = r ^ P.natDegree := by
  let Q := P.map (Int.castRingHom ℂ)
  have hQ : Q.Monic := hP.map _
  have hs : Q.Splits := IsAlgClosed.splits Q
  have hr : ∀ z ∈ Q.roots, ‖z‖ = r := by
    intro z hz
    apply h z
    simpa only [Q, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def,
      show Int.castRingHom ℂ = algebraMap ℤ ℂ from Subsingleton.elim _ _] using
      (Polynomial.mem_roots hQ.ne_zero).mp hz
  have hc := congrArg norm (hs.coeff_zero_eq_prod_roots_of_monic hQ)
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_multiset_prod _ r hr,
    ← hs.natDegree_eq_card_roots] at hc
  simpa only [Q, Polynomial.coeff_map, Int.coe_castRingHom, Polynomial.natDegree_map_eq_of_injective
    (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)] using hc

theorem constant_square (q : ℕ) (P : Polynomial ℤ) (hP : P.Monic)
    (h : ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ = Real.sqrt (q : ℝ)) :
    P.coeff 0 ^ 2 = (q : ℤ) ^ P.natDegree := by
  have hc := norm_constant P hP (Real.sqrt (q : ℝ)) h
  have hr : (P.coeff 0 : ℝ) ^ 2 = (q : ℝ) ^ P.natDegree := by
    calc
      (P.coeff 0 : ℝ) ^ 2 = ‖(P.coeff 0 : ℂ)‖ ^ 2 := by
        rw [show (P.coeff 0 : ℂ) = ((P.coeff 0 : ℝ) : ℂ) by simp,
          Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = (Real.sqrt (q : ℝ) ^ P.natDegree) ^ 2 := congrArg (fun x => x ^ 2) hc
      _ = (q : ℝ) ^ P.natDegree := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg q)]
  exact_mod_cast hr

theorem determinant_valuation_twice (q : ℕ) [Fact q.Prime]
    {V : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]
    (F : Module.End ℚ_[q] V) (P : Polynomial ℤ)
    (hP : F.charpoly = P.map (Int.castRingHom ℚ_[q]))
    (h : ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ = Real.sqrt (q : ℝ)) :
    2 * Padic.valuation F.det = (Module.finrank ℚ_[q] V : ℤ) := by
  have hm : P.Monic := Polynomial.monic_of_injective
    (show Function.Injective (Int.castRingHom ℚ_[q]) from Int.cast_injective)
    (hP ▸ F.charpoly_monic)
  have hn : P.natDegree = Module.finrank ℚ_[q] V := by
    rw [← F.charpoly_natDegree, hP, Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (Int.castRingHom ℚ_[q]) from Int.cast_injective)]
  have hc : (P.coeff 0 : ℚ_[q]) ^ 2 = (q : ℚ_[q]) ^ P.natDegree := by
    exact_mod_cast constant_square q P hm h
  have hd : F.det ^ 2 = (q : ℚ_[q]) ^ P.natDegree := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, hP, Polynomial.coeff_map, mul_pow]
    have hs : ((-1 : ℚ_[q]) ^ Module.finrank ℚ_[q] V) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [hs, one_mul]
    exact hc
  have hv := congrArg Padic.valuation hd
  simpa only [Padic.valuation_pow, Padic.valuation_p, mul_one, hn, Nat.cast_ofNat] using hv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeilDeterminantNorm.WeilDeterminant
