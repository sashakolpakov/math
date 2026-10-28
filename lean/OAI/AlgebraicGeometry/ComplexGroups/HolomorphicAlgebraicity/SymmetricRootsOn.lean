import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic

/-! # Symmetric Roots On -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SymmetricRootsOn.Constructions.SymmetricRoots

noncomputable section

/-!
# Holomorphic polynomial coefficients from root power sums

Newton's identities recover elementary symmetric functions from power sums.
Individual root functions need no continuity or differentiability.
-/

open Set _root_.Polynomial
open scoped BigOperators

def elementary {d : ℕ} (roots : Fin d → ℂ) (k : ℕ) : ℂ :=
  MvPolynomial.eval roots (MvPolynomial.esymm (Fin d) ℂ k)

theorem elementary_zero {d : ℕ} (roots : Fin d → ℂ) : elementary roots 0 = 1 := by
  simp [elementary, MvPolynomial.esymm_zero]

theorem newton_identity {d : ℕ} (roots : Fin d → ℂ) (k : ℕ) :
    (k : ℂ) * elementary roots k = (-1 : ℂ) ^ (k + 1) *
      ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
        (-1 : ℂ) ^ a.1 * elementary roots a.1 * ∑ i, roots i ^ a.2 := by
  have h := congrArg (MvPolynomial.eval roots) (MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k)
  simpa only [map_mul, map_pow, map_natCast, map_neg, map_one, map_sum,
    elementary, MvPolynomial.psum, MvPolynomial.eval_X] using h

theorem differentiableOn_elementary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {d : ℕ} (roots : E → Fin d → ℂ) {U : Set E}
    (hp : ∀ k : ℕ, DifferentiableOn ℂ (fun y => ∑ i, roots y i ^ k) U) (k : ℕ) :
    DifferentiableOn ℂ (fun y => elementary (roots y) k) U := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      simpa only [elementary_zero] using (differentiableOn_const (c := (1 : ℂ)) (s := U))
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have heq (y : E) : elementary (roots y) k = (k : ℂ)⁻¹ * ((-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1 : ℂ) ^ a.1 * elementary (roots y) a.1 * ∑ i, roots y i ^ a.2) := by
      rw [← newton_identity, ← mul_assoc, inv_mul_cancel₀ hk', one_mul]
    simp_rw [heq]
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro a ha
    exact ((ih a.1 (Finset.mem_filter.mp ha).2).const_mul _).fun_mul (hp a.2)

def rootPolynomial {d : ℕ} (roots : Fin d → ℂ) : Polynomial ℂ :=
  ∏ i, (X - C (roots i))

theorem rootPolynomial_monic {d : ℕ} (roots : Fin d → ℂ) : (rootPolynomial roots).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (roots i))

theorem rootPolynomial_natDegree {d : ℕ} (roots : Fin d → ℂ) :
    (rootPolynomial roots).natDegree = d := by
  simp [rootPolynomial]

theorem rootPolynomial_coeff {d : ℕ} (roots : Fin d → ℂ) {k : ℕ} (hk : k ≤ d) :
    (rootPolynomial roots).coeff k = (-1 : ℂ) ^ (d - k) * elementary roots (d - k) := by
  have he : elementary roots (d - k) =
      (Finset.univ.val.map roots).esymm (d - k) := by
    simpa only [elementary, MvPolynomial.aeval_eq_eval] using
      MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin d) ℂ (d - k) roots
  rw [he]
  have hcard : k ≤ (Finset.univ.val.map roots).card := by simpa using hk
  have h := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map roots) hcard
  simpa only [Multiset.map_map, Function.comp_def, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_fin, rootPolynomial, Finset.prod] using h

theorem differentiableOn_rootPolynomial_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {d : ℕ} (roots : E → Fin d → ℂ) {U : Set E}
    (hp : ∀ k : ℕ, DifferentiableOn ℂ (fun y => ∑ i, roots y i ^ k) U) (k : ℕ) :
    DifferentiableOn ℂ (fun y => (rootPolynomial (roots y)).coeff k) U := by
  by_cases hk : k ≤ d
  · simp_rw [rootPolynomial_coeff _ hk]
    exact (differentiableOn_elementary roots hp (d - k)).const_mul _
  · have heq : (fun y => (rootPolynomial (roots y)).coeff k) = fun _ => 0 := by
      funext y
      exact coeff_eq_zero_of_natDegree_lt (by rw [rootPolynomial_natDegree]; omega)
    rw [heq]
    exact differentiableOn_const _

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SymmetricRootsOn.Constructions.SymmetricRoots
