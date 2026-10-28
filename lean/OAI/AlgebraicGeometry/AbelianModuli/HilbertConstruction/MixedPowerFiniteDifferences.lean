import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.DifferencePolynomial
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # Mixed Power Finite Differences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedPowerFiniteDifferences

noncomputable section

/-! One unit difference and g differences of size d applied to the
degree-(g+1) monomial give (g+1)! d^g. This is the numerical coefficient
for one hyperplane and g cuts by the d-th tensor power. -/
open _root_.Polynomial

theorem fwdDiff_iter_affine_argument (f : ℚ → ℚ) (a d : ℚ) (n : ℕ) (x : ℚ) :
    (fwdDiff 1)^[n] (fun y => f (a + d * y)) x =
      (fwdDiff d)^[n] f (a + d * x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (fwdDiff 1)^[n] (fun y => f (a + d * y)) (x + 1) -
      (fwdDiff 1)^[n] (fun y => f (a + d * y)) x =
      (fwdDiff d)^[n] f (a + d * x + d) - (fwdDiff d)^[n] f (a + d * x)
    rw [ih, ih, show a + d * (x + 1) = a + d * x + d by ring]

theorem polynomial_fwdDiff_degree_arbitrary_step (P : Polynomial ℚ) (d : ℚ) (hd : d ≠ 0) (a : ℚ) :
    (fwdDiff d)^[P.natDegree] P.eval a =
      P.leadingCoeff * d ^ P.natDegree * (P.natDegree.factorial : ℚ) := by
  let Q := P.comp (C d * X + C a)
  have hdeg : Q.natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_linear hd, mul_one]
  have hlead : Q.leadingCoeff = P.leadingCoeff * d ^ P.natDegree := by
    rw [leadingCoeff_comp (by rw [natDegree_linear hd]; exact one_ne_zero), leadingCoeff_linear hd]
  have heval : Q.eval = fun x => P.eval (a + d * x) := by
    funext x
    simp [Q, add_comm]
  have h := congrFun Q.fwdDiff_iter_degree_eq_factorial (0 : ℚ)
  change (fwdDiff 1)^[Q.natDegree] Q.eval 0 = Q.leadingCoeff * (Q.natDegree.factorial : ℚ) at h
  rw [hdeg, hlead, heval] at h
  have ht := fwdDiff_iter_affine_argument (fun x => P.eval x) a d P.natDegree 0
  simpa only [mul_zero, add_zero] using ht.symm.trans h

theorem forwardDifferences_commute (a b : ℚ) :
    Function.Commute (fwdDiff a : (ℚ → ℚ) → (ℚ → ℚ)) (fwdDiff b) := by
  intro f
  funext x
  simp only [fwdDiff]
  rw [add_right_comm x a b]
  ring

theorem forwardDifference_commutes_iterate (a b : ℚ) (n : ℕ) (f : ℚ → ℚ) :
    fwdDiff a ((fwdDiff b)^[n] f) = (fwdDiff b)^[n] (fwdDiff a f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [forwardDifferences_commute a b _, ih]

theorem mixedPower_finiteDifference (g : ℕ) (d : ℚ) (hd : d ≠ 0) (a : ℚ) :
    fwdDiff 1 ((fwdDiff d)^[g] (fun x : ℚ => x ^ (g + 1))) a =
      ((g + 1).factorial : ℚ) * d ^ g := by
  let P := Power.DifferencePolynomial.powerDifferencePolynomial (g + 1)
  have hdeg : P.natDegree = g := (Power.DifferencePolynomial.powerDifferencePolynomial_degree_coeff g).1
  have hlead : P.leadingCoeff = (g + 1 : ℚ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Power.DifferencePolynomial.powerDifferencePolynomial_leadingCoeff (g + 1)
  have heval : P.eval = fwdDiff 1 (fun x : ℚ => x ^ (g + 1)) := by
    funext x
    exact Power.DifferencePolynomial.powerDifferencePolynomial_eval (g + 1) x
  rw [forwardDifference_commutes_iterate]
  have h := polynomial_fwdDiff_degree_arbitrary_step P d hd a
  rw [hdeg, hlead, heval] at h
  rw [h]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedPowerFiniteDifferences
