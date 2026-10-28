import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Power Series Monomial -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesMonomial.Construction.PowerSeriesLine

noncomputable section

/-! Restriction of a formal power series to a line, with its coefficient formula. -/

open MvPowerSeries

variable {σ R : Type*} [Finite σ] [CommRing R]

def coordinates (v : σ → R) : σ → PowerSeries R := fun i => v i • PowerSeries.X

theorem hasSubst (v : σ → R) : HasSubst (coordinates v) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  change PowerSeries.constantCoeff (v i • PowerSeries.X) = 0
  simp

omit [Finite σ] in
theorem polynomial_monomial (v : σ → R) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.aeval (coordinates v) (MvPolynomial.monomial d r) =
      PowerSeries.monomial d.degree (r * d.prod (fun i m => v i ^ m)) := by
  classical
  rw [MvPolynomial.aeval_monomial, PowerSeries.monomial_eq_C_mul_X_pow]
  simp only [coordinates, Algebra.smul_def, PowerSeries.algebraMap_apply, Finsupp.prod,
    mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finsupp.degree_apply,
    Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul, Algebra.algebraMap_self,
    RingHom.id_apply]

omit [Finite σ] in
theorem polynomial_coeff (v : σ → R) (p : MvPolynomial σ R) (n : ℕ) :
    PowerSeries.coeff n (MvPolynomial.aeval (coordinates v) p) =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent n p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d r =>
    rw [polynomial_monomial]
    have he : MvPolynomial.homogeneousComponent n (MvPolynomial.monomial d r) =
        if d.degree = n then MvPolynomial.monomial d r else 0 := by
      by_cases h : d.degree = n
      · rw [ite_eq_left h]
        exact MvPolynomial.homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_monomial r h)
      · rw [ite_eq_right h]
        ext e
        by_cases hde : d = e
        · subst e
          simp [MvPolynomial.coeff_homogeneousComponent, h]
        · simp [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_monomial, hde]
    rw [he]
    split_ifs with h
    · simp [h, MvPolynomial.eval_monomial]
    · simp [PowerSeries.coeff_monomial, Ne.symm h]

theorem coeff (v : σ → R) (f : MvPowerSeries σ R) (n : ℕ) :
    PowerSeries.coeff n (subst (coordinates v) f) =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent n (f.truncTotal (n + 1))) := by
  have he := truncTotal_subst_eq_truncTotal_truncTotal_subst (f := f) (k := n + 1)
    (a := coordinates v) (fun i => by
      change PowerSeries.constantCoeff (v i • PowerSeries.X) = 0
      simp)
  have he' := congrArg ((fun p => AddMonoidAlgebra.coeff p ((Finsupp.single () n)))) he
  have hn : (Finsupp.single () n).degree < n + 1 := by simp
  rw [coeff_truncTotal _ hn, coeff_truncTotal _ hn, subst_coe] at he'
  change PowerSeries.coeff n (subst (coordinates v) f) =
    PowerSeries.coeff n (MvPolynomial.aeval (coordinates v) (f.truncTotal (n + 1))) at he'
  exact he'.trans (polynomial_coeff v _ n)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesMonomial.Construction.PowerSeriesLine
