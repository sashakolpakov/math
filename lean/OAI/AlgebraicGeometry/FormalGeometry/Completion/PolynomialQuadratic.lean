import OAI.AlgebraicGeometry.FormalGeometry.Completion.NonnegativeQuadraticMk
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialDifference

/-! # Polynomial Quadratic -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialQuadratic.Construction

noncomputable section

/-! A polynomial invariant with positive leading coefficient and quadratic
top coefficients supplies successive nonnegative quadratic functions. -/

open _root_.Polynomial

universe u

structure PolynomialQuadraticHeight (G : Type u) [AddCommGroup G] where
  value : G → Polynomial ℚ
  zero : value 0 = 0
  detectsZero : ∀ x, value x = 0 → x = 0
  positive : ∀ x, x ≠ 0 → 0 < (value x).leadingCoeff
  integer_values : ∀ x, ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∃ z : ℤ, (value x).eval (n : ℚ) = z
  coeff_parallelogram : ∀ d x y, (value x).natDegree ≤ d → (value y).natDegree ≤ d →
    (value (x + y)).natDegree ≤ d →
    (value (x + y)).coeff d + (value (x - y)).coeff d = 2 * ((value x).coeff d + (value y).coeff d)

namespace PolynomialQuadraticHeight

variable {G : Type u} [AddCommGroup G] (q : PolynomialQuadraticHeight G)

def restrict (S : AddSubgroup G) : PolynomialQuadraticHeight S where
  value x := q.value x
  zero := q.zero
  detectsZero x hx := Subtype.ext (q.detectsZero x hx)
  positive x hx := q.positive x (fun h => hx (Subtype.ext h))
  integer_values x := q.integer_values x
  coeff_parallelogram d x y hx hy hxy := q.coeff_parallelogram d x y hx hy hxy

def coefficientQuadratic (d : ℕ) (hd : ∀ x, (q.value x).natDegree ≤ d) : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G where
  value x := (q.value x).coeff d
  zero := by rw [q.zero, coeff_zero]
  nonneg x := by
    by_cases hx : x = 0
    · rw [hx, q.zero, coeff_zero]
    · rcases lt_or_eq_of_le (hd x) with hlt | heq
      · rw [coeff_eq_zero_of_natDegree_lt hlt]
      · rw [← heq, coeff_natDegree]
        exact (q.positive x hx).le
  parallelogram x y := q.coeff_parallelogram d x y (hd x) (hd y) (hd (x + y))

theorem coefficient_integral (d : ℕ) (hd : ∀ x, (q.value x).natDegree ≤ d) (x : G) :
    ∃ z : ℤ, (d.factorial : ℚ) * (q.coefficientQuadratic d hd).value x = z := by
  obtain ⟨b, hb⟩ := q.integer_values x
  exact PolynomialDifference.Construction.polynomial_factorial_coeff_integral_of_eventual_integer_values _ d (hd x) b hb

theorem kernel_degree_bound (d : ℕ) (hd : ∀ x, (q.value x).natDegree ≤ d + 1)
    (x : (q.coefficientQuadratic (d + 1) hd).zeroKernel) : (q.value (x : G)).natDegree ≤ d := by
  have hx : (q.value (x : G)).coeff (d + 1) = 0 := x.property
  have hb := hd x
  by_contra h
  have he : (q.value (x : G)).natDegree = d + 1 := by omega
  have hp : q.value (x : G) ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q.value (x : G)).natDegree by omega)
  have hz : (q.value (x : G)).coeff (q.value (x : G)).natDegree = 0 :=
    (congrArg (fun k : ℕ => (q.value (x : G)).coeff k) he).trans hx
  rw [coeff_natDegree] at hz
  exact (leadingCoeff_ne_zero.mpr hp) hz

theorem zero_degree_kernel_subsingleton (hd : ∀ x, (q.value x).natDegree ≤ 0) :
    Subsingleton (q.coefficientQuadratic 0 hd).zeroKernel := by
  have hz (x : (q.coefficientQuadratic 0 hd).zeroKernel) : (x : G) = 0 := by
    apply q.detectsZero
    have hx : (q.value (x : G)).coeff 0 = 0 := x.property
    rw [eq_C_of_natDegree_le_zero (hd x), hx, C_0]
  exact ⟨fun x y => Subtype.ext ((hz x).trans (hz y).symm)⟩

end PolynomialQuadraticHeight

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialQuadratic.Construction
