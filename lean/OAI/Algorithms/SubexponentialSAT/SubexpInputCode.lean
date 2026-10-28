import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.WeightedSupport

namespace OAI.Algorithms

/-!
# Executable residue-row dot products and beta inputs

The programs use explicit coefficient and input arrays indexed by Fin D.
The dot-product loop performs D multiplications and D additions. A lift is
supplied as an ordinary executable backend function; its implementation cost
is kept separate rather than silently counted as one scalar operation.
-/

namespace SubexponentialSAT.SubexpInputCode

open scoped BigOperators

section DotProgram

variable {D : ℕ} {K : Type*}

/-- Traverse a supplied list, doing one multiplication and one addition at
each coordinate. The returned natural number counts those scalar operations. -/
def dotListWithCost [Zero K] [Add K] [Mul K]
    (row x : Fin D → K) : List (Fin D) → K × ℕ
  | [] => (0, 0)
  | i :: tail =>
      let rest := dotListWithCost row x tail
      (row i * x i + rest.1, rest.2 + 2)

@[simp] theorem dotListWithCost_value [Semiring K] (row x : Fin D → K)
    (coordinates : List (Fin D)) :
    (dotListWithCost row x coordinates).1 =
      (coordinates.map (fun i => row i * x i)).sum := by
  induction coordinates with
  | nil => rfl
  | cons i tail ih => simp [dotListWithCost, ih]

@[simp] theorem dotListWithCost_cost [Zero K] [Add K] [Mul K] (row x : Fin D → K)
    (coordinates : List (Fin D)) :
    (dotListWithCost row x coordinates).2 = 2 * coordinates.length := by
  induction coordinates with
  | nil => rfl
  | cons i tail ih => simp [dotListWithCost, ih, Nat.mul_add]

/-- Complete finite dot product; the coordinate enumerator is executable. -/
def dotWithCost [Zero K] [Add K] [Mul K] (row x : Fin D → K) : K × ℕ :=
  dotListWithCost row x (List.finRange D)

@[simp] theorem dotWithCost_value [Semiring K] (row x : Fin D → K) :
    (dotWithCost row x).1 = ∑ i, row i * x i := by
  rw [dotWithCost, dotListWithCost_value,
    ← List.sum_toFinset (fun i => row i * x i) (List.nodup_finRange D)]
  simp

@[simp] theorem dotWithCost_cost [Zero K] [Add K] [Mul K] (row x : Fin D → K) :
    (dotWithCost row x).2 = 2 * D := by
  simp [dotWithCost]

/-- Two supplied array entries are read at each coordinate. -/
def dotInputReads (D : ℕ) : ℕ := 2 * D

end DotProgram

section LinearFormBridge

variable {D : ℕ} {K : Type*} [CommSemiring K]

theorem eval_linearForm (row x : Fin D → K) :
    MvPolynomial.eval x (WeightedSupport.linearForm Finset.univ row) =
      ∑ i, row i * x i := by
  simp [WeightedSupport.linearForm, MvPolynomial.eval_monomial]

theorem dotWithCost_eq_eval_linearForm (row x : Fin D → K) :
    (dotWithCost row x).1 =
      MvPolynomial.eval x (WeightedSupport.linearForm Finset.univ row) := by
  rw [dotWithCost_value, eval_linearForm]

end LinearFormBridge

section BetaProgram

variable {D : ℕ} {K R : Type*}

/-- Compute the residue dot product and apply the supplied lift function.
No section is chosen by an existence theorem inside this definition. -/
def beta [Zero K] [Add K] [Mul K] (lift : K → R) (row x : Fin D → K) : R :=
  lift (dotWithCost row x).1

theorem beta_eq_lift_sum [Semiring K] (lift : K → R) (row x : Fin D → K) :
    beta lift row x = lift (∑ i, row i * x i) := by
  rw [beta, dotWithCost_value]

/-- Compose the explicit dot-product program with an instrumented scalar
backend lift. The backend's own returned cost remains visible. -/
def betaWithCost [Zero K] [Add K] [Mul K]
    (liftCode : K → R × ℕ) (row x : Fin D → K) : R × ℕ :=
  let residue := dotWithCost row x
  let lifted := liftCode residue.1
  (lifted.1, residue.2 + lifted.2)

theorem betaWithCost_value [Zero K] [Add K] [Mul K]
    (liftCode : K → R × ℕ) (lift : K → R)
    (hlift : ∀ y, (liftCode y).1 = lift y) (row x : Fin D → K) :
    (betaWithCost liftCode row x).1 = beta lift row x :=
  hlift _

theorem betaWithCost_cost [Zero K] [Add K] [Mul K]
    (liftCode : K → R × ℕ) (row x : Fin D → K) :
    (betaWithCost liftCode row x).2 =
      2 * D + (liftCode (dotWithCost row x).1).2 := by
  simp [betaWithCost]

theorem betaWithCost_cost_le [Zero K] [Add K] [Mul K]
    (liftCode : K → R × ℕ) (B : ℕ)
    (hcost : ∀ y, (liftCode y).2 ≤ B) (row x : Fin D → K) :
    (betaWithCost liftCode row x).2 ≤ 2 * D + B := by
  rw [betaWithCost_cost]
  exact Nat.add_le_add_left (hcost _) _

end BetaProgram

section BetaLinearForm

variable {D : ℕ} {K R : Type*} [CommSemiring K]

theorem beta_eq_lift_eval_linearForm (lift : K → R) (row x : Fin D → K) :
    beta lift row x =
      lift (MvPolynomial.eval x (WeightedSupport.linearForm Finset.univ row)) := by
  rw [beta, dotWithCost_eq_eval_linearForm]

end BetaLinearForm

section ResidueCompatibility

variable {D : ℕ} {R K : Type*} [CommSemiring R] [CommSemiring K]

/-- Dot products commute with the supplied residue-ring homomorphism. -/
theorem map_dotWithCost (ρ : R →+* K) (row x : Fin D → R) :
    ρ (dotWithCost row x).1 =
      (dotWithCost (fun i => ρ (row i)) (fun i => ρ (x i))).1 := by
  simp only [dotWithCost_value, map_sum, map_mul]

/-- Coefficientwise and input-coordinate lifts give exactly the expected
residue dot product. The hypotheses are concrete pointwise lift equalities. -/
theorem reduce_eval_linearForm (ρ : R →+* K)
    (rowLift inputLift : Fin D → R) (row x : Fin D → K)
    (hrow : ∀ i, ρ (rowLift i) = row i)
    (hx : ∀ i, ρ (inputLift i) = x i) :
    ρ (MvPolynomial.eval inputLift
      (WeightedSupport.linearForm Finset.univ rowLift)) =
      (dotWithCost row x).1 := by
  rw [← dotWithCost_eq_eval_linearForm, map_dotWithCost]
  simp only [hrow, hx]

/-- The computed beta is exactly the chosen lift of the lifted row's residue. -/
theorem beta_eq_lift_reduced_eval (ρ : R →+* K) (lift : K → R)
    (rowLift inputLift : Fin D → R) (row x : Fin D → K)
    (hrow : ∀ i, ρ (rowLift i) = row i)
    (hx : ∀ i, ρ (inputLift i) = x i) :
    beta lift row x =
      lift (ρ (MvPolynomial.eval inputLift
        (WeightedSupport.linearForm Finset.univ rowLift))) := by
  rw [reduce_eval_linearForm ρ rowLift inputLift row x hrow hx]
  rfl

theorem reduce_beta (ρ : R →+* K) (lift : K → R)
    (hsection : ∀ y, ρ (lift y) = y) (row x : Fin D → K) :
    ρ (beta lift row x) = (dotWithCost row x).1 :=
  hsection _

end ResidueCompatibility

section Defect

variable {D : ℕ} {R K : Type*} [CommRing R] [CommRing K]

/-- The beta computed by the program has the required zero-residue defect. -/
theorem beta_defect_residue_zero (ρ : R →+* K) (lift : K → R)
    (hsection : ∀ y, ρ (lift y) = y)
    (rowLift inputLift : Fin D → R) (row x : Fin D → K)
    (hrow : ∀ i, ρ (rowLift i) = row i)
    (hx : ∀ i, ρ (inputLift i) = x i) :
    ρ (MvPolynomial.eval inputLift
      (WeightedSupport.linearForm Finset.univ rowLift) - beta lift row x) = 0 := by
  rw [map_sub, reduce_eval_linearForm ρ rowLift inputLift row x hrow hx,
    reduce_beta ρ lift hsection, sub_self]

/-- Any independently verified kernel-as-divisibility theorem now supplies
the local p-divisibility premise used by the symbolic counting backend. -/
theorem beta_defect_dvd (ρ : R →+* K) (lift : K → R)
    (hsection : ∀ y, ρ (lift y) = y) (p : R)
    (hkernel : ∀ y, ρ y = 0 → p ∣ y)
    (rowLift inputLift : Fin D → R) (row x : Fin D → K)
    (hrow : ∀ i, ρ (rowLift i) = row i)
    (hx : ∀ i, ρ (inputLift i) = x i) :
    p ∣ MvPolynomial.eval inputLift
      (WeightedSupport.linearForm Finset.univ rowLift) - beta lift row x :=
  hkernel _ (beta_defect_residue_zero ρ lift hsection rowLift inputLift row x hrow hx)

end Defect

end SubexponentialSAT.SubexpInputCode

end OAI.Algorithms
