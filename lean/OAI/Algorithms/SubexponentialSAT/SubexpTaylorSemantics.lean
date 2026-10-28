import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorControl
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial

namespace OAI.Algorithms

/-! The compact affine sweep computes exactly the shifted polynomial.
Only redundant trailing zero coefficients differ from the earlier dense
Horner implementation. -/

namespace SubexponentialSAT.SubexpTaylorSemantics

open SubexpTaylorControl

def compactShift {C : Type*} (step : C → C → C) : List C → List C
  | [] => []
  | b :: P => sweep step b (compactShift step P)

@[simp] theorem compactShift_length {C : Type*} (step : C → C → C) (P : List C) :
    (compactShift step P).length = P.length := by
  induction P with
  | nil => rfl
  | cons b P ih => simp [compactShift, ih]

theorem map_sweep {C R : Type*} (decode : C → R) (step : C → C → C)
    (operation : R → R → R)
    (hstep : ∀ a b, decode (step a b) = operation (decode a) (decode b))
    (b : C) (P : List C) :
    (sweep step b P).map decode = sweep operation (decode b) (P.map decode) := by
  induction P generalizing b with
  | nil => rfl
  | cons a P ih => simp [sweep, hstep, ih]

theorem denote_sweep {R : Type*} [CommRing R] (theta b : R) (P : List R) :
    PolynomialAlgorithm.denote (sweep (fun a b => a * theta + b) b P) =
      Polynomial.C b + (Polynomial.X + Polynomial.C theta) * PolynomialAlgorithm.denote P := by
  induction P generalizing b with
  | nil => simp [sweep, PolynomialAlgorithm.denote]
  | cons a P ih =>
      simp only [sweep, PolynomialAlgorithm.denote_cons, ih, map_add, map_mul]
      ring

theorem compactShift_decode {C R : Type*} [CommRing R]
    (decode : C → R) (step : C → C → C) (theta : R)
    (hstep : ∀ a b, decode (step a b) = decode a * theta + decode b)
    (P : List C) :
    PolynomialAlgorithm.denote ((compactShift step P).map decode) =
      (PolynomialAlgorithm.denote (P.map decode)).comp (Polynomial.X + Polynomial.C theta) := by
  induction P with
  | nil => simp [compactShift]
  | cons b P ih =>
      rw [compactShift, map_sweep decode step (fun a b => a * theta + b) hstep,
        denote_sweep, ih]
      simp only [List.map_cons, PolynomialAlgorithm.denote_cons, Polynomial.add_comp,
        Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]

/-- Every coefficient agrees with the existing callback implementation,
even though that implementation retains additional trailing zero slots. -/
theorem compactShift_coeff_eq_shiftProgram {C R : Type*} [CommRing R]
    (ops : SubexpSymbolicCost.RepresentedRing C R) (step : C → C → C) (theta : C)
    (hstep : ∀ a b, ops.decode (step a b) = ops.decode a * ops.decode theta + ops.decode b)
    (P : List C) (j : ℕ) :
    (PolynomialAlgorithm.denote ((compactShift step P).map ops.decode)).coeff j =
      (PolynomialAlgorithm.denote
        ((SubexpDensePolynomial.shiftProgram ops.program theta P).1.map ops.decode)).coeff j := by
  rw [compactShift_decode ops.decode step (ops.decode theta) hstep,
    SubexpDensePolynomial.shiftProgram_run]
  change _ = (PolynomialAlgorithm.denote
    (SubexpDensePolynomial.decodeList ops (SubexpDensePolynomial.shiftRun ops theta P).1)).coeff j
  rw [SubexpDensePolynomial.shiftRun_correct, PolynomialAlgorithm.denote_shift]
  rfl

end SubexponentialSAT.SubexpTaylorSemantics

end OAI.Algorithms
