import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramOutput

namespace OAI.Algorithms

/-! Algebraic invariant for the native descending Horner application. Each
coefficient digit has three entries, and no power is recomputed by expansion. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators

structure Triple (C : Type*) where
  a : C
  b : C
  c : C

variable {C A R : Type*} [CommRing A] [CommRing R]

def tripleValue (decode : C → A) (φ : A →+* R) (h : R) (v : Triple C) : R :=
  φ (decode v.a) + h * (φ (decode v.b) + h * φ (decode v.c))

def hornerValue (decode : C → A) (φ : A →+* R) (h g : R) : List (Triple C) → R
  | [] => 0
  | v::vs => tripleValue decode φ h v + g * hornerValue decode φ h g vs

def descendingValue (decode : C → A) (φ : A →+* R) (h g : R)
    (vs : List (Triple C)) (acc : R) : R :=
  vs.foldl (fun current v => tripleValue decode φ h v + g*current) acc

theorem descendingValue_reverse (decode : C → A) (φ : A →+* R) (h g : R)
    (vs : List (Triple C)) :
    descendingValue decode φ h g vs.reverse 0=hornerValue decode φ h g vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.reverse_cons,descendingValue,List.foldl_append,List.foldl_cons,
      List.foldl_nil,hornerValue]
    rw [←descendingValue,ih]

theorem hornerValue_ofFn (decode : C → A) (φ : A →+* R) (h g : R)
    (t : ℕ) (vs : Fin t → Triple C) :
    hornerValue decode φ h g (List.ofFn vs)=
      ∑ s : Fin t, tripleValue decode φ h (vs s)*g^s.val := by
  induction t with
  | zero => simp [hornerValue]
  | succ t ih =>
    rw [List.ofFn_succ,hornerValue,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring

def coefficientTriple (t : ℕ) (code : RingProgram.Code C (3*t)) (s : Fin t) : Triple C :=
  ⟨code (IdempotentProgram.digitIndex s 0),
   code (IdempotentProgram.digitIndex s 1),
   code (IdempotentProgram.digitIndex s 2)⟩

theorem coefficientTriple_value (ops : SubexpSymbolicCost.RepresentedRing C A)
    (φ : A →+* R) (h : R) (t : ℕ) (code : RingProgram.Code C (3*t)) (s : Fin t) :
    tripleValue ops.decode φ h (coefficientTriple t code s)=
      (IdempotentProgram.digitPolynomial ops code s).eval₂ φ h := by
  rw [IdempotentProgram.digitPolynomial_eval]
  simp [tripleValue,coefficientTriple,IdempotentProgram.digitValue,
    IdempotentProgram.digitCode,Fin.sum_univ_succ]
  ; ring

/-- Horner application equals the exact H-adic indicator polynomial, with U
combined into the Horner multiplier rather than expanded into stored powers. -/
theorem apply_coefficients (ops : SubexpSymbolicCost.RepresentedRing C A)
    (φ : A →+* R) (h u : R) (t : ℕ) (code : RingProgram.Code C (3*t)) :
    descendingValue ops.decode φ h (u*IdempotentProgram.hValue h)
      (List.ofFn (coefficientTriple t code)).reverse 0 =
      ∑ s : Fin t,
        u^s.val * (IdempotentProgram.digitPolynomial ops code s).eval₂ φ h *
          IdempotentProgram.hValue h^s.val := by
  rw [descendingValue_reverse,hornerValue_ofFn]
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficientTriple_value,mul_pow]
  ring

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
