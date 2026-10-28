import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost
import OAI.Algorithms.SubexponentialSAT.SubexpCanonicalWords

namespace OAI.Algorithms

/-! Exact coefficient bytes are independent of scan order after normalized
modular arithmetic. This connects the machine's prepend-based pair loop to
the source evaluator without assigning algebraic laws to raw bit vectors. -/

namespace SubexponentialSAT.SubexpCanonicalDense

open SymbolicCost SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing
open SubexpCanonicalWords

def decoded {D : ℕ} {C R : Type*} (decode : C → R) (P : CoeffList D C) : CoeffList D R :=
  P.map fun term => (term.1, decode term.2)

theorem coeff_reverse {D : ℕ} {R : Type*} [CommSemiring R]
    (P : CoeffList D R) (a : RawIndex D) : coeff P.reverse a = coeff P a := by
  induction P with
  | nil => rfl
  | cons term P ih =>
    rcases term with ⟨b,c⟩
    simp [List.reverse_cons, coeff_append, coeff, ih, add_comm]

theorem programRow_output {D : ℕ} {C : Type*} (ops : RingProgram C)
    (p : RawIndex D × C) (Q : CoeffList D C) :
    (programRow ops p Q).1 = Q.map (fun q => (p.1 + q.1, (ops.mulRun p.2 q.2).1)) := by
  induction Q with
  | nil => rfl
  | cons q Q ih => simp only [programRow, List.map_cons, ih]

theorem programRawMul_output {D : ℕ} {C : Type*} (ops : RingProgram C)
    (P Q : CoeffList D C) :
    (programRawMul ops P Q).1 =
      P.flatMap (fun p => Q.map (fun q => (p.1 + q.1, (ops.mulRun p.2 q.2).1))) := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    simp only [programRawMul, appendWithCost_eq, List.flatMap_cons, programRow_output, ih]

section Prepared

variable (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t z o : QuarticCode p D)

theorem scan_canonical (hz : CanonicalQuad p (D+1) z)
    (P : CoeffList D (QuarticCode p D)) (a : RawIndex D) :
    CanonicalQuad p (D+1) (programScan (preparedProgram p D M t z o) P a).1 := by
  induction P with
  | nil => exact hz
  | cons term P ih =>
    rcases term with ⟨b, c⟩
    by_cases h : b = a
    · simp only [programScan, h, ite_true, preparedProgram]
      exact binaryAdd_canonical p (D+1) M _ _
    · simpa only [programScan, h, ite_false] using ih

theorem scan_quotient (c : Fin 4 → ZMod (p^(D+1)))
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (P : CoeffList D (QuarticCode p D)) (a : RawIndex D) :
    quotientDenote c ((programScan (preparedProgram p D M t z o) P a).1.map
      (wordValue p (D+1))) =
      coeff (decoded (fun v => quotientDenote c (v.map (wordValue p (D+1)))) P) a := by
  induction P with
  | nil => simpa [programScan, preparedProgram, coeff, decoded] using hz
  | cons term P ih =>
    rcases term with ⟨b, value⟩
    by_cases h : b = a
    · simp only [programScan, h, ite_true, preparedProgram,
        SubexpPreparedQuartic.binaryAdd_quotient, decoded, List.map_cons, coeff]
      exact congrArg (fun v => quotientDenote c (value.map (wordValue p (D+1))) + v) ih
    · simpa only [programScan, h, ite_false, decoded, List.map_cons, coeff, zero_add] using ih

theorem scan_reverse (c : Fin 4 → ZMod (p^(D+1)))
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P : CoeffList D (QuarticCode p D)) (a : RawIndex D) :
    (programScan (preparedProgram p D M t z o) P.reverse a).1 =
      (programScan (preparedProgram p D M t z o) P a).1 := by
  apply quad_eq_of_quotient_eq p (D+1) (Nat.zero_lt_succ D) c
  · exact scan_canonical p D M t z o hcanonical P.reverse a
  · exact scan_canonical p D M t z o hcanonical P a
  · rw [scan_quotient p D M t z o c hz, scan_quotient p D M t z o c hz]
    rw [decoded, List.map_reverse, coeff_reverse]
    rfl

theorem project_reverse (c : Fin 4 → ZMod (p^(D+1)))
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) :
    (programProject (preparedProgram p D M t z o) slots P.reverse).1 =
      (programProject (preparedProgram p D M t z o) slots P).1 := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
    simp only [programProject, scan_reverse p D M t z o c hz hcanonical, ih]

/-- The prepend-based machine may enumerate its pair records in reverse
order and still produce the exact source-level multiplication output. -/
theorem reversed_pairs_mul (c : Fin 4 → ZMod (p^(D+1)))
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) :
    (programProject (preparedProgram p D M t z o) slots
      (P.flatMap (fun a => Q.map (fun b =>
        (a.1 + b.1, (SubexpPreparedQuartic.binaryMul p (D+1) M t a.2 b.2).1)))).reverse).1 =
      (programMul (preparedProgram p D M t z o) slots P Q).1 := by
  rw [project_reverse p D M t z o c hz hcanonical]
  simp only [programMul, programRawMul_output, preparedProgram]

end Prepared

end SubexponentialSAT.SubexpCanonicalDense

end OAI.Algorithms
