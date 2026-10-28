import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgramLookup

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable (p t : ℕ) [Fact p.Prime]

def Canonical (v:Values p t) : Prop := ∀i,BinaryArithmetic.toNat (v i).val < p^t

theorem op_canonical (M:SubexpPreparedQuartic.Modulus p t) (v:Values p t)
    (op:Op) (h:Canonical p t v) : Canonical p t (op.eval p t M v) := by
  intro i
  cases op with
  | add o l r =>
      by_cases hi:i=o
      · subst i; simpa [Op.eval] using SubexpPreparedQuartic.wordAdd_canonical p t M (v l) (v r)
      · simpa [Op.eval,hi] using h i
  | mul o l r =>
      by_cases hi:i=o
      · subst i; simpa [Op.eval] using RingProgram.wordMul_canonical p t M (v l) (v r)
      · simpa [Op.eval,hi] using h i

theorem run_canonical (M:SubexpPreparedQuartic.Modulus p t) (v:Values p t)
    (ops:List Op) (h:Canonical p t v) : Canonical p t (run p t M ops v) := by
  induction ops generalizing v with
  | nil=>exact h
  | cons a as ih=>exact ih _ (op_canonical p t M v a h)

theorem iterate_canonical (M:SubexpPreparedQuartic.Modulus p t) (v:Values p t)
    (n:ℕ) (h:Canonical p t v) : Canonical p t (iterateForward p t M v n) := by
  induction n with
  | zero=>exact h
  | succ n ih=>exact run_canonical p t M _ _ ih

theorem final_canonical (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h:Canonical 3 t v) : Canonical 3 t (finalValues t M v) :=
  run_canonical 3 t M _ _ (iterate_canonical 3 t M _ _ (run_canonical 3 t M _ _ h))

theorem final_preserves (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h8:decode 3 t v 8=1) (h9:decode 3 t v 9 = -1)
    (i:Reg) (hi6:i≠6) (hi7:i≠7) (hi8:i≠8) (hi10:i≠10) (hi11:i≠11) :
    decode 3 t (run 3 t M finalCoefficients (iterateForward 3 t M v t)) i=decode 3 t v i := by
  rw [decode_run]
  have hh:=iterate_half 3 t M v h8 h9 t
  rw [(final_algebra (decode 3 t (iterateForward 3 t M v t)) hh.2.1).2.2 i hi6 hi10 hi11]
  exact hh.2.2 i hi6 hi7 hi8

def smallInteger : Fin 6→ℤ := ![0,1,-2,3,-6,7]

theorem final_small (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h0:decode 3 t v 0=0) (h1:decode 3 t v 1=1) (h9:decode 3 t v 9 = -1) :
    ∀i:Fin 6,decode 3 t (finalValues t M v) (i.castAdd 6)=(smallInteger i:ZMod (3^t)) := by
  have hc:=constants_algebra (decode 3 t v) h0 h1 h9
  rw [←decode_run 3 t M constants v] at hc
  intro i
  have hp:=final_preserves t M (run 3 t M constants v) hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
    (i.castAdd 6) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
  change decode 3 t (finalValues t M v) (i.castAdd 6)=_ at hp
  rw [hp]
  fin_cases i
  · simpa [smallInteger] using hc.1
  · simpa [smallInteger] using hc.2.1
  · simpa [smallInteger] using hc.2.2.1
  · simpa [smallInteger] using hc.2.2.2.1
  · simpa [smallInteger] using hc.2.2.2.2.1
  · simpa [smallInteger] using hc.2.2.2.2.2.1

theorem final_half (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h0:decode 3 t v 0=0) (h1:decode 3 t v 1=1) (h9:decode 3 t v 9 = -1) :
    2*decode 3 t (finalValues t M v) 8=1 ∧
    decode 3 t (finalValues t M v) 9 = -1 := by
  have hc:=constants_algebra (decode 3 t v) h0 h1 h9
  rw [←decode_run 3 t M constants v] at hc
  have hi:=half_inverse t M (run 3 t M constants v) hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
  have hn:decode 3 t (iterateForward 3 t M (run 3 t M constants v) t) 9 = -1 :=
    (iterate_half 3 t M _ hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2 t).2.1
  simpa [finalValues,run,finalCoefficients,Op.eval,decode] using And.intro hi hn

/-- These exact bytes are the coefficient words requested by the array builder. -/
theorem final_coefficients (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t) :
    let w:=finalValues t M v
    w 10=(SubexpPreparedQuartic.wordAdd 3 t M (w 8) (w 8)).1 ∧
    w 11=(SubexpPreparedQuartic.wordMul 3 t M
      (SubexpPreparedQuartic.wordAdd 3 t M (w 10) (w 8)).1 (w 9)).1 := by
  simp [finalValues,run,finalCoefficients,Op.eval]

def generatedCache (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h0:decode 3 t v 0=0) (h1:decode 3 t v 1=1) (h9:decode 3 t v 9 = -1) :
    RingProgram.ScalarCache 3 t where
  zero := finalValues t M v 0
  one := finalValues t M v 1
  minusOne := finalValues t M v 9
  zero_correct := by simpa [decode,smallInteger] using final_small t M v h0 h1 h9 0
  one_correct := by simpa [decode,smallInteger] using final_small t M v h0 h1 h9 1
  minusOne_correct := (final_half t M v h0 h1 h9).2

def tableRegister : Fin 6→Reg := ![0,1,3,2,4,5]

theorem generated_table (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h0:decode 3 t v 0=0) (h1:decode 3 t v 1=1) (h9:decode 3 t v 9 = -1)
    (hc:Canonical 3 t v) (i:Fin 6) :
    (IdempotentProgram.integerRun (RingProgram.scalarProgram 3 t M (generatedCache t M v h0 h1 h9))
      (IdempotentTableEntryProgram.codeValue i)).1 = finalValues t M v (tableRegister i) := by
  apply IdempotentProgram.integerRun_eq_of_value 3 t M _
    (final_canonical t M v hc 0) _ _ (final_canonical t M v hc _)
  have hh:=final_small t M v h0 h1 h9
  have hh' : ∀ i : Fin 6,
      wordValue 3 t (finalValues t M v (i.castAdd 6)) =
        (smallInteger i : ZMod (3 ^ t)) := by
    intro i
    simpa only [decode] using hh i
  fin_cases i
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 0
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 1
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 3
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 2
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 4
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 5

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
