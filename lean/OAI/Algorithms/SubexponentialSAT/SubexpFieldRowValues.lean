import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldRowProgram
import OAI.Algorithms.SubexponentialSAT.SubexpBasePValues

namespace OAI.Algorithms

/-!
# Numeric row values for the concrete field-candidate program

This specification records both order conventions: the first scope coordinate
is the least-significant base-p digit, and the enumerator prepends each Boolean
value to its output. Leading zeroes in the current-rank word are immaterial.
-/

namespace SubexponentialSAT.SubexpFieldRowValues

open BitProgram StructuredCalls BinaryArithmetic
open SubexpFieldRowProgram (Masters)

def labels (m : Masters) (rank : ℕ) : List (List Bool) :=
  (SubexpBasePUnranking.numericDigits (BinaryArithmetic.toNat m.modulus) m.arity.length rank).map
    (SubexpLiftRing.fixedBits m.modulus.length)

def jobs {D : ℕ} (m : Masters) (scope : List (Fin D)) (rank : ℕ) :
    List (Fin D × List Bool) := scope.zip (labels m rank)

def result {D : ℕ} (m : Masters) (scope : List (Fin D)) (rank : ℕ) : List (List Bool) × Bool :=
  SubexpScopeMaterializer.materialize m.ell.length (jobs m scope rank)
    (SubexpFieldRowProgram.zeroChunks D m.ell.length) true

def value {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (rank : ℕ) : Bool :=
  let r := result m scope rank
  let array := r.1.flatten
  (r.2 && SubexpFactorProgram.allZero (array.drop n)) &&
    ls.any (fun l => l.eval (fun i => (array.take n)[i.val]?.getD false))

theorem jobsFor_eq {D : ℕ} (m : Masters) (scope : List (Fin D))
    (hm : 0 < BinaryArithmetic.toNat m.modulus) :
    SubexpFieldRowProgram.jobsFor m scope = jobs m scope (BinaryArithmetic.toNat m.rank) := by
  simp only [SubexpFieldRowProgram.jobsFor, jobs, labels,
    SubexpBasePValues.digitWords_eq_numeric m.modulus m.rank m.arity.length hm]

private theorem wordAssignment_eq_getD {n : ℕ} (word : List Bool) (hlen : word.length = n) :
    SubexpClauseRowProgram.wordAssignment word hlen = fun i => word[i.val]?.getD false := by
  funext i
  have hi : i.val < word.length := by omega
  simp only [SubexpClauseRowProgram.wordAssignment, List.getElem?_eq_getElem hi,
    Option.getD_some]

/-- A concrete row execution with an output specified solely by numeric rank.
There is no remaining callback execution or semantic-test hypothesis. -/
theorem command_eval {D n : ℕ} (regs : Fin 8 → Bool) (m : Masters)
    (scope : List (Fin D)) (ls : List (SAT.Literal (Fin n)))
    (hm : 0 < BinaryArithmetic.toNat m.modulus) (hcount : scope.length = m.arity.length)
    (hwidth : m.width.length = m.modulus.length) (hell : m.ell.length ≤ m.width.length)
    (hfull : m.fullShape.length = D * m.ell.length)
    (hnshape : m.nShape.length = n) (hn : n ≤ m.fullShape.length)
    (hscope : m.scope = Encoding.encodeList Encoding.encodeNat (scope.map Fin.val))
    (hclause : m.clause = SubexpClauseRowProgram.clauseBytes ls) :
    ∃ t ≤ SubexpFieldRowProgram.rowBudget m (jobs m scope (BinaryArithmetic.toNat m.rank)) ls,
      Eval SubexpFieldRowProgram.command t
        (SubexpFieldRowProgram.data regs m [] [] [] [] [] [])
        (SubexpFieldRowProgram.data SubexpFieldRowProgram.zeroRegs
          {m with output := value m scope ls (BinaryArithmetic.toNat m.rank) :: m.output}
          [] [] [] [] [] []) := by
  obtain ⟨hlen, t, ht, he⟩ := SubexpFieldRowProgram.command_eval regs m
    (SubexpFieldRowProgram.jobsFor m scope) ls
    (SubexpFieldRowProgram.jobsFor_words m scope hcount) hwidth hell hfull hnshape hn
    (hscope.trans (SubexpFieldRowProgram.jobsFor_scope m scope hcount).symm) hclause
  rw [wordAssignment_eq_getD _ hlen] at he
  rw [jobsFor_eq m scope hm] at ht he
  exact ⟨t, ht, he⟩

/-- The corresponding run of the finite instruction table. -/
theorem program_runsIn {D n : ℕ} (regs : Fin 8 → Bool) (m : Masters)
    (scope : List (Fin D)) (ls : List (SAT.Literal (Fin n)))
    (hm : 0 < BinaryArithmetic.toNat m.modulus) (hcount : scope.length = m.arity.length)
    (hwidth : m.width.length = m.modulus.length) (hell : m.ell.length ≤ m.width.length)
    (hfull : m.fullShape.length = D * m.ell.length)
    (hnshape : m.nShape.length = n) (hn : n ≤ m.fullShape.length)
    (hscope : m.scope = Encoding.encodeList Encoding.encodeNat (scope.map Fin.val))
    (hclause : m.clause = SubexpClauseRowProgram.clauseBytes ls) :
    RunsIn SubexpFieldRowProgram.program
      (SubexpFieldRowProgram.rowBudget m (jobs m scope (BinaryArithmetic.toNat m.rank)) ls + 1)
      ((SubexpFieldRowProgram.data regs m [] [] [] [] [] []).withPC
        (some SubexpFieldRowProgram.program.entry))
      ((SubexpFieldRowProgram.data SubexpFieldRowProgram.zeroRegs
        {m with output := value m scope ls (BinaryArithmetic.toNat m.rank) :: m.output}
        [] [] [] [] [] []).withPC none) := by
  obtain ⟨t, ht, he⟩ := command_eval regs m scope ls hm hcount hwidth hell hfull
    hnshape hn hscope hclause
  exact ⟨t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 19 29⟩

end SubexponentialSAT.SubexpFieldRowValues

end OAI.Algorithms
