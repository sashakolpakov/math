import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowLookup
import OAI.Algorithms.SubexponentialSAT.SubexpRowToTaylorCalls

namespace OAI.Algorithms

/-! Compose actual source-code preparation with the complete source-field
polynomial evaluator and coefficient lift. The only changed caller stack is
87, which holds the reversed full row expected by the table writer. -/

namespace SubexponentialSAT.SubexpGlobalRowEvaluation

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpGlobalRowBranch SubexpGlobalRowLookup
  SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (physicalCfg contextStore)

abbrev Expression (p : ℕ) := Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))

theorem code_literal {p : ℕ} (c : SubexpRowPolynomialCalls.Coefficient p 1) :
    SubexpRowToTaylorCalls.code (.lit [c]) = literalWord (SubexpFlatAdd.encode c) := by
  simp [SubexpRowToTaylorCalls.code, Algorithm.Expr.compile,
    SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
    SubexpRowPolynomialCalls.encode, SubexpConvolutionControl.encodeArray, literalWord]

def result (a : Data) (regs : Fin 25 → Bool) (output : Word) : Data :=
  ⟨regs, Function.update a.stacks 87 output⟩

theorem physical_code_store (code : Word) (context : Fin 252 → Word) :
    (physicalCfg (l := 1) none false false false code [] [] context).stacks =
      Function.update (contextStore context) 26 code := by
  funext i
  by_cases h26 : i = 26
  · subst i; simp
  by_cases h28 : i = 28
  · subst i; simp [contextStore]
  by_cases h27 : i = 27
  · subst i; simp [contextStore]
  simpa [h26] using
    SubexpRowPostfixInterpreter.physicalCfg_frame (l := 1) none false false false
      code [] [] context i h26 h28 h27

def contextOf (a : Data) (j : Fin 252) : Word :=
  a.stacks (SubexpRowToTaylorCalls.stack
    (SubexpRowPostfixInterpreter.ports (Fin.natAdd 4 j)))

/-- The interpreter frame is extracted from the actual caller state. Only
its four concrete control stacks need to be empty. -/
theorem contextOf_store (a : Data) (h26 : a.stacks 26 = []) (h27 : a.stacks 27 = [])
    (h28 : a.stacks 28 = []) (h29 : a.stacks 29 = []) :
    ∀ i, a.stacks (SubexpRowToTaylorCalls.stack i) = contextStore (contextOf a) i := by
  intro i
  obtain ⟨j, rfl⟩ := SubexpRowPostfixInterpreter.ports.surjective i
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro j
    fin_cases j
    · change a.stacks 26 = []; exact h26
    · change a.stacks 28 = []; exact h28
    · change a.stacks 27 = []; exact h27
    · change a.stacks 29 = []; exact h29
  · intro j
    exact (SubexpRowPostfixInterpreter.physicalCfg_context (l := 1) none false false false
      [] [] [] (contextOf a) j).symm

theorem prepared_layout (a b : Data) (code : Word) (context : Fin 252 → Word)
    (ha : ∀ i, a.stacks (SubexpRowToTaylorCalls.stack i) = contextStore context i)
    (hb : b.stacks = Function.update a.stacks 26 code) :
    ∀ i, b.stacks (SubexpRowToTaylorCalls.stack i) =
      (physicalCfg (l := 1) none false false false code [] [] context).stacks i := by
  intro i
  rw [hb, physical_code_store]
  by_cases hi : i = 26
  · subst i; simp [SubexpRowToTaylorCalls.stack]
  · have hi' : SubexpRowToTaylorCalls.stack i ≠ 26 := by
      intro heq
      apply hi
      apply Fin.ext
      exact congrArg (fun j : Fin 288 => j.val) heq
    simp [hi, hi', ha i]

theorem final_store (a b : Data) (code output : Word) (rf : Fin 16 → Bool)
    (h26 : a.stacks 26 = []) (hb : b.stacks = Function.update a.stacks 26 code) :
    (SubexpRowToTaylorCalls.finished b rf output).stacks = Function.update a.stacks 87 output := by
  funext i
  by_cases h87 : i = 87
  · subst i; simp
  by_cases hi26 : i = 26
  · subst i; simp [h26]
  rw [SubexpRowToTaylorCalls.finished_frame b rf output i hi26 h87, hb]
  simp [hi26, h87]

variable (p μ : ℕ) [Fact p.Prime] (source : SubexpSelectedConversions.Prepared p 0) (R : ℕ)
variable (sw tw : Word) (frame : Fin 6 → Word) (context : Fin 252 → Word)

/-- A prepared source trace is followed by the actual fixed evaluator.
The full degree-R coefficient array is retained and lifted before any Taylor
truncation. No annotation is substituted for an arithmetic execution. -/
theorem row_after_prepare (universal : Code) (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ) (e : Expression p) (a b : Data) (n : ℕ)
    (ha : ∀ i, a.stacks (SubexpRowToTaylorCalls.stack i) = contextStore context i)
    (hprepare : Eval (prepare universal) n a b)
    (hb : b.stacks = Function.update a.stacks 26 (SubexpRowToTaylorCalls.code e)) :
    ∃ m ≤ n + 16 + SubexpRowToTaylor.runtimeBound R (baseWidth p 1) (baseWidth p μ)
      (SubexpRowToTaylorCalls.code e).length, ∃ regs,
      Eval (row universal SubexpRowToTaylorCalls.command) m a
        (result a regs (SubexpRowToTaylorCalls.output μ source R e)) := by
  have h26 : a.stacks 26 = [] := by
    simpa [SubexpRowToTaylorCalls.stack, contextStore] using ha 26
  obtain ⟨m, rf, hm, heval⟩ := SubexpRowToTaylorCalls.command_eval p μ source R sw tw frame context
    hμ H hz h74 h87 hB e b (prepared_layout a b _ context ha hb)
  let last := SubexpRowToTaylorCalls.finished b rf (SubexpRowToTaylorCalls.output μ source R e)
  have hlast : last = result a last.regs (SubexpRowToTaylorCalls.output μ source R e) :=
    congrArg (StructuredProgram.State.mk last.regs)
      (final_store a b _ _ rf h26 hb)
  have hrun := hprepare.seq heval
  change Eval (row universal SubexpRowToTaylorCalls.command) (n + m) a last at hrun
  rw [hlast] at hrun
  exact ⟨n + m, by omega, last.regs, hrun⟩

theorem output_length (e : Expression p) :
    (SubexpRowToTaylorCalls.output μ source R e).length = (R + 1) * (4 * baseWidth p μ) :=
  SubexpRowToTaylorCalls.output_length μ source R e

end SubexponentialSAT.SubexpGlobalRowEvaluation

end OAI.Algorithms
