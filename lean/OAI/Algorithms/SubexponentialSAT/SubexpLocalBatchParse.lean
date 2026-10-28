import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-!
# Preserving parsing of one local-basis batch

The master on stack 0 contains three consecutive frames: unary dimension,
unary kernel dimension, and the coordinate-major scalar table. This fixed
program copies and decodes those actual bytes, then computes the complement
dimension by one real pop for each item of the copied kernel dimension.

Outputs are stacks 1, 2, 3, and 4; scratch 5--11 is restored. Subtraction
saturates at zero, including when the second dimension exceeds the first.
-/

namespace SubexponentialSAT.SubexpLocalBatchParse

open BitProgram StructuredCalls
open Subexp.MatrixProgramSupport (copy copy_eval readWord readWord_eval)

abbrev Data := State 8 12
abbrev Code := Cmd 8 12

def unary (n : ℕ) : List Bool := List.replicate n true

def payload (N rank : ℕ) (table : List Bool) : List Bool :=
  Encoding.frame (unary N) ++ (Encoding.frame (unary rank) ++ Encoding.frame table)

def dropPorts : UnaryForPrograms.Ports 8 12 := ⟨5, 0, 1⟩
def dropOne : Code := .base (.atom (.pop 4 0 1))
def dropCounted : Code := UnaryForPrograms.forCmd dropPorts dropOne

abbrev dropped (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks 4).head?, Function.update d.stacks 4 (d.stacks 4).tail⟩

theorem dropOne_eval (d : Data) : Eval dropOne 1 d (dropped d) :=
  .base (.atom _ _)

/-- Exact control trace for arbitrary data and counter bits, including an
empty source. Popping an empty stack leaves it empty. -/
theorem drop_visits (counter bits : List Bool) (d : Data)
    (hc : d.stacks 5 = counter) (hs : d.stacks 4 = bits) :
    ∃ e, UnaryForPrograms.Visits dropPorts dropOne
        (List.replicate counter.length 1) (3 * counter.length + 2) d e ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 4
        (bits.drop counter.length) := by
  induction counter generalizing bits d with
  | nil =>
      refine ⟨UnaryForPrograms.popped dropPorts d, .done d hc, ?_⟩
      funext j
      by_cases hj : j = 4
      · subst j
        simp [UnaryForPrograms.popped, dropPorts, hs]
      · simp [UnaryForPrograms.popped, dropPorts, hj, hc]
  | cons bit counter ih =>
      let a := dropped (UnaryForPrograms.popped dropPorts d)
      have ha5 : a.stacks 5 = counter := by
        simp [a, UnaryForPrograms.popped, dropPorts, hc]
      have ha4 : a.stacks 4 = bits.tail := by
        simp [a, UnaryForPrograms.popped, dropPorts, hs]
      obtain ⟨e, he, hes⟩ := ih bits.tail a ha5 ha4
      have hv := UnaryForPrograms.Visits.step
        (p := dropPorts) (body := dropOne) (d := d)
        (by simp [dropPorts, hc]) (dropOne_eval (UnaryForPrograms.popped dropPorts d))
        (by simp [ dropPorts]) he
      have htime : 1 + (3 * counter.length + 2) + 2 =
          3 * (bit :: counter).length + 2 := by simp; omega
      rw [htime] at hv
      refine ⟨e, ?_, ?_⟩
      · simpa only [List.length_cons, List.replicate_succ] using hv
      · funext j
        by_cases hj4 : j = 4
        · subst j
          simp [hes, a, UnaryForPrograms.popped, dropPorts, List.drop_tail]
        · by_cases hj5 : j = 5
          · subst j
            simp [hes, a, UnaryForPrograms.popped, dropPorts]
          · simp [hes, a, UnaryForPrograms.popped, dropPorts, hj4, hj5]

theorem dropCounted_eval (counter bits : List Bool) (d : Data)
    (hc : d.stacks 5 = counter) (hs : d.stacks 4 = bits) :
    ∃ e, Eval dropCounted (3 * counter.length + 2) d e ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 4
        (bits.drop counter.length) := by
  obtain ⟨e, he, hes⟩ := drop_visits counter bits d hc hs
  exact ⟨e, he.eval, hes⟩

theorem subtract_eval (N rank : ℕ) (d : Data)
    (hc : d.stacks 5 = unary rank) (hs : d.stacks 4 = unary N) :
    ∃ e, Eval dropCounted (3 * rank + 2) d e ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 4 (unary (N - rank)) := by
  simpa only [unary, List.length_replicate, List.drop_replicate] using
    dropCounted_eval (unary rank) (unary N) d hc hs

local infixr:60 " ;; " => Cmd.seq

def command : Code :=
  copy 0 5 6 ;;
    readWord 5 1 6 (by decide) ;;
    readWord 5 2 6 (by decide) ;;
    readWord 5 3 6 (by decide) ;;
    copy 1 4 6 ;;
    copy 2 5 6 ;;
    dropCounted

def program := compiled command 0 3

/-- All local output and scratch stacks are initially empty. -/
def Clean (d : Data) : Prop := ∀ i : Fin 12, i ≠ 0 → d.stacks i = []

abbrev resultStacks (d : Data) (N rank : ℕ) (table : List Bool) : Fin 12 → List Bool :=
  Function.update (Function.update (Function.update (Function.update d.stacks
    1 (unary N)) 2 (unary rank)) 3 table) 4 (unary (N - rank))

def cost (N rank : ℕ) (table : List Bool) : ℕ :=
  7 * (payload N rank table).length + 16 * N + 19 * rank + 9 * table.length + 38

/-- Parsing, copying, subtraction, and every internal return are counted. -/
theorem command_eval (N rank : ℕ) (table : List Bool) (d : Data)
    (hm : d.stacks 0 = payload N rank table) (clean : Clean d) :
    ∃ e, Eval command (cost N rank table) d e ∧
      e.stacks = resultStacks d N rank table := by
  obtain ⟨a, ha, has⟩ := copy_eval 0 5 6 (by decide) (by decide) (by decide)
    d (clean 6 (by decide))
  have ha5 : a.stacks 5 = payload N rank table := by
    simp [has, StackRoutines.copyStacks, hm, clean 5 (by decide)]
  obtain ⟨b, hb, hbs⟩ := readWord_eval 5 1 6 (by decide) (by decide) (by decide) a
    (unary N) (Encoding.frame (unary rank) ++ Encoding.frame table)
    ha5
    (by simp [has, StackRoutines.copyStacks, clean 1 (by decide)])
    (by simp [has, StackRoutines.copyStacks, clean 6 (by decide)])
  obtain ⟨c, hc, hcs⟩ := readWord_eval 5 2 6 (by decide) (by decide) (by decide) b
    (unary rank) (Encoding.frame table)
    (by simp [hbs])
    (by simp [hbs, has, StackRoutines.copyStacks, clean 2 (by decide)])
    (by simp [hbs, has, StackRoutines.copyStacks, clean 6 (by decide)])
  obtain ⟨e, he, hes⟩ := readWord_eval 5 3 6 (by decide) (by decide) (by decide) c
    table []
    (by simp [hcs])
    (by simp [hcs, hbs, has, StackRoutines.copyStacks, clean 3 (by decide)])
    (by simp [hcs, hbs, has, StackRoutines.copyStacks, clean 6 (by decide)])
  have he1 : e.stacks 1 = unary N := by simp [hes, hcs, hbs]
  have he2 : e.stacks 2 = unary rank := by simp [hes, hcs]
  have he4 : e.stacks 4 = [] := by
    simp [hes, hcs, hbs, has, StackRoutines.copyStacks, clean 4 (by decide)]
  have he5 : e.stacks 5 = [] := by simp [hes]
  have he6 : e.stacks 6 = [] := by
    simp [hes, hcs, hbs, has, StackRoutines.copyStacks, clean 6 (by decide)]
  obtain ⟨f, hf, hfs⟩ := copy_eval 1 4 6 (by decide) (by decide) (by decide) e he6
  have hf2 : f.stacks 2 = unary rank := by simp [hfs, StackRoutines.copyStacks, he2]
  have hf4 : f.stacks 4 = unary N := by
    simp [hfs, StackRoutines.copyStacks, he1, he4]
  have hf5 : f.stacks 5 = [] := by simp [hfs, StackRoutines.copyStacks, he5]
  have hf6 : f.stacks 6 = [] := by simp [hfs, StackRoutines.copyStacks, he6]
  obtain ⟨g, hg, hgs⟩ := copy_eval 2 5 6 (by decide) (by decide) (by decide) f hf6
  have hg4 : g.stacks 4 = unary N := by simp [hgs, StackRoutines.copyStacks, hf4]
  have hg5 : g.stacks 5 = unary rank := by
    simp [hgs, StackRoutines.copyStacks, hf2, hf5]
  obtain ⟨z, hz, hzs⟩ := subtract_eval N rank g hg5 hg4
  have total := ha.seq (hb.seq (hc.seq (he.seq (hf.seq (hg.seq hz)))))
  refine ⟨z, ?_, ?_⟩
  · convert total using 1
    · rfl
    · simp only [hm, he1, hf2, unary, List.length_replicate, cost]
      omega
  · funext j
    fin_cases j <;>
      simp [resultStacks, hzs, hgs, hfs, hes, hcs, hbs, has, StackRoutines.copyStacks,
        clean 4 (by decide), clean 5 (by decide)]

theorem cost_le_payload (N rank : ℕ) (table : List Bool) :
    cost N rank table ≤ 17 * (payload N rank table).length + 8 := by
  simp only [cost, payload, List.length_append, Encoding.length_frame,
    unary, List.length_replicate]
  omega

theorem resultStacks_master (d : Data) (N rank : ℕ) (table : List Bool) :
    resultStacks d N rank table 0 = d.stacks 0 := by simp [resultStacks]

theorem resultStacks_scratch (d : Data) (N rank : ℕ) (table : List Bool)
    (i : Fin 12) (hi : 5 ≤ i.val) :
    resultStacks d N rank table i = d.stacks i := by
  have h1 : i ≠ 1 := by intro h; subst i; omega
  have h2 : i ≠ 2 := by intro h; subst i; omega
  have h3 : i ≠ 3 := by intro h; subst i; omega
  have h4 : i ≠ 4 := by intro h; subst i; omega
  simp [resultStacks, h1, h2, h3, h4]

/-- Complete execution has a linear bound in the actual preserved payload. -/
theorem program_run (N rank : ℕ) (table : List Bool) (d : Data)
    (hm : d.stacks 0 = payload N rank table) (clean : Clean d) :
    ∃ e : Data, RunsIn program (17 * (d.stacks 0).length + 9)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = resultStacks d N rank table := by
  obtain ⟨e, he, hes⟩ := command_eval N rank table d hm clean
  have hc := cost_le_payload N rank table
  refine ⟨e, ⟨cost N rank table + 1, ?_, compiled_halt_trace he 0 3⟩, hes⟩
  rw [hm]
  omega

end SubexponentialSAT.SubexpLocalBatchParse

end OAI.Algorithms
