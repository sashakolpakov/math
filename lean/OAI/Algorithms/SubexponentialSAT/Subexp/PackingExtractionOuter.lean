import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionBlock

namespace OAI.Algorithms

/-! The fixed outer loop extracts all complete blocks in block-major order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

theorem emitEntries_static (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).block = c.block ∧
    (emitEntries i entries c).buckets = c.buckets ∧
    (emitEntries i entries c).remaining = c.remaining := by
  induction entries generalizing c with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons e es ih =>
    simpa only [emitEntries, List.foldl_cons, emitted] using
      ih (emitted c e.1 (entryVertex i e))

def advanced (i : ℕ) (entries : List Entry) (c : Context) : Context :=
  let d := emitEntries i entries c
  { d with block := true :: d.block, remaining := d.remaining.tail }

theorem advanced_static (i : ℕ) (entries : List Entry) (c : Context) :
    (advanced i entries c).block = true :: c.block ∧
    (advanced i entries c).buckets = c.buckets ∧
    (advanced i entries c).remaining = c.remaining.tail := by
  obtain ⟨hb, ht, hr⟩ := emitEntries_static i entries c
  exact ⟨by simp [advanced, hb], by simp [advanced, ht], by simp [advanced, hr]⟩

abbrev refresh : Cmd 8 19 := .base (.atom (.peek 16 3 4))
abbrev popRemaining : Cmd 8 19 := .base (.atom (.pop 16 3 4))
def guard (regs : Fin 8 → Bool) (c : Context) : Data :=
  base (readRegs regs 3 4 c.remaining.head?) c

theorem refresh_eval (regs : Fin 8 → Bool) (c : Context) :
    Eval refresh 1 (base regs c) (guard regs c) := .base (.atom _ _)

theorem popRemaining_eval (regs : Fin 8 → Bool) (c : Context) :
    Eval popRemaining 1 (base regs c)
      (base (readRegs regs 3 4 c.remaining.head?) { c with remaining := c.remaining.tail }) := by
  have h : Eval popRemaining 1 (base regs c)
      ((StructuredProgram.Atom.pop (16 : Fin 19) (3 : Fin 8) 4).eval (base regs c)) :=
    .base (.atom _ _)
  have he : (StructuredProgram.Atom.pop (16 : Fin 19) (3 : Fin 8) 4).eval (base regs c) =
      base (readRegs regs 3 4 c.remaining.head?) { c with remaining := c.remaining.tail } := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    funext j
    fin_cases j <;> simp [base, ready, state, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  rw [he] at h
  exact h

abbrev body : Cmd 8 19 :=
  .seq (MatrixProgramSupport.copy 15 7 9)
    (.seq blockCommand (.seq (TupleProgram.pushConst 10 0 true) (.seq popRemaining refresh)))
abbrev loop : Cmd 8 19 := .while 4 body
abbrev command : Cmd 8 19 := .seq refresh loop
def program := compiled command 15 12

def bodyBudget (i : ℕ) (entries : List Entry) (c : Context) : ℕ :=
  7 * c.buckets.length + blockBudget i entries c + 12

theorem body_eval (i : ℕ) (entries : List Entry) (c : Context)
    (hblock : c.block = List.replicate i true)
    (hbuckets : c.buckets = ProgramEncoding.encodeRecords (entries.map entryWord))
    (hentries : ∀ e ∈ entries, i < e.2.length) (regs : Fin 8 → Bool) :
    ∃ n ≤ bodyBudget i entries c, ∃ rf,
      Eval body n (base regs c) (guard rf (advanced i entries c)) := by
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval (15 : Fin 19) 7 9
    (by decide) (by decide) (by decide) (base regs c) rfl
  have hea : a = ready a.regs { c with keys := c.buckets, payload := [] } := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext j
    fin_cases j <;> simp [base, ready, state, StackRoutines.copyStacks]
  rw [hea] at ha
  obtain ⟨nb, hnb, rb, hblockrun⟩ := blockCommand_eval i entries c hblock hentries a.regs []
  have hbr : Eval blockCommand nb
      (ready a.regs { c with keys := c.buckets, payload := [] })
      (base rb (emitEntries i entries c)) := by
    simpa only [hbuckets, List.append_nil, base] using hblockrun
  let d := emitEntries i entries c
  let pushed := { d with block := true :: d.block }
  let rp := Function.update rb (0 : Fin 8) true
  have hp : Eval (TupleProgram.pushConst 10 0 true) 2 (base rb d) (base rp pushed) := by
    have h := TupleProgram.pushConst_eval (10 : Fin 19) (0 : Fin 8) true (base rb d)
    have he : TupleProgram.pushedState 10 0 true (base rb d) = base rp pushed := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext j
      fin_cases j <;> rfl
    rw [he] at h
    exact h
  let rf := readRegs rp 3 4 d.remaining.head?
  have hpop : Eval popRemaining 1 (base rp pushed) (base rf (advanced i entries c)) :=
    popRemaining_eval rp pushed
  have hrefresh := refresh_eval rf (advanced i entries c)
  have hbucketStack : (base regs c).stacks 15 = c.buckets := rfl
  simp only [hbucketStack] at ha
  refine ⟨(7 * c.buckets.length + 5) + (nb + (2 + (1 + 1))), ?_, rf, ?_⟩
  · dsimp [bodyBudget]
    omega
  · simpa only [body, base, ready, state, d] using ha.seq (hbr.seq (hp.seq (hpop.seq hrefresh)))

def advanceMany (entries : List Entry) : ℕ → ℕ → Context → Context
  | 0, _, c => c
  | n + 1, i, c => advanceMany entries n (i + 1) (advanced i entries c)

def loopBudget (entries : List Entry) : ℕ → ℕ → Context → ℕ
  | 0, _, _ => 1
  | n + 1, i, c => bodyBudget i entries c +
      loopBudget entries n (i + 1) (advanced i entries c) + 1

theorem loop_eval (entries : List Entry) (n i : ℕ) (c : Context)
    (hblock : c.block = List.replicate i true)
    (hremaining : c.remaining = List.replicate n true)
    (hbuckets : c.buckets = ProgramEncoding.encodeRecords (entries.map entryWord))
    (hentries : ∀ e ∈ entries, i + n ≤ e.2.length) (regs : Fin 8 → Bool) :
    ∃ steps ≤ loopBudget entries n i c, ∃ rf,
      Eval loop steps (guard regs c) (base rf (advanceMany entries n i c)) := by
  induction n generalizing i c regs with
  | zero =>
    refine ⟨1, le_rfl, (guard regs c).regs, ?_⟩
    have hg : (guard regs c).regs 4 = false := by simp [guard, base, ready, state, readRegs, hremaining]
    exact Eval.while_false hg
  | succ n ih =>
    have he : ∀ e ∈ entries, i < e.2.length := by
      intro e he
      have := hentries e he
      omega
    obtain ⟨nb, hnb, rb, hbody⟩ := body_eval i entries c hblock hbuckets he (guard regs c).regs
    have hbody' : Eval body nb (guard regs c) (guard rb (advanced i entries c)) := hbody
    obtain ⟨hb, ht, hr⟩ := advanced_static i entries c
    have hb' : (advanced i entries c).block = List.replicate (i + 1) true := by
      rw [hb, hblock]
      simp [List.replicate_succ]
    have hr' : (advanced i entries c).remaining = List.replicate n true := by
      rw [hr, hremaining]
      simp
    have ht' : (advanced i entries c).buckets =
        ProgramEncoding.encodeRecords (entries.map entryWord) := ht.trans hbuckets
    obtain ⟨nr, hnr, rf, hrest⟩ := ih (i + 1) (advanced i entries c) hb' hr' ht'
      (by intro e he; have := hentries e he; omega) rb
    have hg : (guard regs c).regs 4 = true := by
      simp [guard, base, ready, state, readRegs, hremaining, List.replicate_succ]
    refine ⟨nb + nr + 1, ?_, rf, ?_⟩
    · simp only [loopBudget]
      omega
    · exact Eval.while_true hg hbody' hrest

/-- Extract the first `n` entries of every bucket by an actual nested loop.
The storage accumulator is retained in reverse-bit form for appending leftovers. -/
theorem program_trace (entries : List Entry) (n : ℕ) (c : Context)
    (hblock : c.block = []) (hremaining : c.remaining = List.replicate n true)
    (hbuckets : c.buckets = ProgramEncoding.encodeRecords (entries.map entryWord))
    (hentries : ∀ e ∈ entries, n ≤ e.2.length) (regs : Fin 8 → Bool) :
    ∃ steps ≤ loopBudget entries n 0 c + 2, ∃ rf,
      Trace program steps ((base regs c).withPC (some program.entry))
        ((base rf (advanceMany entries n 0 c)).withPC none) := by
  obtain ⟨steps, hs, rf, he⟩ := loop_eval entries n 0 c
    (by simpa using hblock) hremaining hbuckets (by simpa using hentries) regs
  exact ⟨1 + steps + 1, by omega, rf,
    compiled_halt_trace ((refresh_eval regs c).seq he) 15 12⟩

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
