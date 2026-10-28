import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Records := List (List Bool)

/-- Frame payload without its final delimiter. -/
def escaped (bits : List Bool) : List Bool := bits.flatMap fun b => [true, b]

@[simp] theorem escaped_nil : escaped [] = [] := rfl
@[simp] theorem escaped_cons (b : Bool) (bits : List Bool) :
    escaped (b :: bits) = true :: b :: escaped bits := rfl
@[simp] theorem escaped_append (a b : List Bool) :
    escaped (a ++ b) = escaped a ++ escaped b := by simp [escaped]

theorem frame_eq_escaped (bits : List Bool) :
    Encoding.frame bits = escaped bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [Encoding.frame_cons, ih]

/-- Consume a reversed payload and prepend its escaped forward payload.
The caller supplies frame/list delimiters. -/
abbrev escapeProgram : Program 2 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 5, .push 1 0 3,
    .set 0 true 4, .push 1 0 0, .halt]

theorem escapeProgram_trace (bits out : List Bool) (v pr : Bool) :
    Trace escapeProgram (5 * bits.length + 3)
      (ParserProgram.cfg (some 0) v pr bits out)
      (ParserProgram.cfg none false false [] (escaped bits.reverse ++ out)) := by
  induction bits generalizing out v pr with
  | nil =>
      refine .cons (b := ParserProgram.cfg (some 1) false false [] out) ?_ ?_
      · simp [step, ParserProgram.cfg, execInstr, readRegs]
      refine .cons (b := ParserProgram.cfg (some 5) false false [] out) ?_ ?_
      · simp [step, ParserProgram.cfg, execInstr]
      refine .cons ?_ (.refl _)
      simp [step, ParserProgram.cfg, execInstr]
  | cons b bits ih =>
      have t := ih (true :: b :: out) true true
      have cycle : Trace escapeProgram 5
          (ParserProgram.cfg (some 0) v pr (b :: bits) out)
          (ParserProgram.cfg (some 0) true true bits (true :: b :: out)) := by
        refine .cons (b := ParserProgram.cfg (some 1) b true bits out) ?_ ?_
        · simp [step, ParserProgram.cfg, execInstr, readRegs]
        refine .cons (b := ParserProgram.cfg (some 2) b true bits out) ?_ ?_
        · simp [step, ParserProgram.cfg, execInstr]
        refine .cons (b := ParserProgram.cfg (some 3) b true bits (b :: out)) ?_ ?_
        · simp [step, ParserProgram.cfg, execInstr]
        refine .cons (b := ParserProgram.cfg (some 4) true true bits (b :: out)) ?_ ?_
        · simp [step, ParserProgram.cfg, execInstr]
        refine .cons ?_ (.refl _)
        simp [step, ParserProgram.cfg, execInstr]
      convert cycle.trans t using 1 <;>
        simp [List.reverse_cons, List.append_assoc] ; omega

abbrev escape {r s : ℕ} (p : RecordPrograms.Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram escapeProgram
    (RecordPrograms.registerMap p) (RecordPrograms.stackMap p))

theorem escape_eval {r s : ℕ} (p : RecordPrograms.Ports r s) (base : State r s)
    (bits out : List Bool) (v pr f : Bool) :
    Eval (escape p) (5 * bits.length + 3)
      (RecordPrograms.state p base v pr f bits out)
      (RecordPrograms.state p base false false f [] (escaped bits.reverse ++ out)) := by
  have h := eval_call_lifted escapeProgram (RecordPrograms.registerMap p)
    (RecordPrograms.stackMap p) (RecordPrograms.state p base v pr f bits out)
    (RecordPrograms.registerMap_injective p) (RecordPrograms.stackMap_injective p)
    (a := RecordPrograms.parserState v pr bits out)
    (b := RecordPrograms.parserState false false [] (escaped bits.reverse ++ out))
    (escapeProgram_trace bits out v pr)
  simpa only [RecordPrograms.embed_parserState, escape] using h

abbrev escapedState {r s : ℕ} (p : RecordPrograms.Ports r s) (a : State r s) : State r s :=
  ⟨readRegs a.regs p.tag p.present none,
    Function.update (Function.update a.stacks p.source []) p.payload
      (escaped (a.stacks p.source).reverse ++ a.stacks p.payload)⟩

theorem escape_eval_state {r s : ℕ} (p : RecordPrograms.Ports r s) (a : State r s) :
    Eval (escape p) (5 * (a.stacks p.source).length + 3) a (escapedState p a) := by
  have h := escape_eval p a (a.stacks p.source) (a.stacks p.payload)
    (a.regs p.tag) (a.regs p.present) (a.regs p.found)
  rw [RecordPrograms.state_eq_self p a _ _ _ _ _ rfl rfl rfl rfl rfl] at h
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases ht : i = p.tag <;> by_cases hp : i = p.present <;>
      by_cases hf : i = p.found <;> subst_vars <;>
      simp_all [ readRegs, RecordPrograms.state,
        p.found_ne_tag, p.found_ne_present, p.tag_ne_present,
        Ne.symm p.found_ne_tag, Ne.symm p.found_ne_present]
  · rfl

abbrev pushConst {r s : ℕ} (dst : Fin s) (value : Fin r) (b : Bool) : Cmd r s :=
  .seq (RecordPrograms.atom (.set value b)) (RecordPrograms.atom (.push dst value))

abbrev pushedState {r s : ℕ} (dst : Fin s) (value : Fin r) (b : Bool)
    (a : State r s) : State r s :=
  ⟨Function.update a.regs value b, Function.update a.stacks dst (b :: a.stacks dst)⟩

theorem pushConst_eval {r s : ℕ} (dst : Fin s) (value : Fin r) (b : Bool)
    (a : State r s) : Eval (pushConst dst value b) 2 a (pushedState dst value b a) := by
  have h := Eval.seq (.base (StructuredProgram.Eval.atom (.set value b) a))
    (.base (StructuredProgram.Eval.atom (.push dst value)
      ((StructuredProgram.Atom.set value b).eval a)))
  simpa [pushConst, RecordPrograms.atom, pushedState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

theorem copy_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (a : State r s) (ht : a.stacks tmp = []) :
    Eval (.call (StackRoutines.copyProgram src dst tmp value present))
      (7 * (a.stacks src).length + 5) a
      ⟨readRegs a.regs value present none, StackRoutines.copyStacks src dst a.stacks⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.copyProgram_trace src dst tmp value present hsd hst htd hvp
      a.regs a.stacks ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC, StackRoutines.copyResult,
    StackRoutines.copyProgram, Nat.add_assoc] using h

theorem clear_eval {r s : ℕ} (src : Fin s) (value present : Fin r) (a : State r s) :
    Eval (.call (StackRoutines.clearProgram src value present))
      (2 * (a.stacks src).length + 3) a
      ⟨readRegs a.regs value present none, StackRoutines.clearStacks src a.stacks⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src value present a.regs a.stacks) 2 rfl rfl
  simpa [StructuredProgram.State.withPC, StackRoutines.clearResult,
    StackRoutines.clearProgram, Nat.add_assoc] using h

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

def outerPorts : RecordPrograms.Ports 10 9 :=
  ⟨0, 1, 2, 0, 2, by decide, by decide, by decide, by decide⟩

def innerPorts : RecordPrograms.Ports 10 9 :=
  ⟨3, 4, 5, 3, 4, by decide, by decide, by decide, by decide⟩

def wordPorts : RecordPrograms.Ports 10 9 :=
  ⟨6, 7, 8, 4, 5, by decide, by decide, by decide, by decide⟩

def tuplePorts : RecordPrograms.Ports 10 9 :=
  ⟨6, 7, 8, 6, 5, by decide, by decide, by decide, by decide⟩

abbrev wordCallback : Cmd 10 9 :=
  .seq (pushConst 5 6 false)
    (.seq (escape wordPorts)
      (.seq (.call (StackRoutines.copyProgram 2 6 7 6 7))
        (.seq (escape tuplePorts) (pushConst 5 6 true))))

def innerInvariant (alphabet : List Bool) (tuple tail depth : List Bool) (guard : Bool)
    (a : State 10 9) : Prop :=
  a.stacks 1 = alphabet ∧ a.stacks 2 = tuple.reverse ∧ a.stacks 0 = tail ∧
  a.stacks 6 = [] ∧ a.stacks 7 = [] ∧ a.stacks 8 = depth ∧
  a.regs 0 = false ∧ a.regs 1 = true ∧ a.regs 2 = false ∧ a.regs 9 = guard

def prependRecord (bits out : List Bool) : List Bool :=
  true :: (Encoding.frame bits ++ out)

theorem wordCallback_contract (alphabet tuple tail depth : List Bool) (guard : Bool) :
    RecordPrograms.CallbackContractWith innerPorts wordCallback (fun _ => false)
      (fun word => 5 * word.length + 12 * tuple.length + 15)
      (innerInvariant alphabet tuple tail depth guard)
      (fun word a b => b.stacks 5 = prependRecord (tuple ++ word) (a.stacks 5)) := by
  intro word rest base hb
  let a := RecordPrograms.state innerPorts base false true false rest word.reverse
  let b := pushedState 5 6 false a
  let c := escapedState wordPorts b
  let d : State 10 9 :=
    ⟨readRegs c.regs 6 7 none, StackRoutines.copyStacks 2 6 c.stacks⟩
  let e := escapedState tuplePorts d
  let f := pushedState 5 6 true e
  have hcopy : c.stacks 7 = [] := by
    simpa [c, b, a, escapedState, pushedState, wordPorts, RecordPrograms.state,
      innerPorts] using hb.2.2.2.2.1
  have h1 := pushConst_eval 5 6 false a
  have h2 := escape_eval_state wordPorts b
  have h3 := copy_eval 2 6 7 6 7 (by decide) (by decide) (by decide) (by decide) c hcopy
  have h4 := escape_eval_state tuplePorts d
  have h5 := pushConst_eval 5 6 true e
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  have hf : RecordPrograms.state innerPorts f false true false rest [] = f := by
    apply RecordPrograms.state_eq_self <;>
      simp [f, e, d, c, b, a, wordPorts, tuplePorts,
        RecordPrograms.state, innerPorts, readRegs, StackRoutines.copyStacks]
  refine ⟨5 * word.length + 12 * tuple.length + 15, f, le_rfl, ?_, ?_, ?_⟩
  · rcases hb with ⟨ha, ht, hs, h6, h7, h8, h0, h1, h2, h9⟩
    simp_all [innerInvariant, f, e, d, c, b, a, pushedState, escapedState,
      wordPorts, tuplePorts, RecordPrograms.state, innerPorts, readRegs,
      StackRoutines.copyStacks]
  · rcases hb with ⟨ha, ht, hs, h6, h7, h8, h0, h1, h2, h9⟩
    simp [f, e, d, c, b, a, wordPorts, tuplePorts,
      RecordPrograms.state, innerPorts, StackRoutines.copyStacks,
      ht, h6, prependRecord, frame_eq_escaped, List.append_assoc]
  · rw [hf]
    convert hrun using 1 ;
      simp [ a, b, c, d, wordPorts,
        tuplePorts, RecordPrograms.state, innerPorts, StackRoutines.copyStacks,
        hb.2.1, hb.2.2.2.1] ; omega

theorem unread_false (records : Records) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records <;> simp_all [RecordPrograms.unread]

abbrev tupleCallback : Cmd 10 9 :=
  .seq (.call (StackRoutines.copyProgram 1 3 7 6 7))
    (.seq (RecordPrograms.iterate innerPorts wordCallback)
      (.call (StackRoutines.clearProgram 2 6 7)))

def tupleCost (alphabet : Records) (tuple : List Bool) : ℕ :=
  7 * (ProgramEncoding.encodeRecords alphabet).length +
    RecordPrograms.budget (fun word => 5 * word.length + 12 * tuple.length + 15) alphabet +
    2 * tuple.length + 11

def outerInvariant (alphabet : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) : Prop :=
  a.stacks 1 = ProgramEncoding.encodeRecords alphabet ∧
  a.stacks 3 = [] ∧ a.stacks 4 = [] ∧ a.stacks 6 = [] ∧ a.stacks 7 = [] ∧
  a.stacks 8 = depth ∧ a.regs 9 = guard

def extendOutput (alphabet : Records) (tuple out : List Bool) : List Bool :=
  alphabet.foldl (fun out word => prependRecord (tuple ++ word) out) out

theorem tupleCallback_contract (alphabet : Records) (depth : List Bool) (guard : Bool) :
    RecordPrograms.CallbackContractWith outerPorts tupleCallback (fun _ => false)
      (tupleCost alphabet) (outerInvariant alphabet depth guard)
      (fun tuple a b => b.stacks 5 = extendOutput alphabet tuple (a.stacks 5)) := by
  intro tuple rest base hb
  rcases hb with ⟨ha, h3, h4, h6, h7, h8, h9⟩
  let a := RecordPrograms.state outerPorts base false true false rest tuple.reverse
  let b : State 10 9 :=
    ⟨readRegs a.regs 6 7 none, StackRoutines.copyStacks 1 3 a.stacks⟩
  have hcopy := copy_eval 1 3 7 6 7 (by decide) (by decide) (by decide) (by decide) a
    (by simpa [a, RecordPrograms.state, outerPorts] using h7)
  have hb : innerInvariant (ProgramEncoding.encodeRecords alphabet) tuple rest depth guard b := by
    simp [innerInvariant, b, a, StackRoutines.copyStacks, RecordPrograms.state,
      outerPorts, readRegs, ha, h6, h7, h8, h9]
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with innerPorts wordCallback (fun _ => false)
      (fun word => 5 * word.length + 12 * tuple.length + 15)
      (innerInvariant (ProgramEncoding.encodeRecords alphabet) tuple rest depth guard)
      (fun word a b => b.stacks 5 = prependRecord (tuple ++ word) (a.stacks 5))
      (wordCallback_contract _ tuple rest depth guard) alphabet [] b hb
      (b.regs 3) (b.regs 4) (b.regs 5)
  let c := RecordPrograms.state innerPorts next false true false [] []
  have hin : RecordPrograms.state innerPorts b (b.regs 3) (b.regs 4) (b.regs 5)
      (Encoding.encodeList id alphabet ++ []) [] = b := by
    apply RecordPrograms.state_eq_self <;>
      simp [b, a, StackRoutines.copyStacks, RecordPrograms.state, outerPorts,
        innerPorts, ha, h3, h4, ProgramEncoding.encodeRecords]
  have hiter' : Eval (RecordPrograms.iterate innerPorts wordCallback) n b c := by
    have hany : alphabet.any (fun _ => false) = false := by
      induction alphabet <;> simp_all
    simpa only [hin, hany, unread_false] using hiter
  let d : State 10 9 :=
    ⟨readRegs c.regs 6 7 none, StackRoutines.clearStacks 2 c.stacks⟩
  have hclear := clear_eval 2 6 7 c
  have hout := history.fold_of_false (by simp) (fun s => s.stacks 5)
    (fun out word => prependRecord (tuple ++ word) out) (fun _ _ _ h => h)
  have hd : RecordPrograms.state outerPorts d false true false rest [] = d := by
    rcases hnext with ⟨_, _, ht, _, _, _, hr0, hr1, hr2, _⟩
    apply RecordPrograms.state_eq_self <;>
      simp [d, c, RecordPrograms.state, innerPorts, outerPorts, readRegs,
        StackRoutines.clearStacks, ht, hr0, hr1, hr2]
  refine ⟨(7 * (a.stacks 1).length + 5) + (n + (2 * (c.stacks 2).length + 3)),
    d, ?_, ?_, ?_, ?_⟩
  · have hlen : c.stacks 2 = tuple.reverse := by
      simpa [c, RecordPrograms.state, innerPorts] using hnext.2.1
    simp only [hlen, List.length_reverse]
    have ha' : a.stacks 1 = ProgramEncoding.encodeRecords alphabet := by
      simpa [a, RecordPrograms.state, outerPorts] using ha
    rw [ha']
    dsimp [tupleCost]
    omega
  · rcases hnext with ⟨ha', _, _, h6', h7', h8', _, _, _, h9'⟩
    simp [outerInvariant, d, c, RecordPrograms.state, innerPorts,
      StackRoutines.clearStacks, readRegs, ha', h6', h7', h8', h9']
  · simpa [extendOutput, d, c, b, a, StackRoutines.clearStacks,
      StackRoutines.copyStacks, RecordPrograms.state, innerPorts, outerPorts] using hout
  · rw [hd]
    exact hcopy.seq (hiter'.seq hclear)

abbrev cartesianCmd : Cmd 10 9 := RecordPrograms.iterate outerPorts tupleCallback

def cartesianOutput (tuples alphabet : Records) : Records :=
  (tuples.flatMap fun tuple => alphabet.map (tuple ++ ·)).reverse

def expansionCost (tuples alphabet : Records) : ℕ :=
  3 + RecordPrograms.budget (tupleCost alphabet) tuples

def appendEncoded (records : Records) (out : List Bool) : List Bool :=
  records.foldr prependRecord out

theorem appendEncoded_encodeRecords (xs ys : Records) :
    appendEncoded xs (ProgramEncoding.encodeRecords ys) =
      ProgramEncoding.encodeRecords (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendEncoded, prependRecord, ProgramEncoding.encodeRecords,
      Encoding.encodeList] at ih ⊢; exact ih

theorem fold_prependRecord (xs : Records) (out : List Bool) :
    xs.foldl (fun out bits => prependRecord bits out) out = appendEncoded xs.reverse out := by
  simp [appendEncoded, List.foldr_reverse ]

theorem fold_extendOutput (tuples alphabet : Records) (out : List Bool) :
    tuples.foldl (fun out tuple => extendOutput alphabet tuple out) out =
      appendEncoded (cartesianOutput tuples alphabet) out := by
  rw [cartesianOutput, ← fold_prependRecord]
  induction tuples generalizing out with
  | nil => rfl
  | cons tuple tuples ih =>
      simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append]
      simpa only [List.foldl_map, extendOutput] using ih (extendOutput alphabet tuple out)

theorem cartesian_eval (tuples alphabet accum : Records) (depth : List Bool) (guard : Bool)
    (base : State 10 9) (hb : outerInvariant alphabet depth guard base)
    (hrows : base.stacks 0 = ProgramEncoding.encodeRecords tuples)
    (hpayload : base.stacks 2 = [])
    (hout : base.stacks 5 = ProgramEncoding.encodeRecords accum) :
    ∃ n next, n ≤ expansionCost tuples alphabet ∧ outerInvariant alphabet depth guard next ∧
      next.stacks 0 = [] ∧ next.stacks 2 = [] ∧
      next.stacks 5 = ProgramEncoding.encodeRecords (cartesianOutput tuples alphabet ++ accum) ∧
      Eval cartesianCmd n base next := by
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with outerPorts tupleCallback (fun _ => false)
      (tupleCost alphabet) (outerInvariant alphabet depth guard)
      (fun tuple a b => b.stacks 5 = extendOutput alphabet tuple (a.stacks 5))
      (tupleCallback_contract alphabet depth guard) tuples [] base hb
      (base.regs 0) (base.regs 1) (base.regs 2)
  let final := RecordPrograms.state outerPorts next false true false [] []
  have hstart : RecordPrograms.state outerPorts base (base.regs 0) (base.regs 1)
      (base.regs 2) (Encoding.encodeList id tuples ++ []) [] = base := by
    apply RecordPrograms.state_eq_self <;>
      simp_all [outerPorts, ProgramEncoding.encodeRecords]
  have hfold := history.fold_of_false (by simp) (fun s => s.stacks 5)
    (fun out tuple => extendOutput alphabet tuple out) (fun _ _ _ h => h)
  rw [fold_extendOutput, hout, appendEncoded_encodeRecords] at hfold
  refine ⟨n, final, hn, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [final, outerInvariant, RecordPrograms.state, outerPorts] using hnext
  · simp [final, RecordPrograms.state, outerPorts]
  · simp [final, RecordPrograms.state, outerPorts]
  · simpa [final, RecordPrograms.state, outerPorts] using hfold
  · have hany : tuples.any (fun _ => false) = false := by
      induction tuples <;> simp_all
    simpa only [cartesianCmd, final, hstart, hany, unread_false] using hiter

/-- The Cartesian expansion has one fixed finite control table. -/
def cartesianProgram := StructuredCalls.compiled cartesianCmd 0 5

theorem cartesian_runsIn (tuples alphabet accum : Records) (depth : List Bool) (guard : Bool)
    (base : State 10 9) (hb : outerInvariant alphabet depth guard base)
    (hrows : base.stacks 0 = ProgramEncoding.encodeRecords tuples)
    (hpayload : base.stacks 2 = [])
    (hout : base.stacks 5 = ProgramEncoding.encodeRecords accum) :
    ∃ next, outerInvariant alphabet depth guard next ∧ next.stacks 0 = [] ∧
      next.stacks 2 = [] ∧
      next.stacks 5 = ProgramEncoding.encodeRecords (cartesianOutput tuples alphabet ++ accum) ∧
      RunsIn cartesianProgram (expansionCost tuples alphabet + 1)
        (base.withPC (some cartesianProgram.entry)) (next.withPC none) := by
  obtain ⟨n, next, hn, hi, h0, h2, h5, he⟩ :=
    cartesian_eval tuples alphabet accum depth guard base hb hrows hpayload hout
  exact ⟨next, hi, h0, h2, h5, n + 1, Nat.add_le_add_right hn 1,
    StructuredCalls.compiled_halt_trace he 0 5⟩

theorem cartesianOutput_length (tuples alphabet : Records) :
    (cartesianOutput tuples alphabet).length = tuples.length * alphabet.length := by
  simp only [cartesianOutput, List.length_reverse]
  induction tuples with
  | nil => simp
  | cons tuple tuples ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem cartesianOutput_perm (tuples alphabet : Records) :
    (cartesianOutput tuples alphabet).Perm
      (tuples.flatMap fun tuple => alphabet.map (tuple ++ ·)) := by
  exact List.reverse_perm _

theorem transfer_eval {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present) (a : State r s) :
    Eval (.call (StackRoutines.transferProgram src dst value present))
      (3 * (a.stacks src).length + 3) a
      ⟨readRegs a.regs value present none, StackRoutines.transferStacks src dst a.stacks⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.transferProgram_trace src dst value present hsd hvp a.regs a.stacks)
    3 rfl rfl
  simpa [StructuredProgram.State.withPC, StackRoutines.transferResult,
    StackRoutines.transferProgram, Nat.add_assoc] using h

def Ready (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) : Prop :=
  outerInvariant alphabet depth guard a ∧
  a.stacks 0 = ProgramEncoding.encodeRecords rows ∧ a.stacks 2 = [] ∧ a.stacks 5 = [false]

/-- Reuse the same tuple storage after each Cartesian expansion. Two actual
stack transfers restore the forward serialized order. -/
abbrev expandStep : Cmd 10 9 :=
  .seq cartesianCmd
    (.seq (.call (StackRoutines.transferProgram 5 6 6 7))
      (.seq (.call (StackRoutines.transferProgram 6 0 6 7)) (pushConst 5 6 false)))

def stepCost (rows alphabet : Records) : ℕ :=
  expansionCost rows alphabet +
    6 * (ProgramEncoding.encodeRecords (cartesianOutput rows alphabet)).length + 8

theorem expandStep_eval (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ n next, n ≤ stepCost rows alphabet ∧
      Ready alphabet (cartesianOutput rows alphabet) depth guard next ∧
      Eval expandStep n a next := by
  obtain ⟨n, b, hn, hb, hb0, hb2, hb5, ht⟩ :=
    cartesian_eval rows alphabet [] depth guard a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  simp only [List.append_nil] at hb5
  let c : State 10 9 :=
    ⟨readRegs b.regs 6 7 none, StackRoutines.transferStacks 5 6 b.stacks⟩
  let d : State 10 9 :=
    ⟨readRegs c.regs 6 7 none, StackRoutines.transferStacks 6 0 c.stacks⟩
  let e := pushedState 5 6 false d
  have h1 := transfer_eval 5 6 6 7 (by decide) (by decide) b
  have h2 := transfer_eval 6 0 6 7 (by decide) (by decide) c
  have h3 := pushConst_eval 5 6 false d
  refine ⟨n + ((3 * (b.stacks 5).length + 3) + (3 * (c.stacks 6).length + 3 + 2)),
    e, ?_, ?_, ht.seq (h1.seq (h2.seq h3))⟩
  · have hc6 : (c.stacks 6).length = (b.stacks 5).length := by
      simp [c, StackRoutines.transferStacks, hb.2.2.2.1]
    rw [hc6, hb5]
    dsimp [stepCost]
    omega
  · rcases hb with ⟨hba, hb3, hb4, hb6, hb7, hb8, hb9⟩
    simp [Ready, outerInvariant, e, d, c, StackRoutines.transferStacks,
      readRegs, hba, hb3, hb4, hb6, hb7, hb8, hb9, hb0, hb2, hb5]

abbrev powerRows (alphabet : Records) : ℕ → Records → Records
  | 0, rows => rows
  | n + 1, rows => powerRows alphabet n (cartesianOutput rows alphabet)

abbrev powerCost (alphabet : Records) : ℕ → Records → ℕ
  | 0, _ => 2
  | n + 1, rows => stepCost rows alphabet + powerCost alphabet n (cartesianOutput rows alphabet) + 2

abbrev readDepth : Cmd 10 9 := RecordPrograms.atom (.pop 8 8 9)

abbrev readDepthState (a : State 10 9) : State 10 9 :=
  ⟨readRegs a.regs 8 9 (a.stacks 8).head?, Function.update a.stacks 8 (a.stacks 8).tail⟩

theorem readDepth_eval (a : State 10 9) : Eval readDepth 1 a (readDepthState a) := by
  exact .base (.atom _ _)

abbrev powerLoop : Cmd 10 9 := .while 9 (.seq expandStep readDepth)
abbrev powerCmd : Cmd 10 9 := .seq readDepth powerLoop

theorem powerCmd_eval (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ n next, n ≤ powerCost alphabet depth.length rows ∧
      Ready alphabet (powerRows alphabet depth.length rows) [] false next ∧
      Eval powerCmd n a next := by
  induction depth generalizing rows guard a with
  | nil =>
      let b := readDepthState a
      have hb : Ready alphabet rows [] false b := by
        rcases ha with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
        simp [Ready, outerInvariant, b, readRegs,
          h1,h3,h4,h6,h7,h8,h0,h2,h5]
      refine ⟨2, b, le_rfl, hb, ?_⟩
      exact (readDepth_eval a).seq (Eval.while_false hb.1.2.2.2.2.2.2)
  | cons bit depth ih =>
      let b := readDepthState a
      have hb : Ready alphabet rows depth true b := by
        rcases ha with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
        simp [Ready, outerInvariant, b, readRegs,
          h1,h3,h4,h6,h7,h8,h0,h2,h5]
      obtain ⟨n, c, hn, hc, ht⟩ := expandStep_eval alphabet rows depth true b hb
      obtain ⟨m, d, hm, hd, hr⟩ := ih (cartesianOutput rows alphabet) true c hc
      cases hr with
      | @seq first second k l x y z hp hl =>
          refine ⟨1 + (n + k + l + 1), d, ?_, hd, ?_⟩
          · simp only [List.length_cons, powerCost]
            omega
          · exact (readDepth_eval a).seq
              (Eval.while_true hb.1.2.2.2.2.2.2 (ht.seq hp) hl)

/-- Runtime unary iteration of one fixed Cartesian expansion. -/
def powerProgram := StructuredCalls.compiled powerCmd 1 0

theorem powerProgram_runsIn (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ next, Ready alphabet (powerRows alphabet depth.length rows) [] false next ∧
      RunsIn powerProgram (powerCost alphabet depth.length rows + 1)
        (a.withPC (some powerProgram.entry)) (next.withPC none) := by
  obtain ⟨n, next, hn, hs, he⟩ := powerCmd_eval alphabet rows depth guard a ha
  exact ⟨next, hs, n + 1, Nat.add_le_add_right hn 1,
    StructuredCalls.compiled_halt_trace he 1 0⟩

theorem powerRows_length (alphabet rows : Records) (n : ℕ) :
    (powerRows alphabet n rows).length = rows.length * alphabet.length ^ n := by
  revert rows
  refine Nat.rec (motive := fun n => ∀ rows : Records,
    (powerRows alphabet n rows).length = rows.length * alphabet.length ^ n) ?_ ?_ n
  · intro rows
    simp [powerRows]
  · intro n ih rows
    calc
      (powerRows alphabet (n + 1) rows).length =
          (powerRows alphabet n (cartesianOutput rows alphabet)).length := rfl
      _ = (cartesianOutput rows alphabet).length * alphabet.length ^ n := ih _
      _ = (rows.length * alphabet.length) * alphabet.length ^ n := by
        rw [cartesianOutput_length]
      _ = rows.length * alphabet.length ^ (n + 1) := by
        rw [pow_succ]
        ac_rfl

/-- Install the constant singleton empty tuple and empty output list using
eight real bit instructions. No tuple array is supplied by the caller. -/
abbrev initCmd : Cmd 10 9 :=
  .seq (pushConst 0 6 false) (.seq (pushConst 0 6 false)
    (.seq (pushConst 0 6 true) (pushConst 5 6 false)))

theorem initCmd_eval (alphabet : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ b, Ready alphabet [[]] depth guard b ∧ Eval initCmd 8 a b := by
  let b := pushedState 0 6 false a
  let c := pushedState 0 6 false b
  let d := pushedState 0 6 true c
  let e := pushedState 5 6 false d
  refine ⟨e, ?_, ?_⟩
  · rcases ha with ⟨ha,h3,h4,h6,h7,h8,h9⟩
    simp [Ready, outerInvariant, e, d, c, b, ha,h0,h2,h3,h4,h5,h6,h7,h8,h9,
      ProgramEncoding.encodeRecords, Encoding.encodeList, Encoding.frame]
  · exact (pushConst_eval 0 6 false a).seq ((pushConst_eval 0 6 false b).seq
      ((pushConst_eval 0 6 true c).seq (pushConst_eval 5 6 false d)))

abbrev generateCmd : Cmd 10 9 := .seq initCmd powerCmd

/-- One finite instruction table for all alphabets and all tuple dimensions. -/
def generateProgram := StructuredCalls.compiled generateCmd 1 0

theorem cartesian_control_size : StructuredCalls.size cartesianCmd + 1 = 62 := rfl
theorem power_control_size : StructuredCalls.size powerCmd + 1 = 75 := rfl
theorem generate_control_size : StructuredCalls.size generateCmd + 1 = 83 := rfl

theorem generateProgram_runsIn (alphabet : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ next, Ready alphabet (powerRows alphabet depth.length [[]]) [] false next ∧
      RunsIn generateProgram (powerCost alphabet depth.length [[]] + 9)
        (a.withPC (some generateProgram.entry)) (next.withPC none) := by
  obtain ⟨b,hb,hi⟩ := initCmd_eval alphabet depth guard a ha h0 h2 h5
  obtain ⟨n,next,hn,hs,he⟩ := powerCmd_eval alphabet [[]] depth guard b hb
  refine ⟨next,hs,8+n+1,by omega,?_⟩
  exact StructuredCalls.compiled_halt_trace (hi.seq he) 1 0

theorem generateProgram_primitive_runsIn (alphabet : Records) (depth : List Bool)
    (guard : Bool) (a : State 10 9) (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ next, Ready alphabet (powerRows alphabet depth.length [[]]) [] false next ∧
      Computation.RunsIn (BitProgram.primitive generateProgram).step
        (BitProgram.primitiveOverhead generateProgram * (powerCost alphabet depth.length [[]] + 9))
        (BitProgram.primitiveCfg generateProgram (a.withPC (some generateProgram.entry)))
        (BitProgram.primitiveCfg generateProgram (next.withPC none)) := by
  obtain ⟨next, hs, ht⟩ := generateProgram_runsIn alphabet depth guard a ha h0 h2 h5
  exact ⟨next, hs, BitProgram.primitive_execution generateProgram ht⟩

theorem generated_count (alphabet : Records) (n : ℕ) :
    (powerRows alphabet n [[]]).length = alphabet.length ^ n := by
  simpa using powerRows_length alphabet [[]] n

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
