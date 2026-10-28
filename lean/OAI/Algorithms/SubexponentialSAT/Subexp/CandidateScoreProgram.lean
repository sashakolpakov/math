import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateArrayProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram

namespace OAI.Algorithms

/-!
# Fixed-control candidate scoring

Score records are accumulated as reversed serialized bytes and reversed once
at the end, so output score order agrees with the input candidate order.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def writerState {l : ℕ} (pc : Option (Fin l)) (v pr tag : Bool)
    (input output : List Bool) : Cfg 3 2 l :=
  ⟨pc, ![v,pr,tag], ParserProgram.pair input output⟩

/-- Six labels write the reverse of an escaped payload. Label 5 installs the
constant tag bit; the four-instruction loop consumes the runtime payload. -/
abbrev reverseEscapeProgram : Program 3 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 5
  code := ![.pop 0 0 1 1, .branch 1 2 4, .push 1 2 3, .push 1 0 0,
    .halt, .set 2 true 0]

theorem reverseEscape_core (bits out : List Bool) (v pr : Bool) :
    Trace reverseEscapeProgram (4 * bits.length + 3)
      (writerState (some 0) v pr true bits out)
      (writerState none false false true [] ((TupleProgram.escaped bits).reverse ++ out)) := by
  induction bits generalizing out v pr with
  | nil =>
      refine .cons (b := writerState (some 1) false false true [] out) ?_ ?_
      · simp [step,writerState,execInstr,readRegs]
        funext i; fin_cases i <;> simp
      refine .cons (b := writerState (some 4) false false true [] out) ?_ ?_
      · simp [step,writerState,execInstr]
      refine .cons ?_ (.refl _)
      simp [step,writerState,execInstr]
  | cons bit bits ih =>
      have cycle : Trace reverseEscapeProgram 4
          (writerState (some 0) v pr true (bit :: bits) out)
          (writerState (some 0) bit true true bits (bit :: true :: out)) := by
        refine .cons (b := writerState (some 1) bit true true bits out) ?_ ?_
        · simp [step,writerState,execInstr,readRegs]
          funext i; fin_cases i <;> simp
        refine .cons (b := writerState (some 2) bit true true bits out) ?_ ?_
        · simp [step,writerState,execInstr]
        refine .cons (b := writerState (some 3) bit true true bits (true :: out)) ?_ ?_
        · simp [step,writerState,execInstr]
        refine .cons ?_ (.refl _)
        simp [step,writerState,execInstr]
      have h := cycle.trans (ih (bit :: true :: out) bit true)
      convert h using 1 <;>
        simp [TupleProgram.escaped_cons,List.reverse_cons,List.append_assoc] ; omega

theorem reverseEscape_trace (bits out : List Bool) (v pr tag : Bool) :
    Trace reverseEscapeProgram (4 * bits.length + 4)
      (writerState (some reverseEscapeProgram.entry) v pr tag bits out)
      (writerState none false false true [] ((TupleProgram.escaped bits).reverse ++ out)) := by
  have first : step reverseEscapeProgram
      (writerState (some reverseEscapeProgram.entry) v pr tag bits out) =
      some (writerState (some 0) v pr true bits out) := by
    simp [step,writerState,execInstr]
    funext i; fin_cases i <;> simp
  simpa only [Nat.add_assoc] using SubexponentialSAT.Computation.Trace.cons first (reverseEscape_core bits out v pr)

def resetList {r s : ℕ} : List (Fin r) → StructuredProgram.Cmd r s
  | [] => .skip
  | i :: rest => .seq (.atom (.set i false)) (resetList rest)

def resetValues {r : ℕ} (indices : List (Fin r)) (regs : Fin r → Bool) : Fin r → Bool :=
  indices.foldl (fun rs i => Function.update rs i false) regs

theorem resetValues_apply {r : ℕ} (indices : List (Fin r)) (regs : Fin r → Bool)
    (i : Fin r) : resetValues indices regs i = if i ∈ indices then false else regs i := by
  induction indices generalizing regs with
  | nil => simp [resetValues]
  | cons j rest ih =>
      change resetValues rest (Function.update regs j false) i = _
      rw [ih]
      by_cases hi : i = j <;> by_cases hr : i ∈ rest <;>
        simp_all []

theorem resetList_eval {r s : ℕ} (indices : List (Fin r)) (d : State r s) :
    StructuredProgram.Eval (resetList indices) indices.length d
      ⟨resetValues indices d.regs,d.stacks⟩ := by
  induction indices generalizing d with
  | nil => exact .skip d
  | cons i rest ih =>
      have h := (StructuredProgram.Eval.atom (.set i false) d).seq
        (ih ((StructuredProgram.Atom.set i false).eval d))
      simpa [resetList,resetValues,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        StructuredProgram.State.withPC,execInstr,Nat.add_comm] using h

def lowRegisters (i : Fin 13) : Fin 16 := Fin.castAdd 3 i
def lowStacks (i : Fin 26) : Fin 36 := Fin.castAdd 10 i

theorem lowRegisters_injective : Function.Injective lowRegisters := Fin.castAdd_injective _ _
theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _

abbrev resetLow : Cmd 16 36 := .base (resetList ((List.finRange 13).map lowRegisters))

def resetLowState (a : State 16 36) : State 16 36 :=
  ⟨resetValues ((List.finRange 13).map lowRegisters) a.regs,a.stacks⟩

theorem resetLow_eval (a : State 16 36) : Eval resetLow 13 a (resetLowState a) := by
  simpa [resetLow,resetLowState] using
    Eval.base (resetList_eval ((List.finRange 13).map lowRegisters) a)

@[simp] theorem resetLow_register (a : State 16 36) (i : Fin 13) :
    (resetLowState a).regs (lowRegisters i) = false := by
  simp [resetLowState,resetValues_apply]

theorem resetLow_frame (a : State 16 36) (i : Fin 16) (hi : 13 ≤ i.val) :
    (resetLowState a).regs i = a.regs i := by
  have hnot : i ∉ (List.finRange 13).map lowRegisters := by
    simp only [List.mem_map,List.mem_finRange,true_and,not_exists]
    intro j h
    have hv := congrArg Fin.val h
    simp [lowRegisters] at hv
    omega
  simp [resetLowState,resetValues_apply,hnot]

def writerRegisters : Fin 3 → Fin 16 := ![0,1,2]
def writerStacks : Fin 2 → Fin 36 := ![18,35]

theorem writerRegisters_injective : Function.Injective writerRegisters := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [writerRegisters]
theorem writerStacks_injective : Function.Injective writerStacks := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [writerStacks]

def writerData (v pr tag : Bool) (input output : List Bool) : State 3 2 :=
  ⟨![v,pr,tag],ParserProgram.pair input output⟩

theorem embed_eq {r s R S : ℕ} (ρ : Fin r → Fin R) (σ : Fin s → Fin S)
    (frame : State R S) (small : State r s) (large : State R S)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hr : ∀ i, large.regs (ρ i) = small.regs i)
    (hs : ∀ i, large.stacks (σ i) = small.stacks i)
    (hfr : ∀ i, (¬ ∃ j, ρ j = i) → large.regs i = frame.regs i)
    (hfs : ∀ i, (¬ ∃ j, σ j = i) → large.stacks i = frame.stacks i) :
    embedState ρ σ frame small = large := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, ρ j = i
    · obtain ⟨j,rfl⟩ := h
      exact (embedState_register ρ σ frame small hρ j).trans (hr j).symm
    · exact (embedState_register_frame ρ σ frame small i h).trans (hfr i h).symm
  · funext i
    by_cases h : ∃ j, σ j = i
    · obtain ⟨j,rfl⟩ := h
      exact (embedState_stack ρ σ frame small hσ j).trans (hs j).symm
    · exact (embedState_stack_frame ρ σ frame small i h).trans (hfs i h).symm

theorem embed_writerData (a : State 16 36) (v pr tag : Bool) (input output : List Bool) :
    embedState writerRegisters writerStacks a (writerData v pr tag input output) =
      ⟨Function.update (Function.update (Function.update a.regs 0 v) 1 pr) 2 tag,
        Function.update (Function.update a.stacks 18 input) 35 output⟩ := by
  apply embed_eq _ _ _ _ _ writerRegisters_injective writerStacks_injective
  · intro i; fin_cases i <;> simp [writerData,writerRegisters]
  · intro i; fin_cases i <;> simp [writerData,writerStacks,ParserProgram.pair]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [writerRegisters] using h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1,by simpa [writerRegisters] using h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨2,by simpa [writerRegisters] using h.symm⟩
    simp [h0,h1,h2]
  · intro i hi
    have h18 : i ≠ 18 := fun h => hi ⟨0,by simpa [writerStacks] using h.symm⟩
    have h35 : i ≠ 35 := fun h => hi ⟨1,by simpa [writerStacks] using h.symm⟩
    simp [h18,h35]

abbrev reverseWriter : Cmd 16 36 :=
  .call (ProgramLinking.liftProgram reverseEscapeProgram writerRegisters writerStacks)

def reverseWritten (a : State 16 36) : State 16 36 :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2 true,
    Function.update (Function.update a.stacks 18 []) 35
      ((TupleProgram.escaped (a.stacks 18)).reverse ++ a.stacks 35)⟩

theorem reverseWriter_eval (a : State 16 36) :
    Eval reverseWriter (4 * (a.stacks 18).length + 4) a (reverseWritten a) := by
  have h := eval_call_lifted reverseEscapeProgram writerRegisters writerStacks a
    writerRegisters_injective writerStacks_injective
    (a := writerData (a.regs 0) (a.regs 1) (a.regs 2) (a.stacks 18) (a.stacks 35))
    (b := writerData false false true [] ((TupleProgram.escaped (a.stacks 18)).reverse ++ a.stacks 35))
    (reverseEscape_trace (a.stacks 18) (a.stacks 35) (a.regs 0) (a.regs 1) (a.regs 2))
  simpa [embed_writerData,reverseWriter,reverseWritten] using h

abbrev emitScore : Cmd 16 36 :=
  .seq (TupleProgram.pushConst 35 0 true)
    (.seq reverseWriter (TupleProgram.pushConst 35 0 false))

def emittedScore (a : State 16 36) : State 16 36 :=
  TupleProgram.pushedState 35 0 false
    (reverseWritten (TupleProgram.pushedState 35 0 true a))

theorem emitScore_eval (a : State 16 36) :
    Eval emitScore (4 * (a.stacks 18).length + 8) a (emittedScore a) := by
  have h := (TupleProgram.pushConst_eval 35 0 true a).seq
    ((reverseWriter_eval (TupleProgram.pushedState 35 0 true a)).seq
      (TupleProgram.pushConst_eval 35 0 false
        (reverseWritten (TupleProgram.pushedState 35 0 true a))))
  convert h using 1 <;> simp [emittedScore,TupleProgram.pushedState] ; omega

def reverseRecord (bits out : List Bool) : List Bool :=
  (true :: Encoding.frame bits).reverse ++ out

theorem emittedScore_output (a : State 16 36) :
    (emittedScore a).stacks 35 = reverseRecord (a.stacks 18) (a.stacks 35) := by
  simp [emittedScore,TupleProgram.pushedState,reverseWritten,reverseRecord,
    TupleProgram.frame_eq_escaped,List.reverse_append,List.append_assoc]

@[simp] theorem emittedScore_consumed (a : State 16 36) :
    (emittedScore a).stacks 18 = [] := by
  simp [emittedScore,TupleProgram.pushedState,reverseWritten]

def outerPorts : RecordPrograms.Ports 16 36 :=
  ⟨13,14,15,29,34,by decide,by decide,by decide,by decide⟩

def arrayRegisters : Fin 2 → Fin 16 := ![0,1]
def arrayStacks : Fin 10 → Fin 36 := ![26,27,28,3,0,1,2,4,13,5]

theorem arrayRegisters_injective : Function.Injective arrayRegisters := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [arrayRegisters]
theorem arrayStacks_injective : Function.Injective arrayStacks := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [arrayStacks]

structure Context where
  before : List (List Bool)
  old : List Bool
  after : List (List Bool)
  width : List Bool
  alphabet : List (List Bool)
  depth : List Bool
  index : List Bool
  candidates : List (List Bool)
  pairs : List PairScoreProgram.PlanPair

def pairContext (ctx : Context) (candidate : List Bool) : PairScoreProgram.Context :=
  ⟨ctx.before ++ candidate :: ctx.after,ctx.width,ctx.alphabet,ctx.depth⟩

structure Context.Valid (ctx : Context) : Prop where
  index_length : ctx.index.length = ctx.before.length
  before_width : ∀ row ∈ ctx.before, row.length = ctx.width.length
  old_width : ctx.old.length = ctx.width.length
  after_width : ∀ row ∈ ctx.after, row.length = ctx.width.length
  alphabet_width : ∀ row ∈ ctx.alphabet, row.length = ctx.width.length
  candidate_width : ∀ row ∈ ctx.candidates, row.length = ctx.width.length
  pairs_valid : ∀ pair ∈ ctx.pairs, PairScoreProgram.ValidPair (pairContext ctx ctx.old) pair

def original (ctx : Context) : List Bool :=
  ctx.before.flatten ++ (ctx.old ++ ctx.after.flatten)

def updated (ctx : Context) (candidate : List Bool) : List Bool :=
  ctx.before.flatten ++ (candidate ++ ctx.after.flatten)

def candidateScore (ctx : Context) (candidate : List Bool) : ℕ :=
  PairScoreProgram.score (pairContext ctx candidate) ctx.pairs

def workState (ctx : Context) (regs : Fin 16 → Bool)
    (tail candidate current score pairSource builder : List Bool) : State 16 36 :=
  ⟨regs,fun j =>
    if j = 3 then ctx.width else if j = 13 then current else if j = 18 then score
    else if j = 19 then ProgramEncoding.encodeRecords ctx.alphabet
    else if j = 20 then pairSource else if j = 23 then ctx.depth
    else if j = 26 then original ctx else if j = 27 then candidate
    else if j = 28 then ctx.index else if j = 29 then tail
    else if j = 30 then ProgramEncoding.encodeRecords ctx.candidates
    else if j = 31 then PairScoreProgram.pairRecords ctx.pairs
    else if j = 35 then builder else []⟩

def baseState (ctx : Context) (regs : Fin 16 → Bool) (builder : List Bool) : State 16 36 :=
  workState ctx regs [] [] [] [] [] builder

def pairStartRegs : Fin 16 → Bool := fun i => decide (i = 14)
def scoredRegs : Fin 16 → Bool := fun i => decide (i = 11 ∨ i = 14)
def finishedRegs : Fin 16 → Bool := fun i => decide (i = 2 ∨ i = 11 ∨ i = 14)

abbrev transferCandidate : Cmd 16 36 := .call (StackRoutines.transferProgram 34 27 0 1)
abbrev updateCandidate : Cmd 16 36 :=
  .call (ProgramLinking.liftProgram CandidateArrayProgram.program arrayRegisters arrayStacks)
abbrev copyPairs : Cmd 16 36 := .call (StackRoutines.copyProgram 31 20 33 0 1)
abbrev runPairs : Cmd 16 36 :=
  .call (ProgramLinking.liftProgram PairScoreProgram.program lowRegisters lowStacks)
abbrev cleanup : Cmd 16 36 :=
  .seq (.call (StackRoutines.clearProgram 13 0 1))
    (.call (StackRoutines.clearProgram 27 0 1))

abbrev callback : Cmd 16 36 :=
  .seq transferCandidate (.seq updateCandidate (.seq copyPairs
    (.seq resetLow (.seq runPairs (.seq emitScore cleanup)))))

theorem pairContext_valid (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hw : candidate.length = ctx.width.length) : (pairContext ctx candidate).Valid := by
  refine ⟨?_,hc.alphabet_width⟩
  intro row hr
  simp only [pairContext,List.mem_append,List.mem_cons] at hr
  rcases hr with hr | rfl | hr
  · exact hc.before_width row hr
  · exact hw
  · exact hc.after_width row hr

theorem pairContext_pairs (ctx : Context) (hc : ctx.Valid) (candidate : List Bool) :
    ∀ pair ∈ ctx.pairs, PairScoreProgram.ValidPair (pairContext ctx candidate) pair := by
  intro pair hp
  simpa [PairScoreProgram.ValidPair,pairContext] using hc.pairs_valid pair hp

theorem updated_length (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hw : candidate.length = ctx.width.length) : (updated ctx candidate).length = (original ctx).length := by
  simp [updated,original,hw,hc.old_width]

theorem transferCandidate_eval (ctx : Context) (regs : Fin 16 → Bool)
    (tail builder candidate : List Bool) :
    Eval transferCandidate (3 * candidate.length + 3)
      (RecordPrograms.state outerPorts (baseState ctx regs builder)
        false true false tail candidate.reverse)
      (workState ctx
        (readRegs (RecordPrograms.state outerPorts (baseState ctx regs builder)
          false true false tail candidate.reverse).regs 0 1 none)
        tail candidate [] [] [] builder) := by
  have h := TupleProgram.transfer_eval 34 27 0 1 (by decide) (by decide)
    (RecordPrograms.state outerPorts (baseState ctx regs builder)
      false true false tail candidate.reverse)
  convert h using 1
  · simp [RecordPrograms.state,outerPorts]
  · apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [workState,baseState,StackRoutines.transferStacks,
      RecordPrograms.state,outerPorts]

theorem updateCandidate_eval (ctx : Context) (hc : ctx.Valid) (regs : Fin 16 → Bool)
    (tail builder candidate : List Bool) (hw : candidate.length = ctx.width.length) :
    Eval updateCandidate
      (CandidateArrayProgram.sourceCost (original ctx).length ctx.before.length ctx.width.length)
      (workState ctx regs tail candidate [] [] [] builder)
      (workState ctx (readRegs regs 0 1 none) tail candidate (updated ctx candidate) [] [] builder) := by
  let a := workState ctx regs tail candidate [] [] [] builder
  let smallIn := CandidateArrayProgram.state (regs ∘ arrayRegisters)
    (original ctx) candidate ctx.index ctx.width [] []
  let smallOut := CandidateArrayProgram.state (readRegs (regs ∘ arrayRegisters) 0 1 none)
    (original ctx) candidate ctx.index ctx.width (updated ctx candidate) []
  have hin : embedState arrayRegisters arrayStacks a smallIn = a := by
    apply embed_eq _ _ _ _ _ arrayRegisters_injective arrayStacks_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [a,smallIn,workState,arrayStacks]
    · intros; rfl
    · intros; rfl
  have hout : embedState arrayRegisters arrayStacks a smallOut =
      workState ctx (readRegs regs 0 1 none) tail candidate (updated ctx candidate) [] [] builder := by
    apply embed_eq _ _ _ _ _ arrayRegisters_injective arrayStacks_injective
    · intro i
      fin_cases i <;> simp [smallOut,workState,arrayRegisters,readRegs]
    · intro i
      fin_cases i <;> simp [smallOut,workState,arrayStacks]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [arrayRegisters] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,by simpa [arrayRegisters] using h.symm⟩
      simp [workState,a,readRegs,h0,h1]
    · intro i hi
      have h13 : i ≠ 13 := fun h => hi ⟨8,by simpa [arrayStacks] using h.symm⟩
      simp [workState,a,h13]
  have ht := CandidateArrayProgram.program_trace (regs ∘ arrayRegisters)
    ctx.before ctx.old candidate ctx.after.flatten ctx.index ctx.width
    hc.index_length hc.before_width hc.old_width hw
  have he := eval_call_lifted CandidateArrayProgram.program arrayRegisters arrayStacks a
    arrayRegisters_injective arrayStacks_injective ht
  change Eval updateCandidate
    (CandidateArrayProgram.sourceCost (original ctx).length ctx.before.length ctx.width.length)
    (embedState arrayRegisters arrayStacks a smallIn)
    (embedState arrayRegisters arrayStacks a smallOut) at he
  rw [hin,hout] at he
  exact he

theorem copyPairs_eval (ctx : Context) (regs : Fin 16 → Bool)
    (tail builder candidate current : List Bool) :
    Eval copyPairs (7 * (PairScoreProgram.pairRecords ctx.pairs).length + 5)
      (workState ctx regs tail candidate current [] [] builder)
      (workState ctx (readRegs regs 0 1 none) tail candidate current []
        (PairScoreProgram.pairRecords ctx.pairs) builder) := by
  have h := TupleProgram.copy_eval 31 20 33 0 1 (by decide) (by decide)
    (by decide) (by decide) (workState ctx regs tail candidate current [] [] builder)
    (by simp [workState])
  convert h using 1
  · simp [workState]
  · apply congrArg₂ StructuredProgram.State.mk rfl
    funext j; fin_cases j <;> simp [workState,StackRoutines.copyStacks]

theorem resetLow_work (ctx : Context) (regs : Fin 16 → Bool)
    (tail builder candidate current : List Bool)
    (h13 : regs 13 = false) (h14 : regs 14 = true) (h15 : regs 15 = false) :
    Eval resetLow 13
      (workState ctx regs tail candidate current [] (PairScoreProgram.pairRecords ctx.pairs) builder)
      (workState ctx pairStartRegs tail candidate current [] (PairScoreProgram.pairRecords ctx.pairs) builder) := by
  have h := resetLow_eval
    (workState ctx regs tail candidate current [] (PairScoreProgram.pairRecords ctx.pairs) builder)
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;>
      simp [resetValues_apply,lowRegisters,List.mem_map,
        Fin.exists_fin_succ,workState,pairStartRegs,h13,h14,h15]
  · rfl

theorem runPairs_eval (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hw : candidate.length = ctx.width.length) (tail builder : List Bool) :
    ∃ n ≤ PairScoreProgram.sourceBudget (pairContext ctx candidate) ctx.pairs,
      Eval runPairs n
        (workState ctx pairStartRegs tail candidate (updated ctx candidate) []
          (PairScoreProgram.pairRecords ctx.pairs) builder)
        (workState ctx scoredRegs tail candidate (updated ctx candidate)
          (UnaryCompare.encode (candidateScore ctx candidate)) [] builder) := by
  let a := workState ctx pairStartRegs tail candidate (updated ctx candidate) []
    (PairScoreProgram.pairRecords ctx.pairs) builder
  let b := workState ctx scoredRegs tail candidate (updated ctx candidate)
    (UnaryCompare.encode (candidateScore ctx candidate)) [] builder
  have hin : embedState lowRegisters lowStacks a (PairScoreProgram.inputState (pairContext ctx candidate) ctx.pairs) = a := by
    apply embed_eq _ _ _ _ _ lowRegisters_injective lowStacks_injective
    · intro i
      rw [PairScoreProgram.inputState_regs]
      fin_cases i <;> simp [a,workState,pairStartRegs,lowRegisters,Fin.castAdd]
    · intro i
      rw [PairScoreProgram.inputState_stacks]
      fin_cases i <;> simp [a,workState,pairContext,updated,lowStacks,Fin.castAdd,
        List.flatten_append,List.flatten_cons]
    · intros; rfl
    · intros; rfl
  have hout : embedState lowRegisters lowStacks a (PairScoreProgram.outputState (pairContext ctx candidate) ctx.pairs) = b := by
    apply embed_eq _ _ _ _ _ lowRegisters_injective lowStacks_injective
    · intro i
      rw [PairScoreProgram.outputState_regs]
      fin_cases i <;> simp [b,workState,scoredRegs,lowRegisters,Fin.castAdd]
    · intro i
      rw [PairScoreProgram.outputState_stacks]
      fin_cases i <;> simp [b,workState,pairContext,updated,candidateScore,lowStacks,Fin.castAdd,
        List.flatten_append,List.flatten_cons]
    · intro i hi
      have h11 : i ≠ 11 := fun h => hi ⟨11,by simpa [lowRegisters] using h.symm⟩
      simp [a,b,workState,pairStartRegs,scoredRegs,h11]
    · intro i hi
      have h18 : i ≠ 18 := fun h => hi ⟨18,by simpa [lowStacks] using h.symm⟩
      have h20 : i ≠ 20 := fun h => hi ⟨20,by simpa [lowStacks] using h.symm⟩
      simp [a,b,workState,h18,h20]
  obtain ⟨n,hn,ht⟩ := PairScoreProgram.program_run (pairContext ctx candidate) ctx.pairs
    (pairContext_valid ctx hc candidate hw) (pairContext_pairs ctx hc candidate)
  have he := eval_call_lifted PairScoreProgram.program lowRegisters lowStacks a
    lowRegisters_injective lowStacks_injective ht
  exact ⟨n,hn,by simpa only [hin,hout,runPairs,a,b] using he⟩

theorem finish_eval (ctx : Context) (candidate tail builder : List Bool) :
    Eval (.seq emitScore cleanup)
      (4 * candidateScore ctx candidate + 8 + (2 * (updated ctx candidate).length + 3) +
        (2 * candidate.length + 3))
      (workState ctx scoredRegs tail candidate (updated ctx candidate)
        (UnaryCompare.encode (candidateScore ctx candidate)) [] builder)
      (workState ctx finishedRegs tail [] [] [] []
        (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder)) := by
  let a := workState ctx scoredRegs tail candidate (updated ctx candidate)
    (UnaryCompare.encode (candidateScore ctx candidate)) [] builder
  let b := emittedScore a
  let c : State 16 36 := ⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks 13 b.stacks⟩
  let d : State 16 36 := ⟨readRegs c.regs 0 1 none,StackRoutines.clearStacks 27 c.stacks⟩
  have h1 := emitScore_eval a
  have h2 := TupleProgram.clear_eval 13 0 1 b
  have h3 := TupleProgram.clear_eval 27 0 1 c
  have hend : d = workState ctx finishedRegs tail [] [] [] []
      (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [c,b,a,emittedScore,reverseWritten,TupleProgram.pushedState,
        workState,readRegs,scoredRegs,finishedRegs]
    · funext i
      fin_cases i <;> simp [c,b,a,emittedScore,reverseWritten,TupleProgram.pushedState,
        workState,StackRoutines.clearStacks,reverseRecord,TupleProgram.frame_eq_escaped,
        List.reverse_append,List.append_assoc]
  have h := h1.seq (h2.seq h3)
  change Eval (.seq emitScore cleanup) _ a d at h
  rw [hend] at h
  convert h using 1 ;
    simp [a,b,c,emittedScore,reverseWritten,TupleProgram.pushedState,workState,
      StackRoutines.clearStacks,UnaryCompare.encode,Nat.add_assoc]

def callbackCost (ctx : Context) (candidate : List Bool) : ℕ :=
  CandidateArrayProgram.sourceCost (original ctx).length ctx.before.length ctx.width.length +
    PairScoreProgram.sourceBudget (pairContext ctx candidate) ctx.pairs +
    4 * candidateScore ctx candidate + 5 * candidate.length + 2 * (updated ctx candidate).length +
    7 * (PairScoreProgram.pairRecords ctx.pairs).length + 35

theorem callback_eval (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hw : candidate.length = ctx.width.length) (regs : Fin 16 → Bool) (tail builder : List Bool) :
    ∃ n ≤ callbackCost ctx candidate,
      Eval callback n
        (RecordPrograms.state outerPorts (baseState ctx regs builder)
          false true false tail candidate.reverse)
        (RecordPrograms.state outerPorts
          (baseState ctx finishedRegs (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder))
          false true false tail []) := by
  let r0 := (RecordPrograms.state outerPorts (baseState ctx regs builder)
    false true false tail candidate.reverse).regs
  let r1 := readRegs r0 0 1 none
  let r2 := readRegs r1 0 1 none
  let r3 := readRegs r2 0 1 none
  have h1 := transferCandidate_eval ctx regs tail builder candidate
  have h2 := updateCandidate_eval ctx hc r1 tail builder candidate hw
  have h3 := copyPairs_eval ctx r2 tail builder candidate (updated ctx candidate)
  have h4 := resetLow_work ctx r3 tail builder candidate (updated ctx candidate)
    (by simp [r3,r2,r1,r0,readRegs,RecordPrograms.state,outerPorts])
    (by simp [r3,r2,r1,r0,readRegs,RecordPrograms.state,outerPorts])
    (by simp [r3,r2,r1,r0,readRegs,RecordPrograms.state,outerPorts])
  obtain ⟨n,hn,h5⟩ := runPairs_eval ctx hc candidate hw tail builder
  have h6 := finish_eval ctx candidate tail builder
  have hend : workState ctx finishedRegs tail [] [] [] []
      (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder) =
      RecordPrograms.state outerPorts
        (baseState ctx finishedRegs (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder))
        false true false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [workState,baseState,outerPorts,finishedRegs]
    · funext i; fin_cases i <;> simp [workState,baseState,outerPorts]
  rw [hend] at h6
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  refine ⟨_,?_,h⟩
  dsimp [callbackCost]
  omega

def invariant (ctx : Context) (a : State 16 36) : Prop :=
  ∃ regs builder, a = baseState ctx regs builder

def effect (ctx : Context) (candidate : List Bool) (a b : State 16 36) : Prop :=
  b.stacks 35 = reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) (a.stacks 35)

theorem callback_contract (ctx : Context) (hc : ctx.Valid) :
    RecordPrograms.CallbackContractWithOn outerPorts callback (fun _ => false)
      (callbackCost ctx) (invariant ctx) (effect ctx)
      (fun candidate => candidate.length = ctx.width.length) := by
  rintro candidate tail base hw ⟨regs,builder,rfl⟩
  obtain ⟨n,hn,he⟩ := callback_eval ctx hc candidate hw regs tail builder
  refine ⟨n,baseState ctx finishedRegs
    (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder),hn,
    ⟨_,_,rfl⟩,?_,he⟩
  simp [effect,baseState,workState]

def scoreRecords (ctx : Context) : List (List Bool) :=
  ctx.candidates.map fun candidate => UnaryCompare.encode (candidateScore ctx candidate)

theorem reverseRecord_fold (records : List (List Bool)) (out : List Bool) :
    records.foldl (fun acc bits => reverseRecord bits acc) out =
      (TupleProgram.appendEncoded records []).reverse ++ out := by
  induction records generalizing out with
  | nil => simp [TupleProgram.appendEncoded]
  | cons bits rest ih =>
      rw [List.foldl_cons,ih]
      simp [reverseRecord,TupleProgram.appendEncoded,
        TupleProgram.prependRecord,List.reverse_append,List.reverse_cons,List.append_assoc]

theorem reverseRecord_finish (records : List (List Bool)) :
    (false :: (TupleProgram.appendEncoded records []).reverse).reverse =
      ProgramEncoding.encodeRecords records := by
  induction records with
  | nil => rfl
  | cons bits rest ih =>
      simpa [TupleProgram.appendEncoded,TupleProgram.prependRecord,
        ProgramEncoding.encodeRecords,Encoding.encodeList,List.reverse_append,
        List.reverse_cons,List.append_assoc] using congrArg (fun out => true :: (Encoding.frame bits ++ out)) ih

abbrev copyCandidates : Cmd 16 36 := .call (StackRoutines.copyProgram 30 29 33 0 1)
abbrev iterateCandidates : Cmd 16 36 := RecordPrograms.iterate outerPorts callback

abbrev finish : Cmd 16 36 :=
  .seq (TupleProgram.pushConst 35 0 false) (.call (StackRoutines.transferProgram 35 32 0 1))

abbrev command : Cmd 16 36 := .seq copyCandidates (.seq iterateCandidates finish)
def program := StructuredCalls.compiled command 30 32

def inputState (ctx : Context) (regs : Fin 16 → Bool) : State 16 36 := baseState ctx regs []
def outputState (ctx : Context) (regs : Fin 16 → Bool) : State 16 36 :=
  ⟨regs,Function.update (baseState ctx regs []).stacks 32 (ProgramEncoding.encodeRecords (scoreRecords ctx))⟩

@[simp] theorem outputState_output (ctx : Context) (regs : Fin 16 → Bool) :
    (outputState ctx regs).stacks 32 = ProgramEncoding.encodeRecords (scoreRecords ctx) := by
  simp [outputState]

theorem outputState_stack_frame (ctx : Context) (regs initialRegs : Fin 16 → Bool)
    (i : Fin 36) (hi : i ≠ 32) :
    (outputState ctx regs).stacks i = (inputState ctx initialRegs).stacks i := by
  simp [outputState,inputState,baseState,workState,hi]

@[simp] theorem scoreRecords_length (ctx : Context) :
    (scoreRecords ctx).length = ctx.candidates.length := by simp [scoreRecords]

def sourceBudget (ctx : Context) : ℕ :=
  7 * (ProgramEncoding.encodeRecords ctx.candidates).length +
    RecordPrograms.budget (callbackCost ctx) ctx.candidates +
    3 * (ProgramEncoding.encodeRecords (scoreRecords ctx)).length + 14

theorem copyCandidates_eval (ctx : Context) (regs : Fin 16 → Bool) :
    Eval copyCandidates (7 * (ProgramEncoding.encodeRecords ctx.candidates).length + 5)
      (inputState ctx regs)
      (RecordPrograms.state outerPorts (baseState ctx (readRegs regs 0 1 none) [])
        (regs 13) (regs 14) (regs 15) (ProgramEncoding.encodeRecords ctx.candidates) []) := by
  have h := TupleProgram.copy_eval 30 29 33 0 1 (by decide) (by decide)
    (by decide) (by decide) (inputState ctx regs) (by simp [inputState,baseState,workState])
  convert h using 1
  · simp [inputState, baseState, workState]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [inputState,baseState,workState,outerPorts,readRegs]
    · funext i; fin_cases i <;> simp [inputState,baseState,workState,outerPorts,StackRoutines.copyStacks]

theorem iterateCandidates_eval (ctx : Context) (hc : ctx.Valid) (regs : Fin 16 → Bool) :
    ∃ n r, n ≤ 3 + RecordPrograms.budget (callbackCost ctx) ctx.candidates ∧
      Eval iterateCandidates n
        (RecordPrograms.state outerPorts (baseState ctx (readRegs regs 0 1 none) [])
          (regs 13) (regs 14) (regs 15) (ProgramEncoding.encodeRecords ctx.candidates) [])
        (baseState ctx r (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse) := by
  obtain ⟨n,next,hn,hnext,history,he⟩ := RecordPrograms.iterate_run_with_on
    outerPorts callback (fun _ => false) (callbackCost ctx) (invariant ctx) (effect ctx)
    (fun candidate => candidate.length = ctx.width.length) (callback_contract ctx hc)
    ctx.candidates [] (baseState ctx (readRegs regs 0 1 none) []) hc.candidate_width
    ⟨_,_,rfl⟩ (regs 13) (regs 14) (regs 15)
  obtain ⟨r,builder,rfl⟩ := hnext
  have hbuilder : builder = (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse := by
    have h := history.fold_of_false (by simp) (fun d => d.stacks 35)
      (fun acc candidate => reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) acc)
      (fun _ _ _ h => h)
    have hfold : ctx.candidates.foldl
        (fun acc candidate => reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) acc) [] =
        (scoreRecords ctx).foldl (fun acc bits => reverseRecord bits acc) [] := by
      simp [scoreRecords,List.foldl_map]
    simpa [baseState,workState,hfold,reverseRecord_fold] using h
  subst builder
  let r' := (RecordPrograms.state outerPorts (baseState ctx r []) false true false [] []).regs
  have hend : RecordPrograms.state outerPorts
      (baseState ctx r (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse)
      false true false [] [] =
      baseState ctx r' (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;> simp [baseState,workState,outerPorts]
  have hany : ctx.candidates.any (fun _ => false) = false := by
    induction ctx.candidates <;> simp_all
  refine ⟨n,r',hn,?_⟩
  simpa only [hany,TupleProgram.unread_false,hend,ProgramEncoding.encodeRecords,
    List.append_nil,iterateCandidates] using he

theorem finish_run (ctx : Context) (regs : Fin 16 → Bool) :
    ∃ r, Eval finish (3 * (ProgramEncoding.encodeRecords (scoreRecords ctx)).length + 5)
      (baseState ctx regs (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse)
      (outputState ctx r) := by
  let a := baseState ctx regs (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse
  let b := TupleProgram.pushedState 35 0 false a
  let r := readRegs b.regs 0 1 none
  have h1 := TupleProgram.pushConst_eval 35 0 false a
  have h2 := TupleProgram.transfer_eval 35 32 0 1 (by decide) (by decide) b
  have hbytes : (b.stacks 35).reverse = ProgramEncoding.encodeRecords (scoreRecords ctx) := by
    simpa [b,a,TupleProgram.pushedState,baseState,workState] using reverseRecord_finish (scoreRecords ctx)
  have hlen : (b.stacks 35).length = (ProgramEncoding.encodeRecords (scoreRecords ctx)).length := by
    simpa using congrArg List.length hbytes
  have hflat : TupleProgram.appendEncoded (scoreRecords ctx) [] ++ [false] =
      ProgramEncoding.encodeRecords (scoreRecords ctx) := by
    simpa using reverseRecord_finish (scoreRecords ctx)
  have hend : (⟨readRegs b.regs 0 1 none,StackRoutines.transferStacks 35 32 b.stacks⟩ : State 16 36) =
      outputState ctx r := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [StackRoutines.transferStacks,hflat,b,a,baseState,workState]
  rw [hend] at h2
  refine ⟨r,?_⟩
  convert h1.seq h2 using 1 ; simp [hlen] ; omega

theorem program_run (ctx : Context) (hc : ctx.Valid) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn program (sourceBudget ctx)
      ((inputState ctx regs).withPC (some program.entry)) ((outputState ctx finalRegs).withPC none) := by
  have hcopy := copyCandidates_eval ctx regs
  obtain ⟨n,r,hn,hi⟩ := iterateCandidates_eval ctx hc regs
  obtain ⟨finalRegs,hf⟩ := finish_run ctx r
  refine ⟨finalRegs,_,?_,StructuredCalls.compiled_halt_trace (hcopy.seq (hi.seq hf)) 30 32⟩
  dsimp [sourceBudget]
  omega

theorem primitive_run (ctx : Context) (hc : ctx.Valid) (regs : Fin 16 → Bool) :
    ∃ finalRegs, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * sourceBudget ctx)
      (BitProgram.primitiveCfg program ((inputState ctx regs).withPC (some program.entry)))
      (BitProgram.primitiveCfg program ((outputState ctx finalRegs).withPC none)) := by
  obtain ⟨finalRegs,hr⟩ := program_run ctx hc regs
  exact ⟨finalRegs,BitProgram.primitive_execution program hr⟩

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
