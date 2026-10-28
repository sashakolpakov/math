import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/
namespace SubexponentialSAT.Subexp.PackingLeftoverEmitter

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 9
abbrev Code := Cmd 8 9

private def workState (regs : Fin 8 → Bool)
    (vertex rank address storage metadata addresses scratch temp frame : List Bool) : Data :=
  ⟨regs, ![vertex,rank,address,storage,metadata,addresses,scratch,temp,frame]⟩

def state (regs : Fin 8 → Bool)
    (vertex rank address storage metadata addresses : List Bool) : Data :=
  workState regs vertex rank address storage metadata addresses [] [] []

def metadataPayload (rank : List Bool) : List Bool := false :: Encoding.frame rank

def storageOutput (vertex storage : List Bool) : List Bool :=
  (true :: Encoding.frame vertex).reverse ++ storage

def metadataOutput (vertex rank metadata : List Bool) : List Bool :=
  Encoding.frame vertex ++ (Encoding.frame (metadataPayload rank) ++ metadata)

def addressOutput (vertex address addresses : List Bool) : List Bool :=
  Encoding.frame vertex ++ (Encoding.frame address ++ addresses)

private def sequence (commands : List Code) : Code :=
  commands.foldr Cmd.seq (.base .skip)

def command : Code := sequence [
  MatrixProgramSupport.copy 0 7 6, emitFrame 7 8 6 (by decide),
  TupleProgram.pushConst 8 0 true, transfer 8 3,
  MatrixProgramSupport.copy 1 7 6, emitFrame 7 8 6 (by decide),
  TupleProgram.pushConst 8 0 false, emitFrame 8 4 6 (by decide),
  MatrixProgramSupport.copy 0 7 6, emitFrame 7 4 6 (by decide),
  MatrixProgramSupport.copy 2 7 6, emitFrame 7 5 6 (by decide),
  emitFrame 0 5 6 (by decide),
  TupleProgram.pushConst 1 0 true, TupleProgram.pushConst 2 0 true]

abbrev program : Program 8 9 (size command+1) := compiled command 0 3

def commandCost (vertex rank address : List Bool) : ℕ :=
  44*vertex.length+31*rank.length+15*address.length+101

theorem command_eval_exact (vertex rank address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Eval command (commandCost vertex rank address)
      (state regs vertex rank address storage metadata addresses)
      (state rf [] (true::rank) (true::address) (storageOutput vertex storage)
        (metadataOutput vertex rank metadata) (addressOutput vertex address addresses)) := by
  let a0 := workState regs vertex rank address storage metadata addresses [] [] []
  obtain ⟨d1,h1,s1⟩ := copy_eval (0 : Fin 9) 7 6 (by decide) (by decide) (by decide) a0 rfl
  let a1 := workState d1.regs
    vertex rank address storage metadata addresses [] vertex []
  have e1 : d1 = a1 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s1]
    funext j
    fin_cases j <;> simp [a0,workState,StackRoutines.copyStacks]
  rw [e1] at h1
  obtain ⟨d2,h2,s2⟩ := emitFrame_eval (7 : Fin 9) 8 6 (by decide) (by decide) (by decide) a1 rfl
  let a2 := workState d2.regs
    vertex rank address storage metadata addresses [] [] (Encoding.frame vertex)
  have e2 : d2 = a2 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s2]
    funext j
    fin_cases j <;> simp [a1,workState]
  rw [e2] at h2
  have h3 := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) true a2
  let a3 := workState (Function.update a2.regs 0 true)
    vertex rank address storage metadata addresses [] [] (true :: (Encoding.frame vertex))
  have e3 : TupleProgram.pushedState 8 0 true a2 = a3 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a2,workState]
  rw [e3] at h3
  obtain ⟨d4,h4,s4⟩ := transfer_eval (8 : Fin 9) 3 (by decide) a3
  let a4 := workState d4.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] [] []
  have e4 : d4 = a4 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s4]
    funext j
    fin_cases j <;> simp [a3,workState,StackRoutines.transferStacks]
  rw [e4] at h4
  obtain ⟨d5,h5,s5⟩ := copy_eval (1 : Fin 9) 7 6 (by decide) (by decide) (by decide) a4 rfl
  let a5 := workState d5.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] rank []
  have e5 : d5 = a5 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s5]
    funext j
    fin_cases j <;> simp [a4,workState,StackRoutines.copyStacks]
  rw [e5] at h5
  obtain ⟨d6,h6,s6⟩ := emitFrame_eval (7 : Fin 9) 8 6 (by decide) (by decide) (by decide) a5 rfl
  let a6 := workState d6.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] [] (Encoding.frame rank)
  have e6 : d6 = a6 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s6]
    funext j
    fin_cases j <;> simp [a5,workState]
  rw [e6] at h6
  have h7 := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) false a6
  let a7 := workState (Function.update a6.regs 0 false)
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] [] (false :: (Encoding.frame rank))
  have e7 : TupleProgram.pushedState 8 0 false a6 = a7 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a6,workState]
  rw [e7] at h7
  obtain ⟨d8,h8,s8⟩ := emitFrame_eval (8 : Fin 9) 4 6 (by decide) (by decide) (by decide) a7 rfl
  let a8 := workState d8.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata) addresses [] [] []
  have e8 : d8 = a8 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s8]
    funext j
    fin_cases j <;> simp [a7,workState]
  rw [e8] at h8
  obtain ⟨d9,h9,s9⟩ := copy_eval (0 : Fin 9) 7 6 (by decide) (by decide) (by decide) a8 rfl
  let a9 := workState d9.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata) addresses [] vertex []
  have e9 : d9 = a9 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s9]
    funext j
    fin_cases j <;> simp [a8,workState,StackRoutines.copyStacks]
  rw [e9] at h9
  obtain ⟨d10,h10,s10⟩ := emitFrame_eval (7 : Fin 9) 4 6 (by decide) (by decide) (by decide) a9 rfl
  let a10 := workState d10.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) addresses [] [] []
  have e10 : d10 = a10 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s10]
    funext j
    fin_cases j <;> simp [a9,workState]
  rw [e10] at h10
  obtain ⟨d11,h11,s11⟩ := copy_eval (2 : Fin 9) 7 6 (by decide) (by decide) (by decide) a10 rfl
  let a11 := workState d11.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) addresses [] address []
  have e11 : d11 = a11 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s11]
    funext j
    fin_cases j <;> simp [a10,workState,StackRoutines.copyStacks]
  rw [e11] at h11
  obtain ⟨d12,h12,s12⟩ := emitFrame_eval (7 : Fin 9) 5 6 (by decide) (by decide) (by decide) a11 rfl
  let a12 := workState d12.regs
    vertex rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) (Encoding.frame address ++ addresses) [] [] []
  have e12 : d12 = a12 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s12]
    funext j
    fin_cases j <;> simp [a11,workState]
  rw [e12] at h12
  obtain ⟨d13,h13,s13⟩ := emitFrame_eval (0 : Fin 9) 5 6 (by decide) (by decide) (by decide) a12 rfl
  let a13 := workState d13.regs
    [] rank address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e13 : d13 = a13 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s13]
    funext j
    fin_cases j <;> simp [a12,workState]
  rw [e13] at h13
  have h14 := TupleProgram.pushConst_eval (1 : Fin 9) (0 : Fin 8) true a13
  let a14 := workState (Function.update a13.regs 0 true)
    [] (true :: rank) address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e14 : TupleProgram.pushedState 1 0 true a13 = a14 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a13,workState]
  rw [e14] at h14
  have h15 := TupleProgram.pushConst_eval (2 : Fin 9) (0 : Fin 8) true a14
  let a15 := workState (Function.update a14.regs 0 true)
    [] (true :: rank) (true :: address) ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (false :: (Encoding.frame rank)) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e15 : TupleProgram.pushedState 2 0 true a14 = a15 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a14,workState]
  rw [e15] at h15
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14.seq (h15.seq ((.base (.skip a15)))))))))))))))))
  have hcost : (7*(a0.stacks 0).length+5)+((8*(a1.stacks 7).length+8)+(2+((3*(a3.stacks 8).length+3)+((7*(a4.stacks 1).length+5)+((8*(a5.stacks 7).length+8)+(2+((8*(a7.stacks 8).length+8)+((7*(a8.stacks 0).length+5)+((8*(a9.stacks 7).length+8)+((7*(a10.stacks 2).length+5)+((8*(a11.stacks 7).length+8)+((8*(a12.stacks 0).length+8)+(2+(2+(0))))))))))))))) = commandCost vertex rank address := by
    simp [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,workState,commandCost,Encoding.length_frame]
    ring
  rw [hcost] at hrun
  exact ⟨a15.regs,hrun⟩

theorem program_trace (vertex rank address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Trace program (commandCost vertex rank address+1)
      ((state regs vertex rank address storage metadata addresses).withPC (some program.entry))
      ((state rf [] (true::rank) (true::address) (storageOutput vertex storage)
        (metadataOutput vertex rank metadata) (addressOutput vertex address addresses)).withPC none) := by
  obtain ⟨rf,h⟩ := command_eval_exact vertex rank address storage metadata addresses regs
  exact ⟨rf,compiled_halt_trace h 0 3⟩

end SubexponentialSAT.Subexp.PackingLeftoverEmitter

namespace SubexponentialSAT.Subexp.PackingCoveredQuery

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 5 6

abbrev core : Cmd 5 6 := .seq (SelectorProgram.atom (.set 4 false))
  (.seq SelectorProgram.peek SelectorProgram.scan)

abbrev command : Cmd 5 6 := .seq core
  (.seq (.call (StackRoutines.clearProgram 0 0 1))
    (.seq (.call (StackRoutines.clearProgram 2 0 1))
      (.call (StackRoutines.clearProgram 5 0 1))))

def program := compiled command 0 5

def state (regs : Fin 5 → Bool) (source query output : List Bool) : Data :=
  SubexpRecordScan.recordState regs source [] query [] [] output

def budget (query : List Bool) (records : List (List Bool × List Bool)) : ℕ :=
  5*SelectorProgram.scanBudget query records +
    2*(SelectorProgram.rawRecords records).length+2*query.length+23

/-- The actual selector is followed by physical cleanup. Only its found flag
survives, so no fallback value can be mistaken for a covered vertex. -/
theorem command_eval (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ n ≤ budget query records, ∃ rf,
      Eval command n (state regs (SelectorProgram.rawRecords records) query.reverse [])
        (state rf [] [] []) ∧ rf 4 = (records.lookup query).isSome := by
  let r0 := Function.update regs 4 false
  let a := state regs (SelectorProgram.rawRecords records) query.reverse []
  have h0 : Eval (SelectorProgram.atom (.set 4 false)) 1 a
      (state r0 (SelectorProgram.rawRecords records) query.reverse []) := by
    exact .base (.atom _ _)
  have hp := SelectorProgram.peek_eval r0 (SelectorProgram.rawRecords records) query.reverse []
  obtain ⟨n,hn,rs,tail,hs,hflag⟩ := SelectorProgram.scan_eval query records r0 (by simp [r0])
  let result := SelectorProgram.framedResult (records.lookup query)
  let b := state rs tail query.reverse result
  have hcore : Eval core (1+(1+n)) a b := h0.seq (hp.seq hs)
  have ht := compiled_halt_trace hcore 0 5
  have htail : tail.length ≤ (SelectorProgram.rawRecords records).length+n+3 := by
    have h := SequentialProgram.trace_stack_length_le ht 0
    change tail.length ≤ (SelectorProgram.rawRecords records).length+(1+(1+n)+1) at h
    omega
  have hresult : result.length ≤ n+3 := by
    have h := SequentialProgram.trace_stack_length_le ht 5
    change result.length ≤ 0+(1+(1+n)+1) at h
    omega
  let r1 := readRegs rs 0 1 none
  let c := state r1 [] query.reverse result
  have h1 : Eval (.call (StackRoutines.clearProgram (0 : Fin 6) (0 : Fin 5) 1))
      (2*tail.length+3) b c := by
    have h := TupleProgram.clear_eval (0 : Fin 6) (0 : Fin 5) 1 b
    have he : (⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks 0 b.stacks⟩ : Data) = c := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j
      fin_cases j <;> simp [b,state,SubexpRecordScan.recordState,StackRoutines.clearStacks]
    rw [he] at h
    exact h
  let r2 := readRegs r1 0 1 none
  let d := state r2 [] [] result
  have h2 : Eval (.call (StackRoutines.clearProgram (2 : Fin 6) (0 : Fin 5) 1))
      (2*query.length+3) c d := by
    have h := TupleProgram.clear_eval (2 : Fin 6) (0 : Fin 5) 1 c
    have he : (⟨readRegs c.regs 0 1 none,StackRoutines.clearStacks 2 c.stacks⟩ : Data) = d := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j
      fin_cases j <;> simp [c,state,SubexpRecordScan.recordState,StackRoutines.clearStacks]
    rw [he] at h
    simpa [c,state,SubexpRecordScan.recordState] using h
  let r3 := readRegs r2 0 1 none
  let e := state r3 [] [] []
  have h3 : Eval (.call (StackRoutines.clearProgram (5 : Fin 6) (0 : Fin 5) 1))
      (2*result.length+3) d e := by
    have h := TupleProgram.clear_eval (5 : Fin 6) (0 : Fin 5) 1 d
    have he : (⟨readRegs d.regs 0 1 none,StackRoutines.clearStacks 5 d.stacks⟩ : Data) = e := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j
      fin_cases j <;> simp [d,state,SubexpRecordScan.recordState,StackRoutines.clearStacks]
    rw [he] at h
    exact h
  refine ⟨_,?_,r3,hcore.seq (h1.seq (h2.seq h3)),?_⟩
  · dsimp [budget]
    omega
  · simpa [r3,r2,r1,readRegs] using hflag

theorem program_trace (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ n ≤ budget query records+1, ∃ rf,
      Trace program n
        ((state regs (SelectorProgram.rawRecords records) query.reverse []).withPC (some program.entry))
        ((state rf [] [] []).withPC none) ∧ rf 4 = (records.lookup query).isSome := by
  obtain ⟨n,hn,rf,he,hf⟩ := command_eval query records regs
  exact ⟨n+1,by omega,rf,compiled_halt_trace he 0 5,hf⟩

theorem scanBudget_le (query : List Bool) (records : List (List Bool × List Bool)) :
    SelectorProgram.scanBudget query records ≤
      (9*query.length+20)*(SelectorProgram.rawRecords records).length+1 := by
  induction records with
  | nil => simp [SelectorProgram.scanBudget,SelectorProgram.rawRecords]
  | cons p records ih =>
      rcases p with ⟨key,value⟩
      have hlen : (SelectorProgram.rawRecords ((key,value)::records)).length =
          2*key.length+2*value.length+2+(SelectorProgram.rawRecords records).length := by
        simp [SelectorProgram.rawRecords,Encoding.length_frame]
        omega
      have hlocal : 17*key.length+9*query.length+13*value.length+40 ≤
          (9*query.length+20)*(2*key.length+2*value.length+2) := by
        nlinarith [Nat.zero_le (query.length*key.length),Nat.zero_le (query.length*value.length)]
      rw [SelectorProgram.scanBudget,SubexpRecordScan.recordCost,hlen]
      nlinarith

theorem budget_le (query : List Bool) (records : List (List Bool × List Bool)) :
    budget query records ≤
      (45*query.length+102)*(SelectorProgram.rawRecords records).length+2*query.length+28 := by
  have h := scanBudget_le query records
  dsimp [budget]
  nlinarith

end SubexponentialSAT.Subexp.PackingCoveredQuery


end OAI.Algorithms
