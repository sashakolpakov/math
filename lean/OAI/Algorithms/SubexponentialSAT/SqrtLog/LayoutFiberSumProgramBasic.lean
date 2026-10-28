import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTotalStream
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheckRead
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Native owner-fiber summation helpers. The remaining fiber is a stream of
actual unary index fields, never an array of precomputed matrix entries. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

abbrev Data := State 16 256
abbrev Code := Cmd 16 256

/-- Only the arithmetic scratch bank must be empty. The entry callback may
require the stronger condition that all stacks below 200 are empty. -/
def ArithmeticReady (base : Data) : Prop :=
  ∀ i : Fin 256, i.val < 11 → base.stacks i = []

def bank (base : Data) (queue column : List Bool) (acc next : WordPair) :
    Fin 256 → List Bool := fun i =>
  if i=212 then acc.1 else if i=213 then acc.2 else if i=214 then queue else
  if i=253 then column else if i=254 then next.1 else if i=255 then next.2 else base.stacks i

def data (base : Data) (regs : Fin 16 → Bool) (queue column : List Bool)
    (acc next : WordPair) : Data := ⟨regs,bank base queue column acc next⟩

def encodeIndices (is : List ℕ) : List Bool := is.flatMap Encoding.encodeNat
def unary (i : ℕ) : List Bool := List.replicate i true

def readIndex : Code := .call (RowSelectionProgramTupleCheck.Read.program 214 253 0 1)

theorem readIndex_eval (base : Data) (regs : Fin 16 → Bool) (i : ℕ)
    (queue : List Bool) (acc : WordPair) :
    Eval readIndex (3*i+3)
      (data base regs (Encoding.encodeNat i++queue) [] acc ([],[]))
      (data base (readRegs regs 0 1 (some false)) queue (unary i) acc ([],[])) := by
  apply Eval.call
  have h := RowSelectionProgramTupleCheck.Read.run (214 : Fin 256) 253
    (0 : Fin 16) 1 (by decide) (by decide) regs
    (bank base (Encoding.encodeNat i++queue) [] acc ([],[])) i queue (by simp [bank])
  convert h using 1
  · simp [RowSelectionProgramTupleCheck.Read.start, data]
  · apply congrArg₂ (Cfg.mk none)
    · rfl
    · funext j
      by_cases hq : j=214
      · subst j; simp [data,bank,unary]
      by_cases hc : j=253
      · subst j; simp [data,bank,unary]
      simp [data,bank,unary,hq,hc]

def clearColumn : Code := .call (StackRoutines.clearProgram 253 0 1)

theorem clearColumn_eval (base : Data) (regs : Fin 16 → Bool)
    (queue column : List Bool) (acc : WordPair) :
    Eval clearColumn (2*column.length+3)
      (data base regs queue column acc ([],[]))
      (data base (readRegs regs 0 1 none) queue [] acc ([],[])) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (253 : Fin 256) (0 : Fin 16) 1
    (data base regs queue column acc ([],[]))
  have he : (⟨readRegs regs 0 1 none,
      StackRoutines.clearStacks 253 (bank base queue column acc ([],[]))⟩ : Data)=
      data base (readRegs regs 0 1 none) queue [] acc ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases hc : j=253
      · subst j; simp [bank,StackRoutines.clearStacks]
      simp [bank,StackRoutines.clearStacks,hc]
  change Eval clearColumn (2*column.length+3) _
    (⟨readRegs regs 0 1 none,
      StackRoutines.clearStacks 253 (bank base queue column acc ([],[]))⟩ : Data) at h
  rw [he] at h
  exact h

def addRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
theorem addRegisters_injective : Function.Injective addRegisters := Fin.castAdd_injective _ _
def addStacks : Fin 16 → Fin 256 := ![212,213,254,255,0,1,2,3,4,5,6,7,8,9,10,214]
theorem addStacks_injective : Function.Injective addStacks := by decide
def addProgram := compiled (RowSelectionProgram.streamOperation false) 0 1
def addEntry : Code := .call (ProgramLinking.liftProgram addProgram addRegisters addStacks)

theorem addEntry_eval (base : Data) (hb : ArithmeticReady base)
    (regs : Fin 16 → Bool) (queue column : List Bool) (acc next : WordPair) :
    ∃ n ≤ 25000*(pairLength acc+pairLength next+3)^2+2, ∃ rf result,
      Eval addEntry n (data base regs queue column acc next)
        (data base rf queue column result ([],[])) ∧
      pairValue result=pairValue acc+pairValue next ∧
      pairTotal result.1 result.2=pairTotal acc.1 acc.2+pairTotal next.1 next.2 ∧
      pairLength result ≤ pairLength acc+pairLength next+2 := by
  obtain ⟨n,hn,rr,result,he,hv,hm,hl⟩ :=
    streamOperation_eval_total false (regs ∘ addRegisters) acc next queue
  let a := data base regs queue column acc next
  have hi : projectState addRegisters addStacks a=
      streamData (regs ∘ addRegisters) acc next queue := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a,data,bank,addStacks] <;>
        exact hb _ (by decide)
  have ht := compiled_halt_trace he 0 1
  change Trace addProgram (n+1)
    ((streamData (regs ∘ addRegisters) acc next queue).withPC (some addProgram.entry))
    ((streamData rr result ([],[]) queue).withPC none) at ht
  rw [←hi] at ht
  have hc := eval_call_from_state addProgram addRegisters addStacks a
    addRegisters_injective addStacks_injective ht
  let rf := (embedState addRegisters addStacks a (streamData rr result ([],[]) queue)).regs
  have ho : embedState addRegisters addStacks a (streamData rr result ([],[]) queue)=
      data base rf queue column result ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hp : ∃ j, addStacks j=i
      · obtain ⟨j,rfl⟩ := hp
        have hh := embedState_stack addRegisters addStacks a
          (streamData rr result ([],[]) queue) addStacks_injective j
        exact hh.trans (by
          fin_cases j <;> simp [bank,addStacks,streamData]
          all_goals exact hb _ (by decide))
      · have hh := embedState_stack_frame addRegisters addStacks a
          (streamData rr result ([],[]) queue) i hp
        have h212 : i≠212 := fun h => hp ⟨0,h.symm⟩
        have h213 : i≠213 := fun h => hp ⟨1,h.symm⟩
        have h254 : i≠254 := fun h => hp ⟨2,h.symm⟩
        have h255 : i≠255 := fun h => hp ⟨3,h.symm⟩
        exact hh.trans (by simp [a,data,bank,h212,h213,h254,h255])
  rw [ho] at hc
  refine ⟨n+1,by omega,rf,result,hc,?_,?_,?_⟩
  · simpa [combine] using hv
  · simpa using hm
  · simpa [wordGrowth] using hl

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
