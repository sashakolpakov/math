import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawArgumentService
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Fixed physical layout for reading a coordinate-major Taylor cache. -/
namespace SubexponentialSAT.SubexpCacheArgument

open BitProgram StructuredCalls SubexpScanPrimitives

structure Inputs where
  beta : List Bool
  negative : List Bool
  cache : List Bool
  dimension : ℕ
  keyWidth : ℕ

abbrev unary (n : ℕ) := List.replicate n true

def flags (v p mark u saved tag present spare : Bool) : Fin 8 → Bool :=
  ![v,p,mark,u,saved,tag,present,spare]

def machine (regs : Fin 8 → Bool) (I : Inputs)
    (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) : State 8 24 :=
  ⟨regs, ![I.beta,I.negative,I.cache,unary I.dimension,unary I.keyWidth,
    output,outer,outerPayload,inner,innerPayload,unary i,unary right,unary j,[],
    unary left,unary keyRight,unary z,unary width,key,coefficient,[],[],[],[]]⟩

@[simp] theorem machine_eta (regs regs' : Fin 8 → Bool) (I : Inputs)
    (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    ({ regs := regs,
       «stacks» := (machine regs' I output outer outerPayload inner innerPayload i right j
         coefficient key left keyRight z width).stacks } : State 8 24) =
      machine regs I output outer outerPayload inner innerPayload i right j
        coefficient key left keyRight z width := by
  rfl

def ready (regs : Fin 8 → Bool) (I : Inputs)
    (output outer outerPayload inner innerPayload : List Bool) (i right j : ℕ) : State 8 24 :=
  machine regs I output outer outerPayload inner innerPayload i right j [] [] 0 0 0 0

def reset (regs : Fin 8 → Bool) : Fin 8 → Bool := readRegs regs 0 1 none
def finish (regs : Fin 8 → Bool) : Fin 8 → Bool := Function.update (Function.update regs 0 true) 1 false

abbrev atom (a : StructuredProgram.Atom 8 24) : Cmd 8 24 := .base (.atom a)
abbrev copy (src dst : Fin 24) : Cmd 8 24 := .call (StackRoutines.copyProgram src dst 13 0 1)
abbrev transfer (src dst : Fin 24) : Cmd 8 24 := .call (StackRoutines.transferProgram src dst 0 1)
abbrev clear (src : Fin 24) : Cmd 8 24 := .call (StackRoutines.clearProgram src 0 1)
abbrev pushTrue (dst : Fin 24) : Cmd 8 24 := .seq (atom (.set 0 true)) (atom (.push dst 0))

def serviceRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def servicePorts : Fin 10 → Fin 24 := ![19,18,14,5,15,16,17,20,21,22]
def serviceProgram := ProgramLinking.liftProgram SubexpRawArgumentService.program serviceRegs servicePorts

abbrev emitPrepared : Cmd 8 24 := .call serviceProgram

abbrev emitVariable : Cmd 8 24 :=
  .seq (transfer 9 19) (.seq (copy 10 14) (.seq (copy 11 15)
    (.seq (copy 12 16) (.seq (copy 4 17) emitPrepared))))

def innerPorts : RecordPrograms.Ports 8 24 where
  tag := 5
  present := 6
  found := 7
  source := 8
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def outerPorts : RecordPrograms.Ports 8 24 where
  tag := 5
  present := 6
  found := 7
  source := 6
  payload := 7
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev innerBody : Cmd 8 24 :=
  .seq (RecordPrograms.reader innerPorts) (.seq emitVariable
    (.seq (pushTrue 12) (.seq (atom (.set 3 false)) (atom (.pop 8 5 6)))))
abbrev innerLoop : Cmd 8 24 := .while 5 innerBody

abbrev innerRun : Cmd 8 24 := .seq (atom (.pop 8 5 6)) innerLoop

abbrev outerBody : Cmd 8 24 :=
  .seq (RecordPrograms.reader outerPorts) (.seq (transfer 7 8)
    (.seq (atom (.set 3 true)) (.seq innerRun (.seq (clear 12)
      (.seq (pushTrue 10) (.seq (atom (.pop 11 0 1)) (atom (.pop 6 5 6))))))))
abbrev outerLoop : Cmd 8 24 := .while 5 outerBody

abbrev emitConstant (src : Fin 24) (u : Bool) : Cmd 8 24 :=
  .seq (atom (.set 2 false)) (.seq (atom (.set 3 u))
    (.seq (copy src 19) (.seq (copy 3 14) (.seq (copy 4 17) emitPrepared))))

abbrev command : Cmd 8 24 :=
  .seq (emitConstant 0 false) (.seq (emitConstant 1 true)
    (.seq (copy 2 6) (.seq (copy 3 11) (.seq (atom (.pop 11 0 1))
      (.seq (atom (.set 2 true)) (.seq (atom (.pop 6 5 6))
        (.seq outerLoop (clear 10))))))))

def program := compiled command 0 5

@[simp] theorem reset_reset (regs : Fin 8 → Bool) : reset (reset regs) = reset regs :=
  StackRoutines.readRegs_reset _ _ _ _

@[simp] theorem finish_reset (regs : Fin 8 → Bool) : finish (reset regs) = finish regs := by
  funext k; fin_cases k <;> simp [finish,reset,readRegs]

@[simp] theorem reset_flags (v p mark u saved tag present spare : Bool) :
    reset (flags v p mark u saved tag present spare) = flags false false mark u saved tag present spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem finish_flags (v p mark u saved tag present spare : Bool) :
    finish (flags v p mark u saved tag present spare) = flags true false mark u saved tag present spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem machine_stack_0 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 0 = I.beta := rfl

@[simp] theorem machine_stack_1 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 1 = I.negative := rfl

@[simp] theorem machine_stack_2 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 2 = I.cache := rfl

@[simp] theorem machine_stack_3 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 3 = unary I.dimension := rfl

@[simp] theorem machine_stack_4 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 4 = unary I.keyWidth := rfl

@[simp] theorem machine_stack_5 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 5 = output := rfl

@[simp] theorem machine_stack_6 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 6 = outer := rfl

@[simp] theorem machine_stack_7 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 7 = outerPayload := rfl

@[simp] theorem machine_stack_8 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 8 = inner := rfl

@[simp] theorem machine_stack_9 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 9 = innerPayload := rfl

@[simp] theorem machine_stack_10 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 10 = unary i := rfl

@[simp] theorem machine_stack_11 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 11 = unary right := rfl

@[simp] theorem machine_stack_12 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 12 = unary j := rfl

@[simp] theorem machine_stack_13 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 13 = [] := rfl

@[simp] theorem machine_stack_14 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 14 = unary left := rfl

@[simp] theorem machine_stack_15 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 15 = unary keyRight := rfl

@[simp] theorem machine_stack_16 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 16 = unary z := rfl

@[simp] theorem machine_stack_17 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 17 = unary width := rfl

@[simp] theorem machine_stack_18 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 18 = key := rfl

@[simp] theorem machine_stack_19 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 19 = coefficient := rfl

@[simp] theorem machine_stack_20 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 20 = [] := rfl

@[simp] theorem machine_stack_21 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 21 = [] := rfl

@[simp] theorem machine_stack_22 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 22 = [] := rfl

@[simp] theorem machine_stack_23 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 23 = [] := rfl

@[simp] theorem machine_regs (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) : (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).regs = regs := rfl

@[simp] theorem machine_update_5 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : List Bool) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 5 (next) = (machine regs I next outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_6 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : List Bool) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 6 (next) = (machine regs I output next outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_7 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : List Bool) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 7 (next) = (machine regs I output outer next inner innerPayload i right j coefficient key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_8 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : List Bool) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 8 (next) = (machine regs I output outer outerPayload next innerPayload i right j coefficient key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_9 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : List Bool) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 9 (next) = (machine regs I output outer outerPayload inner next i right j coefficient key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_10 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : ℕ) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 10 (unary next) = (machine regs I output outer outerPayload inner innerPayload next right j coefficient key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_11 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : ℕ) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 11 (unary next) = (machine regs I output outer outerPayload inner innerPayload i next j coefficient key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_12 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : ℕ) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 12 (unary next) = (machine regs I output outer outerPayload inner innerPayload i right next coefficient key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_14 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : ℕ) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 14 (unary next) = (machine regs I output outer outerPayload inner innerPayload i right j coefficient key next keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_15 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : ℕ) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 15 (unary next) = (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left next z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_16 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : ℕ) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 16 (unary next) = (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight next width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_17 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : ℕ) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 17 (unary next) = (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z next).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_18 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : List Bool) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 18 (next) = (machine regs I output outer outerPayload inner innerPayload i right j coefficient next left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

@[simp] theorem machine_update_19 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (next : List Bool) :
    Function.update (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks 19 (next) = (machine regs I output outer outerPayload inner innerPayload i right j next key left keyRight z width).stacks := by
  funext k; fin_cases k <;> simp

theorem copy_10_14 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (_left keyRight z width : ℕ) :
    Eval (copy 10 14) (7 * i + 5)
      (machine regs I output outer outerPayload inner innerPayload i right j coefficient key 0 keyRight z width) (machine (reset regs) I output outer outerPayload inner innerPayload i right j coefficient key i keyRight z width) := by
  have h := copy_eval (machine regs I output outer outerPayload inner innerPayload i right j coefficient key 0 keyRight z width) 10 14 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_10,machine_stack_14,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_14,machine_regs,
    machine_eta,reset] using h

theorem copy_11_15 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left _keyRight z width : ℕ) :
    Eval (copy 11 15) (7 * right + 5)
      (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left 0 z width) (machine (reset regs) I output outer outerPayload inner innerPayload i right j coefficient key left right z width) := by
  have h := copy_eval (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left 0 z width) 11 15 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_11,machine_stack_15,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_15,machine_regs,
    machine_eta,reset] using h

theorem copy_12_16 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight _z width : ℕ) :
    Eval (copy 12 16) (7 * j + 5)
      (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight 0 width) (machine (reset regs) I output outer outerPayload inner innerPayload i right j coefficient key left keyRight j width) := by
  have h := copy_eval (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight 0 width) 12 16 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_12,machine_stack_16,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_16,machine_regs,
    machine_eta,reset] using h

theorem copy_4_17 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z _width : ℕ) :
    Eval (copy 4 17) (7 * I.keyWidth + 5)
      (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z 0) (machine (reset regs) I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z I.keyWidth) := by
  have h := copy_eval (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z 0) 4 17 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_4,machine_stack_17,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_17,machine_regs,
    machine_eta,reset] using h

theorem copy_3_14 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (_left keyRight z width : ℕ) :
    Eval (copy 3 14) (7 * I.dimension + 5)
      (machine regs I output outer outerPayload inner innerPayload i right j coefficient key 0 keyRight z width) (machine (reset regs) I output outer outerPayload inner innerPayload i right j coefficient key I.dimension keyRight z width) := by
  have h := copy_eval (machine regs I output outer outerPayload inner innerPayload i right j coefficient key 0 keyRight z width) 3 14 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_3,machine_stack_14,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_14,machine_regs,
    machine_eta,reset] using h

theorem copy_3_11 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i _right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (copy 3 11) (7 * I.dimension + 5)
      (machine regs I output outer outerPayload inner innerPayload i 0 j coefficient key left keyRight z width) (machine (reset regs) I output outer outerPayload inner innerPayload i I.dimension j coefficient key left keyRight z width) := by
  have h := copy_eval (machine regs I output outer outerPayload inner innerPayload i 0 j coefficient key left keyRight z width) 3 11 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_3,machine_stack_11,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_11,machine_regs,
    machine_eta,reset] using h

theorem copy_0_19 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (_coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (copy 0 19) (7 * (I.beta).length + 5)
      (machine regs I output outer outerPayload inner innerPayload i right j [] key left keyRight z width) (machine (reset regs) I output outer outerPayload inner innerPayload i right j I.beta key left keyRight z width) := by
  have h := copy_eval (machine regs I output outer outerPayload inner innerPayload i right j [] key left keyRight z width) 0 19 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_0,machine_stack_19,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_19,machine_regs,
    machine_eta,reset] using h

theorem copy_1_19 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (_coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (copy 1 19) (7 * (I.negative).length + 5)
      (machine regs I output outer outerPayload inner innerPayload i right j [] key left keyRight z width) (machine (reset regs) I output outer outerPayload inner innerPayload i right j I.negative key left keyRight z width) := by
  have h := copy_eval (machine regs I output outer outerPayload inner innerPayload i right j [] key left keyRight z width) 1 19 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_1,machine_stack_19,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_19,machine_regs,
    machine_eta,reset] using h

theorem copy_2_6 (regs : Fin 8 → Bool) (I : Inputs) (output _outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (copy 2 6) (7 * (I.cache).length + 5)
      (machine regs I output [] outerPayload inner innerPayload i right j coefficient key left keyRight z width) (machine (reset regs) I output I.cache outerPayload inner innerPayload i right j coefficient key left keyRight z width) := by
  have h := copy_eval (machine regs I output [] outerPayload inner innerPayload i right j coefficient key left keyRight z width) 2 6 13 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  simpa only [copy,afterCopy,machine_stack_2,machine_stack_6,List.length_replicate,
    List.replicate_zero,List.append_nil,StackRoutines.copyStacks,machine_update_6,machine_regs,
    machine_eta,reset] using h

theorem transfer_9_19 (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner _innerPayload : List Bool)
    (i right j : ℕ) (_coefficient key : List Bool) (left keyRight z width : ℕ) (bits : List Bool) :
    Eval (transfer 9 19) (3 * bits.length + 3)
      (machine regs I output outer outerPayload inner bits.reverse i right j [] key left keyRight z width) (machine (reset regs) I output outer outerPayload inner [] i right j bits key left keyRight z width) := by
  have h := transfer_eval (machine regs I output outer outerPayload inner bits.reverse i right j [] key left keyRight z width) 9 19 0 1 (by decide) (by decide)
  simpa only [transfer,afterTransfer,machine_stack_9,machine_stack_19,List.length_reverse,
    StackRoutines.transferStacks,machine_update_9,machine_update_19,List.reverse_reverse,
    List.append_nil,machine_regs,machine_eta,reset] using h

theorem transfer_7_8 (regs : Fin 8 → Bool) (I : Inputs) (output outer _outerPayload _inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (bits : List Bool) :
    Eval (transfer 7 8) (3 * bits.length + 3)
      (machine regs I output outer bits.reverse [] innerPayload i right j coefficient key left keyRight z width) (machine (reset regs) I output outer [] bits innerPayload i right j coefficient key left keyRight z width) := by
  have h := transfer_eval (machine regs I output outer bits.reverse [] innerPayload i right j coefficient key left keyRight z width) 7 8 0 1 (by decide) (by decide)
  simpa only [transfer,afterTransfer,machine_stack_7,machine_stack_8,List.length_reverse,
    StackRoutines.transferStacks,machine_update_7,machine_update_8,List.reverse_reverse,
    List.append_nil,machine_regs,machine_eta,reset] using h

theorem set_machine (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (dst : Fin 8) (b : Bool) :
    Eval (atom (.set dst b)) 1 (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width) (machine (Function.update regs dst b) I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem clear_i (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (clear 10) (2*i+3) (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width) (machine (reset regs) I output outer outerPayload inner innerPayload 0 right j coefficient key left keyRight z width) := by
  have h := ListRegisterProgram.clear_run (10 : Fin 24) (0 : Fin 8) 1 regs (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks
  have hs :
      (machine regs I output outer outerPayload inner innerPayload 0 right j coefficient
        key left keyRight z width).stacks =
      (machine (reset regs) I output outer outerPayload inner innerPayload 0 right j
        coefficient key left keyRight z width).stacks := by
    rfl
  rw [machine_stack_10, List.length_replicate, StackRoutines.clearStacks,
    ← List.replicate_zero (a := true), machine_update_10, hs] at h
  exact Eval.call _ h

theorem push_i (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (pushTrue 10) 2 (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width) (machine (Function.update regs 0 true) I output outer outerPayload inner innerPayload (i+1) right j coefficient key left keyRight z width) := by
  have h1 := set_machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width 0 true
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (10 : Fin 24) (0 : Fin 8))
    (machine (Function.update regs 0 true) I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width))
  have h := h1.seq h2
  simpa only [pushTrue,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,machine_regs,
    machine_stack_10,Function.update_self,← List.replicate_succ,machine_update_10,
    machine_eta] using h

theorem clear_j (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (clear 12) (2*j+3) (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width) (machine (reset regs) I output outer outerPayload inner innerPayload i right 0 coefficient key left keyRight z width) := by
  have h := ListRegisterProgram.clear_run (12 : Fin 24) (0 : Fin 8) 1 regs (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width).stacks
  have hs :
      (machine regs I output outer outerPayload inner innerPayload i right 0 coefficient
        key left keyRight z width).stacks =
      (machine (reset regs) I output outer outerPayload inner innerPayload i right 0
        coefficient key left keyRight z width).stacks := by
    rfl
  rw [machine_stack_12, List.length_replicate, StackRoutines.clearStacks,
    ← List.replicate_zero (a := true), machine_update_12, hs] at h
  exact Eval.call _ h

theorem push_j (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (pushTrue 12) 2 (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width) (machine (Function.update regs 0 true) I output outer outerPayload inner innerPayload i right (j+1) coefficient key left keyRight z width) := by
  have h1 := set_machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width 0 true
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (12 : Fin 24) (0 : Fin 8))
    (machine (Function.update regs 0 true) I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width))
  have h := h1.seq h2
  simpa only [pushTrue,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,machine_regs,
    machine_stack_12,Function.update_self,← List.replicate_succ,machine_update_12,
    machine_eta] using h

@[simp] theorem unary_head (n : ℕ) : (unary n).head?.getD false = decide (0 < n) := by
  cases n <;> simp [unary,List.replicate_succ]
@[simp] theorem unary_present (n : ℕ) : (unary n).head?.isSome = decide (0 < n) := by
  cases n <;> simp [unary,List.replicate_succ]
@[simp] theorem unary_tail (n : ℕ) : (unary n).tail = unary (n-1) := by cases n <;> rfl

theorem pop_right (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) :
    Eval (atom (.pop 11 0 1)) 1 (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width) (machine (readRegs regs 0 1 (unary right).head?) I output outer outerPayload inner innerPayload i (right-1) j coefficient key left keyRight z width) := by
  have h := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (11 : Fin 24) (0 : Fin 8) 1)
    (machine regs I output outer outerPayload inner innerPayload i right j coefficient key left keyRight z width))
  simpa only [atom,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,machine_regs,
    machine_stack_11,unary_tail,machine_update_11,machine_eta] using h

theorem pop_outer (regs : Fin 8 → Bool) (I : Inputs) (output _outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (b : Bool) (tail : List Bool) :
    Eval (atom (.pop 6 5 6)) 1 (machine regs I output (b::tail) outerPayload inner innerPayload i right j coefficient key left keyRight z width) (machine (readRegs regs 5 6 (some b)) I output tail outerPayload inner innerPayload i right j coefficient key left keyRight z width) := by
  have h := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.pop (6 : Fin 24) (5 : Fin 8) 6) (machine regs I output (b::tail) outerPayload inner innerPayload i right j coefficient key left keyRight z width))
  simpa only [atom,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,machine_regs,
    machine_stack_6,List.head?_cons,List.tail_cons,machine_update_6,machine_eta] using h

theorem pop_inner (regs : Fin 8 → Bool) (I : Inputs) (output outer outerPayload _inner innerPayload : List Bool)
    (i right j : ℕ) (coefficient key : List Bool) (left keyRight z width : ℕ) (b : Bool) (tail : List Bool) :
    Eval (atom (.pop 8 5 6)) 1 (machine regs I output outer outerPayload (b::tail) innerPayload i right j coefficient key left keyRight z width) (machine (readRegs regs 5 6 (some b)) I output outer outerPayload tail innerPayload i right j coefficient key left keyRight z width) := by
  have h := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.pop (8 : Fin 24) (5 : Fin 8) 6) (machine regs I output outer outerPayload (b::tail) innerPayload i right j coefficient key left keyRight z width))
  simpa only [atom,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,machine_regs,
    machine_stack_8,List.head?_cons,List.tail_cons,machine_update_8,machine_eta] using h

@[simp] theorem flags_0 (v p mark u saved tag present spare : Bool) : flags v p mark u saved tag present spare 0 = v := rfl

@[simp] theorem update_flags_0 (v p mark u saved tag present spare b : Bool) :
    Function.update (flags v p mark u saved tag present spare) 0 b = flags b p mark u saved tag present spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem flags_1 (v p mark u saved tag present spare : Bool) : flags v p mark u saved tag present spare 1 = p := rfl

@[simp] theorem update_flags_1 (v p mark u saved tag present spare b : Bool) :
    Function.update (flags v p mark u saved tag present spare) 1 b = flags v b mark u saved tag present spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem flags_2 (v p mark u saved tag present spare : Bool) : flags v p mark u saved tag present spare 2 = mark := rfl

@[simp] theorem update_flags_2 (v p mark u saved tag present spare b : Bool) :
    Function.update (flags v p mark u saved tag present spare) 2 b = flags v p b u saved tag present spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem flags_3 (v p mark u saved tag present spare : Bool) : flags v p mark u saved tag present spare 3 = u := rfl

@[simp] theorem update_flags_3 (v p mark u saved tag present spare b : Bool) :
    Function.update (flags v p mark u saved tag present spare) 3 b = flags v p mark b saved tag present spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem flags_4 (v p mark u saved tag present spare : Bool) : flags v p mark u saved tag present spare 4 = saved := rfl

@[simp] theorem update_flags_4 (v p mark u saved tag present spare b : Bool) :
    Function.update (flags v p mark u saved tag present spare) 4 b = flags v p mark u b tag present spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem flags_5 (v p mark u saved tag present spare : Bool) : flags v p mark u saved tag present spare 5 = tag := rfl

@[simp] theorem update_flags_5 (v p mark u saved tag present spare b : Bool) :
    Function.update (flags v p mark u saved tag present spare) 5 b = flags v p mark u saved b present spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem flags_6 (v p mark u saved tag present spare : Bool) : flags v p mark u saved tag present spare 6 = present := rfl

@[simp] theorem update_flags_6 (v p mark u saved tag present spare b : Bool) :
    Function.update (flags v p mark u saved tag present spare) 6 b = flags v p mark u saved tag b spare := by
  funext k; fin_cases k <;> rfl

@[simp] theorem flags_7 (v p mark u saved tag present spare : Bool) : flags v p mark u saved tag present spare 7 = spare := rfl

@[simp] theorem update_flags_7 (v p mark u saved tag present spare b : Bool) :
    Function.update (flags v p mark u saved tag present spare) 7 b = flags v p mark u saved tag present b := by
  funext k; fin_cases k <;> rfl

end SubexponentialSAT.SubexpCacheArgument

end OAI.Algorithms
