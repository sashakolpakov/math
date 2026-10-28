import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanContractBridge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleBridge

namespace OAI.Algorithms

/-! Shared native coefficient-ring ABI. All service programs have fixed size. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Public ports are result0, modulus5, operands8/9, degree11, width12,
base scalar zero17, and cached k-major table22. Other fields are private work. -/
structure ServiceStore where
  modulus : List Bool
  result : List Bool
  x : List Bool
  y : List Bool
  degree : List Bool
  width : List Bool
  zero : List Bool
  table : List Bool
  outer : List Bool := []
  inner : List Bool := []
  tableWork : List Bool := []
  reverseStream : List Bool := []
  stream : List Bool := []

def serviceTapes (s : ServiceStore) : Fin 32 → List Bool := fun i =>
  if i = 0 then s.result else if i = 5 then s.modulus
  else if i = 8 then s.x else if i = 9 then s.y else if i = 11 then s.degree
  else if i = 12 then s.width else if i = 15 then s.outer else if i = 16 then s.inner
  else if i = 17 then s.zero else if i = 20 then s.tableWork
  else if i = 21 then s.reverseStream else if i = 22 then s.table
  else if i = 23 then s.stream else []

def serviceWorkState (regs : Fin 8 → Bool) (s : ServiceStore) : State 8 32 :=
  ⟨regs, serviceTapes s⟩

def serviceState (regs : Fin 8 → Bool)
    (modulus result x y degree width zero table : List Bool) : State 8 32 :=
  serviceWorkState regs ⟨modulus, result, x, y, degree, width, zero, table, [], [], [], [], []⟩

abbrev serviceCopy (src dst : Fin 32) : Cmd 8 32 := .call (copyProgram src dst 31 1 3)
abbrev serviceClear (dst : Fin 32) : Cmd 8 32 := .call (clearProgram dst 1 3)
abbrev serviceTransfer (src dst : Fin 32) : Cmd 8 32 := .call (transferProgram src dst 1 3)

def serviceAfterCopy (s : State 8 32) (src dst : Fin 32) : State 8 32 :=
  ⟨readRegs s.regs 1 3 none, copyStacks src dst s.stacks⟩
def serviceAfterClear (s : State 8 32) (dst : Fin 32) : State 8 32 :=
  ⟨readRegs s.regs 1 3 none, clearStacks dst s.stacks⟩
def serviceAfterTransfer (s : State 8 32) (src dst : Fin 32) : State 8 32 :=
  ⟨readRegs s.regs 1 3 none, transferStacks src dst s.stacks⟩

theorem serviceCopy_eval (s : State 8 32) (src dst : Fin 32)
    (hsd : src ≠ dst) (hs : src ≠ 31) (hd : (31 : Fin 32) ≠ dst) (ht : s.stacks 31 = []) :
    Eval (serviceCopy src dst) (7*(s.stacks src).length+5) s (serviceAfterCopy s src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 31 1 3 hsd hs hd (by decide) s.regs s.stacks ht)

theorem serviceClear_eval (s : State 8 32) (dst : Fin 32) :
    Eval (serviceClear dst) (2*(s.stacks dst).length+3) s (serviceAfterClear s dst) :=
  .call _ (ListRegisterProgram.clear_run dst 1 3 s.regs s.stacks)

theorem serviceTransfer_eval (s : State 8 32) (src dst : Fin 32) (hne : src ≠ dst) :
    Eval (serviceTransfer src dst) (3*(s.stacks src).length+3) s (serviceAfterTransfer s src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 1 3 hne (by decide) s.regs s.stacks)

abbrev servicePrepare : Cmd 8 32 := serviceCopy 22 20

theorem servicePrepare_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    Eval servicePrepare (7*s.table.length+5)
      (serviceWorkState regs {s with tableWork := []})
      (serviceWorkState (readRegs regs 1 3 none) {s with tableWork := s.table}) := by
  have h := serviceCopy_eval (serviceWorkState regs {s with tableWork := []}) 22 20
    (by decide) (by decide) (by decide) (by rfl)
  convert h using 1
  · rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [serviceWorkState, serviceTapes, copyStacks]

abbrev serviceRoute : Cmd 8 32 := .seq (serviceClear 8) (.seq (serviceClear 9)
  (.seq (serviceTransfer 23 21) (serviceTransfer 21 9)))

theorem serviceRoute_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    Eval serviceRoute (2*s.x.length + 2*s.y.length + 6*s.stream.length + 12)
      (serviceWorkState regs {s with reverseStream := []})
      (serviceWorkState (readRegs regs 1 3 none) {s with x := [], y := s.stream, reverseStream := [], stream := []}) := by
  let a := serviceWorkState regs {s with reverseStream := []}
  let b := serviceAfterClear a 8
  let c := serviceAfterClear b 9
  let d := serviceAfterTransfer c 23 21
  have h1 := serviceClear_eval a 8
  have h2 := serviceClear_eval b 9
  have h3 := serviceTransfer_eval c 23 21 (by decide)
  have h4 := serviceTransfer_eval d 21 9 (by decide)
  have he := h1.seq (h2.seq (h3.seq h4))
  have hf : serviceAfterTransfer d 21 9 =
      serviceWorkState (readRegs regs 1 3 none) {s with x := [], y := s.stream, reverseStream := [], stream := []} := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [d, c, b, a, serviceAfterTransfer, serviceAfterClear, serviceWorkState, readRegs_reset]
    · funext i; fin_cases i <;>
        simp [d, c, b, a, serviceAfterTransfer, serviceAfterClear, serviceWorkState,
          serviceTapes, clearStacks, transferStacks]
  rw [hf] at he
  convert he using 1
  simp [d, c, b, a, serviceAfterTransfer, serviceAfterClear, serviceWorkState,
    serviceTapes, clearStacks, transferStacks]
  omega

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
