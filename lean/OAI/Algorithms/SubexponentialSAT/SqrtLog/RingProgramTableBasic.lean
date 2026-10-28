import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanTriple
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! Native primitives used by the companion-table preparation machine. -/
namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Data := State 8 27

/-- The first fifteen ports are the audited scalar/triple scanner ABI. -/
structure Store where
  modulus : List Bool
  left : List Bool := []
  source : List Bool := []
  saved : List Bool := []
  count : List Bool := []
  width : List Bool
  vector : List Bool := []
  coefficients : List Bool := []
  minusOne : List Bool
  tail : List Bool
  newTail : List Bool := []
  output : List Bool := []
  polynomial : List Bool
  degree : List Bool
  zero : List Bool
  powers : List Bool := []
  rounds : List Bool := []

abbrev tapes (s : Store) : Fin 27 → List Bool :=
  ![s.left, [], [], [], [], s.modulus, [], [], [], s.source, s.saved,
    s.count, s.width, [], [], s.vector, s.coefficients, s.minusOne, s.tail,
    s.newTail, s.output, s.polynomial, s.degree, [], s.zero, s.powers, s.rounds]

abbrev state (regs : Fin 8 → Bool) (s : Store) : Data := ⟨regs, tapes s⟩

abbrev clear (dst : Fin 27) : Cmd 8 27 := .call (clearProgram dst 1 3)
abbrev copy (src dst : Fin 27) : Cmd 8 27 := .call (copyProgram src dst 23 1 3)
abbrev transfer (src dst : Fin 27) : Cmd 8 27 := .call (transferProgram src dst 1 3)

def afterClear (d : Data) (dst : Fin 27) : Data :=
  ⟨readRegs d.regs 1 3 none, clearStacks dst d.stacks⟩
def afterCopy (d : Data) (src dst : Fin 27) : Data :=
  ⟨readRegs d.regs 1 3 none, copyStacks src dst d.stacks⟩
def afterTransfer (d : Data) (src dst : Fin 27) : Data :=
  ⟨readRegs d.regs 1 3 none, transferStacks src dst d.stacks⟩

theorem clear_eval (d : Data) (dst : Fin 27) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 1 3 d.regs d.stacks)

theorem copy_eval (d : Data) (src dst : Fin 27)
    (hsd : src ≠ dst) (hs : src ≠ 23) (hd : (23 : Fin 27) ≠ dst)
    (htmp : d.stacks 23 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 23 1 3 hsd hs hd
    (by decide) d.regs d.stacks htmp)

theorem transfer_eval (d : Data) (src dst : Fin 27) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 1 3 hne (by decide) d.regs d.stacks)

def loadRegisters : Fin 2 → Fin 8 := ![1, 3]
theorem loadRegisters_injective : Function.Injective loadRegisters := by decide

def loadPorts (src dst : Fin 27) : Fin 5 → Fin 27 := ![src, dst, 12, 13, 14]
abbrev load (src dst : Fin 27) : Cmd 8 27 := .call
  (ProgramLinking.liftProgram RingScan.loadWordProgram loadRegisters (loadPorts src dst))

def afterLoad (d : Data) (src dst : Fin 27) (word tail : List Bool) : Data :=
  ⟨readRegs d.regs 1 3 none,
    Function.update (Function.update d.stacks src tail) dst (word ++ d.stacks dst)⟩

theorem load_eval (d : Data) (src dst : Fin 27)
    (hinj : Function.Injective (loadPorts src dst)) (word tail : List Bool)
    (hsrc : d.stacks src = word ++ tail) (h13 : d.stacks 13 = []) (h14 : d.stacks 14 = [])
    (hwidth : (d.stacks 12).length = word.length) :
    Eval (load src dst) (14 * word.length + 12) d (afterLoad d src dst word tail) := by
  let a := RingScan.loadState ![d.regs 1, d.regs 3] (word ++ tail)
    (d.stacks dst) (d.stacks 12) [] []
  let b := RingScan.loadState ![false, false] tail
    (word ++ d.stacks dst) (d.stacks 12) [] []
  have ha : embedState loadRegisters (loadPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective hinj
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> first | exact hsrc | exact h13 | exact h14 | rfl
    · intro i hi; rfl
  have hsd : src ≠ dst := by
    intro h
    have : (0 : Fin 5) = 1 := hinj h
    exact (by decide : (0 : Fin 5) ≠ 1) this
  have hds : dst ≠ src := Ne.symm hsd
  have hsp (k : Fin 5) (hk : k ≠ 0) : loadPorts src dst k ≠ src := by
    intro h
    exact hk (hinj h)
  have hdp (k : Fin 5) (hk : k ≠ 1) : loadPorts src dst k ≠ dst := by
    intro h
    exact hk (hinj h)
  have hs12 : (12 : Fin 27) ≠ src := hsp 2 (by decide)
  have hd12 : (12 : Fin 27) ≠ dst := hdp 2 (by decide)
  have hs13 : (13 : Fin 27) ≠ src := hsp 3 (by decide)
  have hd13 : (13 : Fin 27) ≠ dst := hdp 3 (by decide)
  have hs14 : (14 : Fin 27) ≠ src := hsp 4 (by decide)
  have hd14 : (14 : Fin 27) ≠ dst := hdp 4 (by decide)
  have hb : embedState loadRegisters (loadPorts src dst) d b = afterLoad d src dst word tail := by
    apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective hinj
    · intro i; fin_cases i <;> simp [b, RingScan.loadState, afterLoad, loadRegisters, readRegs]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
      simp [afterLoad, readRegs, h1, h3]
    · intro i
      fin_cases i
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, hsd]
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts]
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, hs12, hd12]
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, h13, hs13, hd13]
      · simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, h14, hs14, hd14]
    · intro i hi
      have hs : i ≠ src := fun h => hi ⟨0, h.symm⟩
      have hd : i ≠ dst := fun h => hi ⟨1, h.symm⟩
      simp [afterLoad, hs, hd]
  have ht := RingScan.loadWordProgram_trace ![d.regs 1, d.regs 3] word tail
    (d.stacks dst) (d.stacks 12) hwidth
  have hr : readRegs (![d.regs 1, d.regs 3] : Fin 2 → Bool) 0 1 none = ![false,false] := by
    funext i; fin_cases i <;> rfl
  rw [hr] at ht
  have he := eval_call_lifted RingScan.loadWordProgram loadRegisters (loadPorts src dst) d
    loadRegisters_injective hinj (a := a) (b := b) ht
  simpa only [ha, hb, load] using he


theorem copy_store_eval (s t : Store) (regs : Fin 8 → Bool) (src dst : Fin 27)
    (hsd : src ≠ dst) (hs : src ≠ 23) (hd : (23 : Fin 27) ≠ dst)
    (heq : copyStacks src dst (tapes s) = tapes t) :
    Eval (copy src dst) (7 * (tapes s src).length + 5) (state regs s)
      (state (readRegs regs 1 3 none) t) := by
  have h := copy_eval (state regs s) src dst hsd hs hd (by rfl)
  simpa only [afterCopy, state, heq] using h

theorem clear_store_eval (s t : Store) (regs : Fin 8 → Bool) (dst : Fin 27)
    (heq : clearStacks dst (tapes s) = tapes t) :
    Eval (clear dst) (2 * (tapes s dst).length + 3) (state regs s)
      (state (readRegs regs 1 3 none) t) := by
  have h := clear_eval (state regs s) dst
  simpa only [afterClear, state, heq] using h

theorem transfer_store_eval (s t : Store) (regs : Fin 8 → Bool) (src dst : Fin 27)
    (hne : src ≠ dst) (heq : transferStacks src dst (tapes s) = tapes t) :
    Eval (transfer src dst) (3 * (tapes s src).length + 3) (state regs s)
      (state (readRegs regs 1 3 none) t) := by
  have h := transfer_eval (state regs s) src dst hne
  simpa only [afterTransfer, state, heq] using h

theorem load_store_eval (s t : Store) (regs : Fin 8 → Bool) (src dst : Fin 27)
    (hinj : Function.Injective (loadPorts src dst)) (word tail : List Bool)
    (hsrc : tapes s src = word ++ tail)
    (hwidth : s.width.length = word.length)
    (heq : Function.update (Function.update (tapes s) src tail) dst
      (word ++ tapes s dst) = tapes t) :
    Eval (load src dst) (14 * word.length + 12) (state regs s)
      (state (readRegs regs 1 3 none) t) := by
  have h := load_eval (state regs s) src dst hinj word tail hsrc (by rfl) (by rfl) hwidth
  simpa only [afterLoad, state, heq] using h

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
