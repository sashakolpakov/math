import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseOperandIO

namespace OAI.Algorithms

/-!
# Physical operand wrappers for dense projection and addition

The wrappers parse the actual top operand records, copy the retained-slot
master, invoke a fixed finite local arithmetic program, clear its copied
inputs, frame the result, and reset the interpreter registers. Local core
execution is an explicit trace premise until instantiated by the concrete
projection/addition theorems.
-/

namespace SubexponentialSAT.SubexpDenseOperandWrappers

open BitProgram StructuredCalls SubexpScanPrimitives SubexpDenseOperandIO

abbrev Data := State 16 128

def coreRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def coreStacks : Fin 26 → Fin 128 := Fin.castAdd 102

theorem coreRegs_injective : Function.Injective coreRegs := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem coreStacks_injective : Function.Injective coreStacks := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 128 => i.val) h)

def localState (d : Data) : State 8 26 :=
  ⟨d.regs ∘ coreRegs, d.stacks ∘ coreStacks⟩

def coreOutput (d : Data) (regs : Fin 8 → Bool) (bits : List Bool) : Data :=
  ⟨Fin.addCases (m := 8) (n := 8) (motive := fun _ => Bool)
      regs (fun i : Fin 8 => d.regs (Fin.natAdd 8 i)),
    Function.update (Function.update d.stacks 20 []) 21 bits⟩

def localOutput (d : Data) (regs : Fin 8 → Bool) (bits : List Bool) : State 8 26 :=
  ⟨regs, Function.update (Function.update (localState d).stacks 20 []) 21 bits⟩

abbrev coreCall {l : ℕ} (core : Program 8 26 l) : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram core coreRegs coreStacks)

theorem coreCall_eval {l n : ℕ} (core : Program 8 26 l) (d : Data)
    (regs : Fin 8 → Bool) (bits : List Bool)
    (h : Trace core n ((localState d).withPC (some core.entry))
      ((localOutput d regs bits).withPC none)) :
    Eval (coreCall core) n d (coreOutput d regs bits) := by
  have hi : embedState coreRegs coreStacks d (localState d) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ coreRegs_injective coreStacks_injective
    · intro i; rfl
    · intros; rfl
    · intro i; rfl
    · intros; rfl
  have ho : embedState coreRegs coreStacks d (localOutput d regs bits) =
      coreOutput d regs bits := by
    apply embedState_eq_of_ports _ _ _ _ _ coreRegs_injective coreStacks_injective
    · intro i
      simp [coreOutput, localOutput, coreRegs]
    · intro j hj
      revert hj
      refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) j
      · intro hj
        exact False.elim (hj ⟨i, rfl⟩)
      · intro _
        exact Fin.addCases_right (m := 8) (n := 8)
          (motive := fun _ => Bool) (left := regs)
          (right := fun j : Fin 8 => d.regs (Fin.natAdd 8 j)) i
    · intro i
      fin_cases i <;> rfl
    · intro j hj
      have h20 : j ≠ 20 := fun h => hj ⟨20, by simpa [coreStacks] using h.symm⟩
      have h21 : j ≠ 21 := fun h => hj ⟨21, by simpa [coreStacks] using h.symm⟩
      simp [coreOutput, h20, h21]
  simpa only [coreCall, hi, ho] using
    eval_call_lifted core coreRegs coreStacks d coreRegs_injective coreStacks_injective h

abbrev copySlots : Cmd 16 128 := .call (StackRoutines.copyProgram 25 20 24 0 1)

abbrev initializeOutput : Cmd 16 128 :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 21 0)))

def initialized (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 21 (false :: d.stacks 21)⟩

theorem initializeOutput_eval (d : Data) : Eval initializeOutput 2 d (initialized d) := by
  have h₁ := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set
    (s := 128) (0 : Fin 16) false) d)
  have h₂ := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push
    (r := 16) (21 : Fin 128) 0) ((StructuredProgram.Atom.set 0 false).eval d))
  simpa [initializeOutput, initialized, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.withPC,
    StructuredProgram.State.ofCfg, execInstr] using Eval.seq h₁ h₂

abbrev clearInput (src : Fin 128) : Cmd 16 128 :=
  .call (StackRoutines.clearProgram src 0 1)

def cleared (d : Data) (src : Fin 128) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clearInput_eval (d : Data) (src : Fin 128) :
    Eval (clearInput src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  have ht := StackRoutines.halt_after_trace (StackRoutines.clearProgram src 0 1)
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks) 2 rfl rfl
  exact .call _ (by
    simpa [clearInput, cleared, StackRoutines.clearResult, StackRoutines.clearStacks,
      StructuredProgram.State.withPC, Nat.add_assoc] using ht)

def prepared (d : Data) : Data := initialized (afterCopy d 25 20 0 1)

abbrev prepare : Cmd 16 128 := .seq copySlots initializeOutput

theorem prepare_eval (d : Data) (htmp : d.stacks 24 = []) :
    Eval prepare (7 * (d.stacks 25).length + 7) d (prepared d) := by
  have hc := copy_eval d 25 20 24 0 1 (by decide) (by decide) (by decide) (by decide) htmp
  have hi := initializeOutput_eval (afterCopy d 25 20 0 1)
  simpa only [prepare, copySlots, prepared, Nat.add_assoc] using Eval.seq hc hi

def loadPrepared (d : Data) (raw tail : List Bool) : Data :=
  prepared (takeResult d 22 raw tail)

def addPrepared (d : Data) (left right tail : List Bool) : Data :=
  prepared (takeResult (takeResult d 23 right (true :: (Encoding.frame left ++ tail)))
    22 left tail)

abbrev load {l : ℕ} (core : Program 8 26 l) : Cmd 16 128 :=
  .seq (takeOperand 22) (.seq prepare (.seq (coreCall core)
    (.seq (clearInput 22) (.seq putOperand reset))))

abbrev add {l : ℕ} (core : Program 8 26 l) : Cmd 16 128 :=
  .seq (takeOperand 23) (.seq (takeOperand 22) (.seq prepare (.seq (coreCall core)
    (.seq (clearInput 22) (.seq (clearInput 23) (.seq putOperand reset))))))

abbrev loadProgram {l : ℕ} (core : Program 8 26 l) := StructuredCalls.compiled (load core) 27 27
abbrev addProgram {l : ℕ} (core : Program 8 26 l) := StructuredCalls.compiled (add core) 27 27

def result (d : Data) (bits tail : List Bool) : Data :=
  ⟨fun _ => false, Function.update d.stacks 27 (true :: (Encoding.frame bits ++ tail))⟩

theorem loadPrepared_stacks (d : Data) (raw tail : List Bool) :
    (loadPrepared d raw tail).stacks =
      Function.update (Function.update (Function.update (Function.update
        (Function.update d.stacks 27 tail) 22 (raw ++ d.stacks 22)) 29 [])
        20 (d.stacks 25 ++ d.stacks 20)) 21 (false :: d.stacks 21) := by
  simp only [loadPrepared, prepared, initialized, afterCopy,
    takeResult_stack d 22 raw tail (by decide) (by decide)]
  funext i
  by_cases hi27 : i = 27 <;> by_cases hi29 : i = 29 <;>
    by_cases hi22 : i = 22 <;> by_cases hi23 : i = 23 <;>
    simp_all [StackRoutines.copyStacks, Function.update_apply]

theorem addPrepared_stacks (d : Data) (left right tail : List Bool) :
    (addPrepared d left right tail).stacks =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update d.stacks 27 tail) 23 (right ++ d.stacks 23))
        22 (left ++ d.stacks 22)) 29 [])
        20 (d.stacks 25 ++ d.stacks 20)) 21 (false :: d.stacks 21) := by
  simp only [addPrepared, prepared, initialized, afterCopy,
    takeResult_stack _ 22 _ _ (by decide) (by decide),
    takeResult_stack _ 23 _ _ (by decide) (by decide)]
  funext i
  by_cases hi27 : i = 27 <;> by_cases hi29 : i = 29 <;>
    by_cases hi22 : i = 22 <;> by_cases hi23 : i = 23 <;>
    simp_all [StackRoutines.copyStacks, Function.update_apply]

theorem load_eval {l n : ℕ} (core : Program 8 26 l) (d : Data)
    (raw bits tail : List Bool) (regs : Fin 8 → Bool)
    (hin : d.stacks 27 = true :: (Encoding.frame raw ++ tail))
    (h20 : d.stacks 20 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = [])
    (h24 : d.stacks 24 = []) (h29 : d.stacks 29 = [])
    (hcore : Trace core n ((localState (loadPrepared d raw tail)).withPC (some core.entry))
      ((localOutput (loadPrepared d raw tail) regs bits).withPC none)) :
    Eval (load core) (n + 11 * raw.length + 7 * (d.stacks 25).length + 8 * bits.length + 45)
      d (result d bits tail) := by
  let d₁ := takeResult d 22 raw tail
  let d₂ := loadPrepared d raw tail
  let d₃ := coreOutput d₂ regs bits
  let d₄ := cleared d₃ 22
  let d₅ := putResult d₄ bits
  have h₁ := takeOperand_eval d 22 raw tail (by decide) hin h29
  have h₁s := takeResult_stack d 22 raw tail (by decide) (by decide)
  have h₂ := prepare_eval d₁ (by simp [d₁, h₁s, h24])
  have h₃ := coreCall_eval core d₂ regs bits hcore
  have h₄ := clearInput_eval d₃ 22
  have h₂s := loadPrepared_stacks d raw tail
  have h₅ := putOperand_eval d₄ bits
    (by simp [d₄, d₃, coreOutput, cleared])
    (by simp [d₄, d₃, d₂, coreOutput, cleared, h₂s])
  have h₆ := reset_eval d₅
  have he : (⟨fun _ => false, d₅.stacks⟩ : Data) = result d bits tail := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [show d₅.stacks = _ from putResult_stack d₄ bits]
      funext i
      by_cases hi20 : i = 20 <;> by_cases hi21 : i = 21 <;>
        by_cases hi22 : i = 22 <;> by_cases hi27 : i = 27 <;> by_cases hi29 : i = 29 <;>
        simp_all [d₄, d₃, d₂, coreOutput, cleared, result]
  rw [he] at h₆
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄ (Eval.seq h₅ h₆))))
  have hl₁ : (d₁.stacks 25).length = (d.stacks 25).length := by simp [d₁, h₁s]
  have hl₃ : (d₃.stacks 22).length = raw.length := by
    simp [d₃, d₂, coreOutput, h₂s, h22]
  convert h using 1; omega

theorem binary_cleanup_stacks (d out : Data) (left right bits tail : List Bool)
    (h20 : d.stacks 20 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = [])
    (h23 : d.stacks 23 = []) (h29 : d.stacks 29 = [])
    (hout : out.stacks = Function.update
      (Function.update (addPrepared d left right tail).stacks 20 []) 21 bits) :
    (putResult (cleared (cleared out 22) 23) bits).stacks =
      Function.update d.stacks 27 (true :: (Encoding.frame bits ++ tail)) := by
  rw [putResult_stack]
  simp only [cleared, hout, addPrepared_stacks]
  funext i
  by_cases h20' : i = 20
  · subst i; simp [h20]
  by_cases h21' : i = 21
  · subst i; simp [h21]
  by_cases h22' : i = 22
  · subst i; simp [h22]
  by_cases h23' : i = 23
  · subst i; simp [h23]
  by_cases h27' : i = 27
  · subst i; simp
  by_cases h29' : i = 29
  · subst i; simp [h29]
  simp [h20', h21', h22', h23', h27', h29']

theorem add_eval {l n : ℕ} (core : Program 8 26 l) (d : Data)
    (left right bits tail : List Bool) (regs : Fin 8 → Bool)
    (hin : d.stacks 27 = true :: (Encoding.frame right ++
      true :: (Encoding.frame left ++ tail)))
    (h20 : d.stacks 20 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = [])
    (h23 : d.stacks 23 = []) (h24 : d.stacks 24 = []) (h29 : d.stacks 29 = [])
    (hcore : Trace core n ((localState (addPrepared d left right tail)).withPC (some core.entry))
      ((localOutput (addPrepared d left right tail) regs bits).withPC none)) :
    Eval (add core) (n + 11 * (left.length + right.length) +
      7 * (d.stacks 25).length + 8 * bits.length + 56) d (result d bits tail) := by
  let d₁ := takeResult d 23 right (true :: (Encoding.frame left ++ tail))
  let d₂ := takeResult d₁ 22 left tail
  let d₃ := addPrepared d left right tail
  let d₄ := coreOutput d₃ regs bits
  let d₅ := cleared d₄ 22
  let d₆ := cleared d₅ 23
  let d₇ := putResult d₆ bits
  have h₁ := takeOperand_eval d 23 right (true :: (Encoding.frame left ++ tail)) (by decide) hin h29
  have h₁s := takeResult_stack d 23 right (true :: (Encoding.frame left ++ tail)) (by decide) (by decide)
  have h₂ := takeOperand_eval d₁ 22 left tail (by decide)
    (by simp [d₁, h₁s]) (by simp [d₁, h₁s])
  have h₂s := takeResult_stack d₁ 22 left tail (by decide) (by decide)
  have h₃ := prepare_eval d₂ (by simp [d₂, h₂s, d₁, h₁s, h24])
  have h₄ := coreCall_eval core d₃ regs bits hcore
  have h₅ := clearInput_eval d₄ 22
  have h₆ := clearInput_eval d₅ 23
  have h₃s := addPrepared_stacks d left right tail
  have h₇ := putOperand_eval d₆ bits
    (by simp [d₆, d₅, d₄, coreOutput, cleared])
    (by simp [d₆, d₅, d₄, d₃, coreOutput, cleared, h₃s])
  have h₈ := reset_eval d₇
  have he : (⟨fun _ => false, d₇.stacks⟩ : Data) = result d bits tail := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact binary_cleanup_stacks d d₄ left right bits tail h20 h21 h22 h23 h29 rfl
  rw [he] at h₈
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄
    (Eval.seq h₅ (Eval.seq h₆ (Eval.seq h₇ h₈))))))
  have hl₂ : (d₂.stacks 25).length = (d.stacks 25).length := by simp [d₂, h₂s, d₁, h₁s]
  have hl₄ : (d₄.stacks 22).length = left.length := by
    simp [d₄, d₃, coreOutput, h₃s, h22]
  have hl₅ : (d₅.stacks 23).length = right.length := by
    simp [d₅, d₄, d₃, cleared, coreOutput, h₃s, h23]
  convert h using 1; omega

/-- Binary framing reusable by a physical multiplication core as well.
The core may use the larger workspace, provided it restores all stacks
except consumed query port 20 and result port 21. -/
def physicalCoreOutput (d : Data) (regs : Fin 16 → Bool) (bits : List Bool) : Data :=
  ⟨regs, Function.update (Function.update d.stacks 20 []) 21 bits⟩

abbrev binary {l : ℕ} (core : Program 16 128 l) : Cmd 16 128 :=
  .seq (takeOperand 23) (.seq (takeOperand 22) (.seq prepare (.seq (.call core)
    (.seq (clearInput 22) (.seq (clearInput 23) (.seq putOperand reset))))))

abbrev binaryProgram {l : ℕ} (core : Program 16 128 l) :=
  StructuredCalls.compiled (binary core) 27 27

theorem binary_eval {l n : ℕ} (core : Program 16 128 l) (d : Data)
    (left right bits tail : List Bool) (regs : Fin 16 → Bool)
    (hin : d.stacks 27 = true :: (Encoding.frame right ++
      true :: (Encoding.frame left ++ tail)))
    (h20 : d.stacks 20 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = [])
    (h23 : d.stacks 23 = []) (h24 : d.stacks 24 = []) (h29 : d.stacks 29 = [])
    (hcore : Trace core n ((addPrepared d left right tail).withPC (some core.entry))
      ((physicalCoreOutput (addPrepared d left right tail) regs bits).withPC none)) :
    Eval (binary core) (n + 11 * (left.length + right.length) +
      7 * (d.stacks 25).length + 8 * bits.length + 56) d (result d bits tail) := by
  let d₁ := takeResult d 23 right (true :: (Encoding.frame left ++ tail))
  let d₂ := takeResult d₁ 22 left tail
  let d₃ := addPrepared d left right tail
  let d₄ := physicalCoreOutput d₃ regs bits
  let d₅ := cleared d₄ 22
  let d₆ := cleared d₅ 23
  let d₇ := putResult d₆ bits
  have h₁ := takeOperand_eval d 23 right (true :: (Encoding.frame left ++ tail)) (by decide) hin h29
  have h₁s := takeResult_stack d 23 right (true :: (Encoding.frame left ++ tail)) (by decide) (by decide)
  have h₂ := takeOperand_eval d₁ 22 left tail (by decide)
    (by simp [d₁, h₁s]) (by simp [d₁, h₁s])
  have h₂s := takeResult_stack d₁ 22 left tail (by decide) (by decide)
  have h₃ := prepare_eval d₂ (by simp [d₂, h₂s, d₁, h₁s, h24])
  have h₄ : Eval (.call core) n d₃ (physicalCoreOutput d₃ regs bits) := .call core hcore
  have h₅ := clearInput_eval d₄ 22
  have h₆ := clearInput_eval d₅ 23
  have h₃s := addPrepared_stacks d left right tail
  have h₇ := putOperand_eval d₆ bits
    (by simp [d₆, d₅, d₄, physicalCoreOutput, cleared])
    (by simp [d₆, d₅, d₄, d₃, physicalCoreOutput, cleared, h₃s])
  have h₈ := reset_eval d₇
  have he : (⟨fun _ => false, d₇.stacks⟩ : Data) = result d bits tail := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact binary_cleanup_stacks d d₄ left right bits tail h20 h21 h22 h23 h29 rfl
  rw [he] at h₈
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄
    (Eval.seq h₅ (Eval.seq h₆ (Eval.seq h₇ h₈))))))
  have hl₂ : (d₂.stacks 25).length = (d.stacks 25).length := by simp [d₂, h₂s, d₁, h₁s]
  have hl₄ : (d₄.stacks 22).length = left.length := by
    simp [d₄, d₃, physicalCoreOutput, h₃s, h22]
  have hl₅ : (d₅.stacks 23).length = right.length := by
    simp [d₅, d₄, d₃, cleared, physicalCoreOutput, h₃s, h23]
  convert h using 1; omega

end SubexponentialSAT.SubexpDenseOperandWrappers

end OAI.Algorithms
