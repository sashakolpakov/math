import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSignatureSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramBounds
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.SubexpRecordScan
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

abbrev Data := State 8 16
abbrev Code := Cmd 8 16

def state (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool) : Data :=
  ⟨regs, ![W, [], [], [], [], [], [], [], [], [], [], [], bits, [], key,
    words (rows.map words)]⟩

def signaturePorts : Fin 15 → Fin 16 := Fin.castAdd 1

def command : Code :=
  .seq (copy 15 13 11)
    (.call (ProgramLinking.liftProgram signatureProgram id signaturePorts))

def program := compiled command 12 14

def cost (W bits : List Bool) (rows : List (List (List Bool))) : ℕ :=
  7 * (words (rows.map words)).length + 5 + (signatureCost W bits rows + 2)

theorem command_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool)
    (hlen : ∀ row ∈ rows, row.length = bits.length) :
    ∃ n ≤ cost W bits rows, ∃ out,
      Eval command n (state regs W bits rows key)
        (state out W bits rows (signatureValue W bits rows ++ key)) := by
  let a := state regs W bits rows key
  obtain ⟨b, hb, hbs⟩ := copy_eval (15 : Fin 16) 13 11
    (by decide) (by decide) (by decide) a rfl
  have hproj : projectState id signaturePorts b = signatureState b.regs W bits rows key := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    fin_cases i <;> simp [signaturePorts, hbs, a, state,
      StackRoutines.copyStacks]
  obtain ⟨ns, hns, out, he⟩ := signatureCommand_eval b.regs W bits rows key hlen
  rw [← hproj] at he
  have hc := eval_call_from_state signatureProgram id signaturePorts b
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace he 13 14)
  have hembed : embedState id signaturePorts b
      (signatureState out W bits [] (signatureValue W bits rows ++ key)) =
      state out W bits rows (signatureValue W bits rows ++ key) := by
    apply embedState_eq_of_ports id signaturePorts b _ _ Function.injective_id
      (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i
      fin_cases i <;> simp [signaturePorts, state, signatureState, words]
    · intro i hi
      have hi15 : i = 15 := by
        apply Fin.ext
        by_contra hn
        have hil : i.val < 15 := by have := i.isLt; omega
        exact hi ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
      subst i
      simp [hbs, a, state, StackRoutines.copyStacks]
  rw [hembed] at hc
  exact ⟨_, by dsimp [cost, a, state] at *; omega, out, hb.seq hc⟩

theorem cost_le (W bits : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = bits.length)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) :
    cost W bits rows ≤ 7 * (words (rows.map words)).length +
      rows.length * (signatureRowBound W bits.length B + 2) + 8 := by
  have hs := signatureCost_bound W bits rows B hlen hwidth
  dsimp [cost]
  omega

/-- Every physical bit in the complete key is retained; equality is precisely
full integer-signature equality, including every original raw row. -/
theorem key_eq_iff {h d : ℕ} (W : List Bool)
    (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (x y : Fin h → Bool)
    (hc : ∀ j i, (OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat (c j i) : ℤ) =
      (OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) + A j i) :
    signatureValue W (List.ofFn x) (List.ofFn (fun j => List.ofFn (c j))) =
      signatureValue W (List.ofFn y) (List.ofFn (fun j => List.ofFn (c j))) ↔
    OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A x =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A y := by
  rw [signatureValue_exact_iff W c A x y hc]
  exact ⟨fun h => funext h, fun h => congrFun h⟩

theorem program_runs (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool)))
    (hlen : ∀ row ∈ rows, row.length = bits.length) :
    ∃ n ≤ cost W bits rows + 1, ∃ out,
      Trace program n ((state regs W bits rows []).withPC (some program.entry))
        ((state out W bits rows (signatureValue W bits rows)).withPC none) := by
  obtain ⟨n, hn, out, he⟩ := command_eval regs W bits rows [] hlen
  simp only [List.append_nil] at he
  exact ⟨n + 1, Nat.add_le_add_right hn 1, out, compiled_halt_trace he 12 14⟩

theorem state_stackBits (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) :
    stackBits (state regs W bits rows []).stacks =
      W.length + bits.length + (words (rows.map words)).length := by
  simp [stackBits, state, Fin.sum_univ_succ, Nat.add_assoc]

/-- A complete per-key execution has polynomial local time. This estimate is
applied to that invocation only, never to the exponential outer traversal. -/
theorem prefix_stack_bound {labels : ℕ} (p : Program 8 16 labels)
    (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) {steps : ℕ} {intermediate : Cfg 8 16 labels}
    (hle : steps ≤ cost W bits rows + 1)
    (htrace : Trace p steps
      ((state regs W bits rows []).withPC (some p.entry)) intermediate)
    (i : Fin 16) :
    (intermediate.stacks i).length ≤
      16 * (W.length + bits.length + (words (rows.map words)).length) +
        cost W bits rows + 1 := by
  apply StructuredSpace.local_stack_bound p (steps := cost W bits rows + 1)
    (initialBound := 16 * (W.length + bits.length + (words (rows.map words)).length))
    _ steps intermediate hle htrace i
  change stackBits (state regs W bits rows []).stacks ≤ _
  rw [state_stackBits]
  omega

namespace KeyEquality

open OAI.Algorithms.SubexponentialSAT.SubexpRecordScan

/-- The two compared words and the surrounding frame survive comparison. -/
def command : Cmd 5 6 :=
  .seq (.call (StackRoutines.copyProgram 0 1 4 (0 : Fin 5) 1))
    (.seq (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (.seq (.call compareKeys)
        (.seq (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
          (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1)))))

def program := compiled command 0 0

theorem command_eval (regs : Fin 5 → Bool) (left right frame : List Bool) :
    ∃ n ≤ 18 * left.length + 9 * right.length + 25, ∃ out,
      Eval command n (recordState regs left [] right [] [] frame)
        (recordState out left [] right [] [] frame) ∧
      out 4 = decide (left = right) := by
  let r₁ := readRegs regs 0 1 none
  let r₂ := readRegs r₁ 0 1 none
  have h₁ : Eval (.call (StackRoutines.copyProgram 0 1 4 (0 : Fin 5) 1))
      (7 * left.length + 5)
      (recordState regs left [] right [] [] frame)
      (recordState r₁ left left right [] [] frame) := by
    simpa [afterCopy, StackRoutines.copyStacks, recordState, storage, r₁] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.copy_eval (recordState regs left [] right [] [] frame)
        0 1 4 (by decide) (by decide) (by decide) rfl
  have h₂ : Eval (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (7 * right.length + 5)
      (recordState r₁ left left right [] [] frame)
      (recordState r₂ left left right right [] frame) := by
    simpa [afterCopy, StackRoutines.copyStacks, recordState, storage, r₂] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.copy_eval (recordState r₁ left left right [] [] frame)
        2 3 4 (by decide) (by decide) (by decide) rfl
  obtain ⟨nc, hnc, rc, left', right', hc, hanswer, hl, hr⟩ :=
    compareKeys_eval r₂ left left right right [] frame
  let r₃ := readRegs rc 0 1 none
  let r₄ := readRegs r₃ 0 1 none
  have h₃ : Eval (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
      (2 * left'.length + 3)
      (recordState rc left left' right right' [] frame)
      (recordState r₃ left [] right right' [] frame) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, storage, r₃] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.clear_eval (recordState rc left left' right right' [] frame) 1
  have h₄ : Eval (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1))
      (2 * right'.length + 3)
      (recordState r₃ left [] right right' [] frame)
      (recordState r₄ left [] right [] [] frame) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, storage, r₄] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.clear_eval (recordState r₃ left [] right right' [] frame) 3
  refine ⟨_, by omega, r₄, h₁.seq (h₂.seq (hc.seq (h₃.seq h₄))), ?_⟩
  simpa [r₄, r₃, readRegs] using hanswer

/-- Every prefix includes both preserved key words, the comparison copies,
all cleanup scratch and the persistent caller frame. -/
theorem prefix_stack_bound (regs : Fin 5 → Bool) (left right frame : List Bool)
    {steps : ℕ} {intermediate : Cfg 5 6 _}
    (hle : steps ≤ 18 * left.length + 9 * right.length + 26)
    (htrace : Trace program steps
      ((recordState regs left [] right [] [] frame).withPC (some program.entry)) intermediate)
    (i : Fin 6) :
    (intermediate.stacks i).length ≤
      24 * left.length + 15 * right.length + 6 * frame.length + 26 := by
  have hinit : dataBits
      ((recordState regs left [] right [] [] frame).withPC (some program.entry)) ≤
      6 * (left.length + right.length + frame.length) := by
    unfold dataBits stackBits
    calc
      _ ≤ ∑ _j : Fin 6, (left.length + right.length + frame.length) := by
        apply Finset.sum_le_sum
        intro j _
        fin_cases j <;> simp [storage] <;> omega
      _ = _ := by simp
  have hsum : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  have hgrow := trace_dataBits program htrace
  omega

end KeyEquality

namespace Rescan

abbrev Data := State 16 24
abbrev Code := Cmd 16 24

def workState (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) : Data :=
  ⟨regs, ![W, [], [], [], [], [], [], [], [], [], [], [], bits, [], key,
    words (rows.map words), candidate, saved, predecessor, fuel, [], [], [fresh], []]⟩

def signatureRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def signatureStacks : Fin 16 → Fin 24 := Fin.castAdd 8

def keyCall : Code := .call (ProgramLinking.liftProgram
  AttainedSignatureProgram.program signatureRegisters signatureStacks)

def equalityRegisters : Fin 5 → Fin 16 := Fin.castAdd 11
def equalityStacks : Fin 6 → Fin 24 := ![14, 1, 17, 3, 4, 5]

def equalityCall : Code := .call (ProgramLinking.liftProgram
  KeyEquality.program equalityRegisters equalityStacks)

theorem keyCall_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool)
    (hlen : ∀ row ∈ rows, row.length = bits.length) :
    ∃ n ≤ cost W bits rows + 1, ∃ out,
      Eval keyCall n (workState regs W rows candidate saved predecessor fuel fresh bits key)
        (workState out W rows candidate saved predecessor fuel fresh bits
          (signatureValue W bits rows ++ key)) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh bits key
  have hr : Function.Injective signatureRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective signatureStacks := Fin.castAdd_injective _ _
  have hp : projectState signatureRegisters signatureStacks a =
      AttainedSignatureProgram.state (regs ∘ signatureRegisters) W bits rows key := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    fin_cases i <;> rfl
  obtain ⟨n, hn, out, he⟩ := AttainedSignatureProgram.command_eval
    (regs ∘ signatureRegisters) W bits rows key hlen
  rw [← hp] at he
  have hc := eval_call_from_state AttainedSignatureProgram.program
    signatureRegisters signatureStacks a hr hs (compiled_halt_trace he 12 14)
  let e := embedState signatureRegisters signatureStacks a
    (AttainedSignatureProgram.state out W bits rows (signatureValue W bits rows ++ key))
  have heq : e = workState e.regs W rows candidate saved predecessor fuel fresh bits
      (signatureValue W bits rows ++ key) := by
    apply embedState_eq_of_ports signatureRegisters signatureStacks a _ _ hr hs
    · intro i
      exact embedState_register signatureRegisters signatureStacks a _ hr i
    · intro i hi
      exact embedState_register_frame signatureRegisters signatureStacks a _ i hi
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      have hil : 16 ≤ i.val := by
        by_contra h
        exact hi ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      fin_cases i <;> simp_all [workState, a]
  change Eval keyCall (n + 1) a e at hc
  rw [heq] at hc
  exact ⟨n + 1, Nat.add_le_add_right hn 1, e.regs, hc⟩

theorem equalityCall_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) :
    ∃ n ≤ 18 * key.length + 9 * saved.length + 26, ∃ out,
      Eval equalityCall n (workState regs W rows candidate saved predecessor fuel fresh bits key)
        (workState out W rows candidate saved predecessor fuel fresh bits key) ∧
      out 4 = decide (key = saved) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh bits key
  have hr : Function.Injective equalityRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective equalityStacks := by decide
  have hp : projectState equalityRegisters equalityStacks a =
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ equalityRegisters) key [] saved [] [] [] := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    fin_cases i <;> rfl
  obtain ⟨n, hn, out, he, hanswer⟩ := KeyEquality.command_eval
    (regs ∘ equalityRegisters) key saved []
  rw [← hp] at he
  have hc := eval_call_from_state KeyEquality.program equalityRegisters equalityStacks a hr hs
    (compiled_halt_trace he 0 0)
  let e := embedState equalityRegisters equalityStacks a
    (OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.recordState out key [] saved [] [] [])
  have heq : e = workState e.regs W rows candidate saved predecessor fuel fresh bits key := by
    apply embedState_eq_of_ports equalityRegisters equalityStacks a _ _ hr hs
    · intro i
      exact embedState_register equalityRegisters equalityStacks a _ hr i
    · intro i hi
      exact embedState_register_frame equalityRegisters equalityStacks a _ i hi
    · intro i
      fin_cases i <;> rfl
    · intro i _
      rfl
  have ha : e.regs 4 = decide (key = saved) := by
    change e.regs (equalityRegisters 4) = _
    rw [embedState_register equalityRegisters equalityStacks a _ hr]
    exact hanswer
  change Eval equalityCall (n + 1) a e at hc
  rw [heq] at hc
  exact ⟨n + 1, by omega, e.regs, hc, ha⟩

def countdownPorts : CounterForPrograms.Ports 16 24 where
  register := ⟨![13, 14, 15], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  counter := 19
  scratch := 20
  counter_ne_scratch := by decide

def predecessorPorts : CounterForPrograms.Ports 16 24 where
  register := countdownPorts.register
  counter := 18
  scratch := 20
  counter_ne_scratch := by decide

def clear (i : Fin 24) : Code := .call (StackRoutines.clearProgram i 0 1)
def copy (i j : Fin 24) : Code := .call (StackRoutines.copyProgram i j 21 0 1)

theorem clear_eval (i : Fin 24) (a : Data) :
    Eval (clear i) (2 * (a.stacks i).length + 3) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks i a.stacks⟩ :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem copy_eval (i j : Fin 24) (a : Data)
    (hij : i ≠ j) (hi : i ≠ 21) (hj : (21 : Fin 24) ≠ j)
    (ht : a.stacks 21 = []) :
    Eval (copy i j) (7 * (a.stacks i).length + 5) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks i j a.stacks⟩ :=
  .call _ (ListRegisterProgram.copy_run i j 21 0 1 hij hi hj (by decide)
    a.regs a.stacks ht)

def storeFresh (b : Bool) : Code := .seq (clear 22)
  (.base (.seq (.atom (.set 0 b)) (.atom (.push 22 0))))

/-- Reject only a duplicate full key; keep scanning to charge and complete all
predecessor work independently of success. -/
def updateFresh : Code := .ite 4 (storeFresh false) (.base .skip)

theorem storeFresh_eval (b : Bool) (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) :
    ∃ out, Eval (storeFresh b) 7
      (workState regs W rows candidate saved predecessor fuel fresh bits key)
      (workState out W rows candidate saved predecessor fuel b bits key) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh bits key
  let c : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 22 a.stacks⟩
  let d := (StructuredProgram.Atom.set (0 : Fin 16) b).eval c
  let e := (StructuredProgram.Atom.push (22 : Fin 24) (0 : Fin 16)).eval d
  have hc : Eval (clear 22) 5 a c := clear_eval 22 a
  have he : Eval (.base (.seq (.atom (.set 0 b)) (.atom (.push 22 0)))) 2 c e :=
    .base ((StructuredProgram.Eval.atom _ c).seq (StructuredProgram.Eval.atom _ d))
  have hf : e = workState e.regs W rows candidate saved predecessor fuel b bits key := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i <;> simp [d, c, a, workState, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  refine ⟨e.regs, ?_⟩
  have ht := hc.seq he
  rw [hf] at ht
  exact ht

theorem updateFresh_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) :
    ∃ n ≤ 8, ∃ out, Eval updateFresh n
      (workState regs W rows candidate saved predecessor fuel fresh bits key)
      (workState out W rows candidate saved predecessor fuel (fresh && !(regs 4)) bits key) := by
  cases hf : regs 4 with
  | false =>
    exact ⟨1, by omega, regs, by
      simpa [updateFresh, hf] using (Eval.ite_false hf (.base (.skip _)) :
        Eval updateFresh 1
          (workState regs W rows candidate saved predecessor fuel fresh bits key)
          (workState regs W rows candidate saved predecessor fuel fresh bits key))⟩
  | true =>
    obtain ⟨out, he⟩ := storeFresh_eval false regs W rows candidate saved predecessor fuel fresh bits key
    exact ⟨8, le_rfl, out, by simpa [updateFresh, hf] using (Eval.ite_true hf he :
      Eval updateFresh 8
        (workState regs W rows candidate saved predecessor fuel fresh bits key)
        (workState out W rows candidate saved predecessor fuel false bits key))⟩

/-- One predecessor is processed by actual full-signature and byte-equality
programs; the assignment counter is incremented only after all scratch is free. -/
def body : Code :=
  .seq (copy 18 12) (.seq keyCall (.seq equalityCall
    (.seq updateFresh (.seq (clear 12) (.seq (clear 14)
      (Counters.incrementCmd predecessorPorts))))))

def bodyCost (W predecessor saved : List Bool) (rows : List (List (List Bool))) : ℕ :=
  7 * predecessor.length + 5 + (cost W predecessor rows + 1) +
    (18 * (signatureValue W predecessor rows).length + 9 * saved.length + 26) + 8 +
    (2 * predecessor.length + 3) + (2 * (signatureValue W predecessor rows).length + 3) +
    (CounterPrograms.rippleCost true predecessor + 1)

theorem body_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (hlen : ∀ row ∈ rows, row.length = predecessor.length) :
    ∃ n ≤ bodyCost W predecessor saved rows, ∃ out,
      Eval body n (workState regs W rows candidate saved predecessor fuel fresh [] [])
        (workState out W rows candidate saved (CounterPrograms.ripple true predecessor) fuel
          (fresh && !decide (signatureValue W predecessor rows = saved)) [] []) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh [] []
  let r₁ := readRegs regs 0 1 none
  have hcopy : Eval (copy 18 12) (7 * predecessor.length + 5) a
      (workState r₁ W rows candidate saved predecessor fuel fresh predecessor []) := by
    have ht := copy_eval 18 12 a (by decide) (by decide) (by decide) rfl
    have he : (⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 18 12 a.stacks⟩ : Data) =
        workState r₁ W rows candidate saved predecessor fuel fresh predecessor [] := by
      apply congrArg (StructuredProgram.State.mk r₁)
      funext i
      fin_cases i <;> simp [a, workState, StackRoutines.copyStacks]
    rw [he] at ht
    exact ht
  obtain ⟨nk, hnk, rk, hk⟩ := keyCall_eval r₁ W rows candidate saved predecessor fuel
    fresh predecessor [] hlen
  simp only [List.append_nil] at hk
  obtain ⟨ne, hne, re, he, hanswer⟩ := equalityCall_eval rk W rows candidate saved predecessor fuel
    fresh predecessor (signatureValue W predecessor rows)
  obtain ⟨nf, hnf, rf, hf⟩ := updateFresh_eval re W rows candidate saved predecessor fuel
    fresh predecessor (signatureValue W predecessor rows)
  rw [hanswer] at hf
  let fresh' := fresh && !decide (signatureValue W predecessor rows = saved)
  let r₂ := readRegs rf 0 1 none
  have hclearBits : Eval (clear 12) (2 * predecessor.length + 3)
      (workState rf W rows candidate saved predecessor fuel fresh' predecessor
        (signatureValue W predecessor rows))
      (workState r₂ W rows candidate saved predecessor fuel fresh' []
        (signatureValue W predecessor rows)) := by
    have ht := clear_eval 12 (workState rf W rows candidate saved predecessor fuel fresh'
      predecessor (signatureValue W predecessor rows))
    have hs : StackRoutines.clearStacks 12
        (workState rf W rows candidate saved predecessor fuel fresh' predecessor
          (signatureValue W predecessor rows)).stacks =
        (workState r₂ W rows candidate saved predecessor fuel fresh' []
          (signatureValue W predecessor rows)).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [hs] at ht
    exact ht
  let r₃ := readRegs r₂ 0 1 none
  have hclearKey : Eval (clear 14) (2 * (signatureValue W predecessor rows).length + 3)
      (workState r₂ W rows candidate saved predecessor fuel fresh' []
        (signatureValue W predecessor rows))
      (workState r₃ W rows candidate saved predecessor fuel fresh' [] []) := by
    have ht := clear_eval 14 (workState r₂ W rows candidate saved predecessor fuel fresh' []
      (signatureValue W predecessor rows))
    have hs : StackRoutines.clearStacks 14
        (workState r₂ W rows candidate saved predecessor fuel fresh' []
          (signatureValue W predecessor rows)).stacks =
        (workState r₃ W rows candidate saved predecessor fuel fresh' [] []).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [hs] at ht
    exact ht
  let b := workState r₃ W rows candidate saved predecessor fuel fresh' [] []
  let e := Counters.incrementResult predecessorPorts b
  have hincr := Counters.increment_eval predecessorPorts b (by rfl)
  have heq : e = workState e.regs W rows candidate saved
      (CounterPrograms.ripple true predecessor) fuel fresh' [] [] := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    exact (Counters.incrementResult_stacks predecessorPorts b (by rfl)).trans (by
      funext i
      fin_cases i <;> simp [b, workState, predecessorPorts])
  change Eval (Counters.incrementCmd predecessorPorts)
    (CounterPrograms.rippleCost true predecessor + 1) b e at hincr
  rw [heq] at hincr
  refine ⟨_, ?_, e.regs, hcopy.seq (hk.seq (he.seq (hf.seq
    (hclearBits.seq (hclearKey.seq hincr)))))⟩
  dsimp [bodyCost]
  omega

def keyBound (W : List Bool) (h d B : ℕ) : ℕ :=
  d * (2 * (widthBound W h B + 1) + 1)

def bodyBound (W saved : List Bool) (rows : List (List (List Bool))) (h B : ℕ) : ℕ :=
  17 * h + 20 * keyBound W h rows.length B + 9 * saved.length +
    7 * (words (rows.map words)).length + rows.length * (signatureRowBound W h B + 2) + 62

theorem bodyCost_le (W predecessor saved : List Bool) (rows : List (List (List Bool)))
    (h B : ℕ) (hp : predecessor.length = h)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) :
    bodyCost W predecessor saved rows ≤ bodyBound W saved rows h B := by
  have hr : ∀ row ∈ rows, row.length = predecessor.length := by simpa [hp] using hlen
  have hc := cost_le W predecessor rows B hr hwidth
  have hk := signatureValue_length_bound W predecessor rows B hr hwidth
  have hi := CounterPrograms.rippleCost_le true predecessor
  rw [hp] at hc hk hi
  unfold bodyCost bodyBound keyBound
  rw [hp]
  omega

def naturalKey (W : List Bool) (rows : List (List (List Bool))) (h i : ℕ) : List Bool :=
  signatureValue W (ExecCNFTupleEnumeration.fixedBits h i) rows

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
