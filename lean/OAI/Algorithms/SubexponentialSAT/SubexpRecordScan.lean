import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFRecords
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Fixed-control selection of serialized coefficient records

The inner record body is `frame key ++ frame coefficient`. All execution
claims below are traces of fixed Boolean-register/stack instruction tables.
-/

namespace SubexponentialSAT.SubexpRecordScan

open BitProgram StructuredProgram StructuredCalls

abbrev Data := StructuredProgram.State 5 6

private theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

private theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    StructuredCalls.embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [StructuredCalls.embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [StructuredCalls.embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [StructuredCalls.embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [StructuredCalls.embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

def lowRegs : Fin 2 → Fin 5 := Fin.castAdd 3

theorem lowRegs_injective : Function.Injective lowRegs := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 5 => x.val) h

def twoPorts (src dst : Fin 6) : Fin 2 → Fin 6 := ParserProgram.pair src dst

theorem twoPorts_injective (src dst : Fin 6) (h : src ≠ dst) :
    Function.Injective (twoPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [twoPorts, ParserProgram.pair]

/-- The existing frame parser relocated to two named ports. -/
abbrev parseFrame (src dst : Fin 6) : Program 5 6 7 :=
  ProgramLinking.liftProgram ParserProgram.frameProgram lowRegs (twoPorts src dst)

def afterFrame (d : Data) (src dst : Fin 6) (bits rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst
      (bits.reverse ++ d.stacks dst)⟩

/-- Actual parser execution on arbitrary surrounding register/stack data. -/
theorem parseFrame_eval (d : Data) (src dst : Fin 6) (hsd : src ≠ dst)
    (bits rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    StructuredCalls.Eval (.call (parseFrame src dst)) (6 * bits.length + 4)
      d (afterFrame d src dst bits rest) := by
  let a : StructuredProgram.State 2 2 :=
    ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
      ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : StructuredProgram.State 2 2 :=
    ⟨ParserProgram.pair false true,
      ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : StructuredCalls.embedState lowRegs (twoPorts src dst) d a = d := by
    apply embedState_eq _ _ lowRegs_injective (twoPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
    · intros; rfl
  have hb : StructuredCalls.embedState lowRegs (twoPorts src dst) d b =
      afterFrame d src dst bits rest := by
    apply embedState_eq _ _ lowRegs_injective (twoPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterFrame, lowRegs, readRegs, b, ParserProgram.pair]
    · intro i; fin_cases i <;>
        simp [afterFrame, twoPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [lowRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [lowRegs] using h.symm⟩
      simp [afterFrame, readRegs, h0, h1]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [twoPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [twoPorts] using h.symm⟩
      simp [afterFrame, hsrc, hdst]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := StructuredCalls.eval_call_lifted ParserProgram.frameProgram lowRegs
    (twoPorts src dst) d lowRegs_injective (twoPorts_injective src dst hsd) ht
  simpa only [ha, hb, parseFrame] using h

/-- The register/stack state after clearing a scratch port. -/
def afterClear (d : Data) (src : Fin 6) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

theorem clear_eval (d : Data) (src : Fin 6) :
    StructuredCalls.Eval (.call (StackRoutines.clearProgram src (0 : Fin 5) 1))
      (2 * (d.stacks src).length + 3) d (afterClear d src) := by
  apply StructuredCalls.Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [afterClear, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh

def afterCopy (d : Data) (src dst : Fin 6) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (d : Data) (src dst tmp : Fin 6)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (htmp : d.stacks tmp = []) :
    StructuredCalls.Eval (.call (StackRoutines.copyProgram src dst tmp (0 : Fin 5) 1))
      (7 * (d.stacks src).length + 5) d (afterCopy d src dst) := by
  apply StructuredCalls.Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 5) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [afterCopy, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

def skipRegs : Fin 3 → Fin 5 := ExecCNFRecords.ports 0 1 4
def onlyInput : Fin 1 → Fin 6 := fun _ => 0
def payloadPorts : Fin 3 → Fin 6 := ExecCNFRecords.ports 0 5 4

theorem skipRegs_injective : Function.Injective skipRegs := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [skipRegs, ExecCNFRecords.ports]

theorem onlyInput_injective : Function.Injective onlyInput := by
  intro a b _
  exact Subsingleton.elim _ _

theorem payloadPorts_injective : Function.Injective payloadPorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [payloadPorts, ExecCNFRecords.ports]

/-- Enter the existing raw-frame routines, rather than their tagged-list entry. -/
abbrev rawSkip : Program 3 1 11 := {ExecCNFRecords.skipProgram with entry := 4}
abbrev rawCopy : Program 2 3 16 := {ExecCNFRecords.copyProgram with entry := 4}

abbrev skipPayload : Program 5 6 11 :=
  ProgramLinking.liftProgram rawSkip skipRegs onlyInput

abbrev copyPayload : Program 5 6 16 :=
  ProgramLinking.liftProgram rawCopy lowRegs payloadPorts

def afterSkip (d : Data) (rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false), Function.update d.stacks 0 rest⟩

def afterPayload (d : Data) (bits rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 0 rest) 5
      (Encoding.frame bits ++ d.stacks 5)⟩

theorem skipPayload_eval (d : Data) (bits rest : List Bool)
    (hin : d.stacks 0 = Encoding.frame bits ++ rest) :
    StructuredCalls.Eval (.call skipPayload) (5 * bits.length + 4)
      d (afterSkip d rest) := by
  let a : StructuredProgram.State 3 1 :=
    ⟨ExecCNFRecords.regs (d.regs 0) (d.regs 1) (d.regs 4),
      fun _ => Encoding.frame bits ++ rest⟩
  let b : StructuredProgram.State 3 1 :=
    ⟨ExecCNFRecords.regs false true (d.regs 4), fun _ => rest⟩
  have ha : StructuredCalls.embedState skipRegs onlyInput d a = d := by
    apply embedState_eq _ _ skipRegs_injective onlyInput_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i; exact hin
    · intros; rfl
    · intros; rfl
  have hb : StructuredCalls.embedState skipRegs onlyInput d b = afterSkip d rest := by
    apply embedState_eq _ _ skipRegs_injective onlyInput_injective
    · intro i; fin_cases i <;>
        simp [afterSkip, skipRegs, ExecCNFRecords.ports, ExecCNFRecords.regs, readRegs, b]
    · intro i; fin_cases i; simp [afterSkip, onlyInput, b]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [skipRegs, ExecCNFRecords.ports] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [skipRegs, ExecCNFRecords.ports] using h.symm⟩
      simp [afterSkip, readRegs, h0, h1]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [onlyInput] using h.symm⟩
      simp [afterSkip, h0]
  have ht : Trace rawSkip (5 * bits.length + 4)
      (a.withPC (some rawSkip.entry)) (b.withPC none) :=
    ExecCNFRecords.frame_trace bits rest (d.regs 0) (d.regs 1) (d.regs 4)
  have h := StructuredCalls.eval_call_lifted rawSkip skipRegs onlyInput d
    skipRegs_injective onlyInput_injective ht
  simpa only [ha, hb, skipPayload] using h

theorem copyPayload_eval (d : Data) (bits rest : List Bool)
    (hin : d.stacks 0 = Encoding.frame bits ++ rest) (htmp : d.stacks 4 = []) :
    StructuredCalls.Eval (.call copyPayload) (13 * bits.length + 11)
      d (afterPayload d bits rest) := by
  let a : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
      ExecCNFRecords.ports (Encoding.frame bits ++ rest) (d.stacks 5) []⟩
  let b : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair false false,
      ExecCNFRecords.ports rest (Encoding.frame bits ++ d.stacks 5) []⟩
  have ha : StructuredCalls.embedState lowRegs payloadPorts d a = d := by
    apply embedState_eq _ _ lowRegs_injective payloadPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
      · exact htmp
    · intros; rfl
    · intros; rfl
  have hb : StructuredCalls.embedState lowRegs payloadPorts d b =
      afterPayload d bits rest := by
    apply embedState_eq _ _ lowRegs_injective payloadPorts_injective
    · intro i; fin_cases i <;> simp [afterPayload, lowRegs, readRegs, b, ParserProgram.pair]
    · intro i; fin_cases i <;>
        simp [afterPayload, payloadPorts, ExecCNFRecords.ports, b, htmp]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [lowRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [lowRegs] using h.symm⟩
      simp [afterPayload, readRegs, h0, h1]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [payloadPorts, ExecCNFRecords.ports] using h.symm⟩
      have h5 : j ≠ 5 := fun h => hj ⟨1, by simpa [payloadPorts, ExecCNFRecords.ports] using h.symm⟩
      simp [afterPayload, h0, h5]
  have ht : Trace rawCopy (13 * bits.length + 11)
      (a.withPC (some rawCopy.entry)) (b.withPC none) :=
    ExecCNFRecords.copy_frame_trace bits rest (d.stacks 5) (d.regs 0) (d.regs 1)
  have h := StructuredCalls.eval_call_lifted rawCopy lowRegs payloadPorts d
    lowRegs_injective payloadPorts_injective ht
  simpa only [ha, hb, copyPayload] using h

/-- Conditional payload selection keeps the entire frame and its boundary. -/
abbrev selectPayload : StructuredCalls.Cmd 5 6 :=
  .ite 4 (.call copyPayload) (.call skipPayload)

def selectedState (d : Data) (bits rest : List Bool) : Data :=
  if d.regs 4 then afterPayload d bits rest else afterSkip d rest

theorem selectPayload_eval (d : Data) (bits rest : List Bool)
    (hin : d.stacks 0 = Encoding.frame bits ++ rest) (htmp : d.stacks 4 = []) :
    ∃ n ≤ 13 * bits.length + 12,
      StructuredCalls.Eval selectPayload n d (selectedState d bits rest) := by
  cases h : d.regs 4 with
  | false =>
    refine ⟨5 * bits.length + 4 + 1, by omega, ?_⟩
    simpa only [selectPayload, selectedState, h, Bool.false_eq_true, ite_false] using
      StructuredCalls.Eval.ite_false h (skipPayload_eval d bits rest hin)
  | true =>
    refine ⟨13 * bits.length + 11 + 1, by omega, ?_⟩
    simpa only [selectPayload, selectedState, h, ite_true] using
      StructuredCalls.Eval.ite_true h (copyPayload_eval d bits rest hin htmp)

abbrev storage (input key query work tmp output : List Bool) : Fin 6 → List Bool :=
  fun j => if j = 0 then input else if j = 1 then key else if j = 2 then query
    else if j = 3 then work else if j = 4 then tmp else output

abbrev recordState (regs : Fin 5 → Bool) (input key query work tmp output : List Bool) : Data :=
  ⟨regs, storage input key query work tmp output⟩

@[simp] theorem storage_zero (a b c d e f : List Bool) : storage a b c d e f 0 = a := rfl
@[simp] theorem storage_one (a b c d e f : List Bool) : storage a b c d e f 1 = b := rfl
@[simp] theorem storage_two (a b c d e f : List Bool) : storage a b c d e f 2 = c := rfl
@[simp] theorem storage_three (a b c d e f : List Bool) : storage a b c d e f 3 = d := rfl
@[simp] theorem storage_four (a b c d e f : List Bool) : storage a b c d e f 4 = e := rfl
@[simp] theorem storage_five (a b c d e f : List Bool) : storage a b c d e f 5 = f := rfl

@[simp] theorem storage_update_zero (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 0 x = storage x b c d e f := by
  funext j; fin_cases j <;> simp [storage]

@[simp] theorem storage_update_one (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 1 x = storage a x c d e f := by
  funext j; fin_cases j <;> simp [storage]

@[simp] theorem storage_update_three (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 3 x = storage a b c x e f := by
  funext j; fin_cases j <;> simp [storage]

@[simp] theorem storage_update_five (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 5 x = storage a b c d e x := by
  funext j; fin_cases j <;> simp [storage]

abbrev compareKeys : Program 5 6 10 :=
  ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram id (twoPorts 1 3)

/-- Actual bit-string comparison, with preserved surrounding ports and
bounded leftover lengths for the following cleanup loops. -/
theorem compareKeys_eval (regs : Fin 5 → Bool)
    (input left query right tmp output : List Bool) :
    ∃ n ≤ 9 * (left.length + 1), ∃ regs' left' right',
      StructuredCalls.Eval (.call compareKeys) n
        (recordState regs input left query right tmp output)
        (recordState regs' input left' query right' tmp output) ∧
      regs' 4 = decide (left = right) ∧
      left'.length ≤ left.length ∧ right'.length ≤ right.length := by
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout, hleft, hright⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded regs left right
  let frame := recordState regs input left query right tmp output
  let a : StructuredProgram.State 5 2 := ⟨regs, ExecClauseCost.bitStacks left right⟩
  let b : StructuredProgram.State 5 2 := ⟨c.regs, c.stacks⟩
  have ha : StructuredCalls.embedState id (twoPorts 1 3) frame a = frame := by
    apply embedState_eq _ _ Function.injective_id (twoPorts_injective 1 3 (by decide))
    · intro j; rfl
    · intro j; fin_cases j <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : StructuredCalls.embedState id (twoPorts 1 3) frame b =
      recordState c.regs input (c.stacks 0) query (c.stacks 1) tmp output := by
    apply embedState_eq _ _ Function.injective_id (twoPorts_injective 1 3 (by decide))
    · intro j; rfl
    · intro j; fin_cases j <;> rfl
    · intro j hj
      exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨0, by simpa [twoPorts] using h.symm⟩
      have h3 : j ≠ 3 := fun h => hj ⟨1, by simpa [twoPorts] using h.symm⟩
      simp [ storage, frame, h1, h3]
  have hcfg : b.withPC none = c := by
    cases c
    simp_all [b, StructuredProgram.State.withPC]
  have ht' : Trace ExecClauseCost.bitEqualityProgram n
      (a.withPC (some ExecClauseCost.bitEqualityProgram.entry)) (b.withPC none) := by
    rw [hcfg]
    exact ht
  have h := StructuredCalls.eval_call_lifted ExecClauseCost.bitEqualityProgram id
    (twoPorts 1 3) frame Function.injective_id (twoPorts_injective 1 3 (by decide)) ht'
  refine ⟨n, hn, c.regs, c.stacks 0, c.stacks 1, ?_, hout, hleft, hright⟩
  simpa only [ha, hb, compareKeys] using h

/-- The entire inner-record selector is one fixed structured program.
Every call here is a fixed finite instruction table. -/
abbrev oneRecord : StructuredCalls.Cmd 5 6 :=
  .seq (.call (parseFrame 0 1))
    (.seq (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (.seq (.call compareKeys)
        (.seq (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
          (.seq (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1)) selectPayload))))

/-- The actual compiled Boolean-stack machine; its control size is independent
of the encoded key and coefficient lengths. -/
def oneRecordProgram := StructuredCalls.compiled oneRecord 0 5

theorem oneRecord_control_size : StructuredCalls.size oneRecord = 59 := by decide

/-- The exact structured execution bound for one serialized inner record. -/
def recordCost (key query payload : List Bool) : ℕ :=
  17 * key.length + 9 * query.length + 13 * payload.length + 36

/-- One record is consumed; the query is restored; all three scratch ports
are empty; and the complete coefficient frame is selected exactly on key
equality. The Boolean result remains in register 4. -/
theorem oneRecord_eval (regs : Fin 5 → Bool)
    (key query payload tail output : List Bool) :
    ∃ n ≤ recordCost key query payload, ∃ regs',
      StructuredCalls.Eval oneRecord n
        (recordState regs (Encoding.frame key ++ (Encoding.frame payload ++ tail))
          [] query.reverse [] [] output)
        (recordState regs' tail [] query.reverse [] []
          (if key = query then Encoding.frame payload ++ output else output)) ∧
      regs' 4 = decide (key = query) := by
  let source := Encoding.frame payload ++ tail
  let r₁ := readRegs regs 0 1 (some false)
  let r₂ := readRegs r₁ 0 1 none
  have hp : StructuredCalls.Eval (.call (parseFrame 0 1)) (6 * key.length + 4)
      (recordState regs (Encoding.frame key ++ source) [] query.reverse [] [] output)
      (recordState r₁ source key.reverse query.reverse [] [] output) := by
    have h := parseFrame_eval
      (recordState regs (Encoding.frame key ++ source) [] query.reverse [] [] output)
      0 1 (by decide) key source rfl
    simpa [afterFrame, recordState, r₁] using h
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1)) (7 * query.length + 5)
      (recordState r₁ source key.reverse query.reverse [] [] output)
      (recordState r₂ source key.reverse query.reverse query.reverse [] output) := by
    have h := copy_eval
      (recordState r₁ source key.reverse query.reverse [] [] output)
      2 3 4 (by decide) (by decide) (by decide) rfl
    simpa [afterCopy, StackRoutines.copyStacks, recordState, r₂] using h
  obtain ⟨nc, hnc, rr, left, right, hcompare, hanswer, hleft, hright⟩ :=
    compareKeys_eval r₂ source key.reverse query.reverse query.reverse [] output
  simp only [List.length_reverse] at hnc hleft hright
  have hans : rr 4 = decide (key = query) := by
    simpa only [List.reverse_inj] using hanswer
  let r₃ := readRegs rr 0 1 none
  let r₄ := readRegs r₃ 0 1 none
  have hclear₁ : StructuredCalls.Eval
      (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1)) (2 * left.length + 3)
      (recordState rr source left query.reverse right [] output)
      (recordState r₃ source [] query.reverse right [] output) := by
    have h := clear_eval (recordState rr source left query.reverse right [] output) 1
    simpa [afterClear, StackRoutines.clearStacks, recordState, r₃] using h
  have hclear₃ : StructuredCalls.Eval
      (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1)) (2 * right.length + 3)
      (recordState r₃ source [] query.reverse right [] output)
      (recordState r₄ source [] query.reverse [] [] output) := by
    have h := clear_eval (recordState r₃ source [] query.reverse right [] output) 3
    simpa [afterClear, StackRoutines.clearStacks, recordState, r₄] using h
  let ready := recordState r₄ source [] query.reverse [] [] output
  have hflag : ready.regs 4 = decide (key = query) := by
    simpa [ready, recordState, r₄, r₃, readRegs] using hans
  obtain ⟨ns, hns, hselect⟩ := selectPayload_eval ready payload tail rfl rfl
  have hend : selectedState ready payload tail =
      recordState (selectedState ready payload tail).regs tail [] query.reverse [] []
        (if key = query then Encoding.frame payload ++ output else output) := by
    apply state_ext
    · rfl
    · by_cases heq : key = query
      · have htrue : ready.regs 4 = true := by simpa [heq] using hflag
        simp only [selectedState, htrue, ite_true]
        simp [afterPayload, ready, heq]
      · have hfalse : ready.regs 4 = false := by simpa [heq] using hflag
        simp only [selectedState, hfalse, Bool.false_eq_true, ite_false]
        simp [afterSkip, ready, heq]
  have hfinal : (selectedState ready payload tail).regs 4 = decide (key = query) := by
    unfold selectedState
    split <;> simpa [afterPayload, afterSkip, readRegs] using hflag
  rw [hend] at hselect
  refine ⟨(6 * key.length + 4) + ((7 * query.length + 5) +
    (nc + ((2 * left.length + 3) + ((2 * right.length + 3) + ns)))), ?_,
    (selectedState ready payload tail).regs, ?_, hfinal⟩
  · unfold recordCost
    omega
  · exact StructuredCalls.Eval.seq hp
      (StructuredCalls.Eval.seq hcopy
        (StructuredCalls.Eval.seq hcompare
          (StructuredCalls.Eval.seq hclear₁ (StructuredCalls.Eval.seq hclear₃ hselect))))

/-- Actual fixed-table traces, including the final halt instruction. -/
theorem oneRecord_trace (regs : Fin 5 → Bool)
    (key query payload tail output : List Bool) :
    ∃ n ≤ recordCost key query payload + 1, ∃ regs',
      Trace oneRecordProgram n
        ((recordState regs (Encoding.frame key ++ (Encoding.frame payload ++ tail))
          [] query.reverse [] [] output).withPC (some oneRecordProgram.entry))
        ((recordState regs' tail [] query.reverse [] []
          (if key = query then Encoding.frame payload ++ output else output)).withPC none) ∧
      regs' 4 = decide (key = query) := by
  obtain ⟨n, hn, regs', heval, hans⟩ := oneRecord_eval regs key query payload tail output
  exact ⟨n + 1, Nat.add_le_add_right hn 1, regs',
    StructuredCalls.compiled_halt_trace heval 0 5, hans⟩

/-- The measured bound is linear in actual encoded input lengths. -/
theorem recordCost_le_encoded_length (key query payload : List Bool) :
    recordCost key query payload + 1 ≤
      9 * (SubexpSymbolicCost.framedRecord key payload).length +
        9 * query.length + 19 := by
  rw [SubexpSymbolicCost.framedRecord_length]
  unfold recordCost
  omega

/-- Matching the concrete exponent-key encoding is exactly matching exponent
indices, by the independently proved encoding injectivity. -/
theorem oneRecord_fixedKey_trace {D : ℕ} (regs : Fin 5 → Bool)
    (key query : SymbolicCost.RawIndex D) (payload tail output : List Bool) :
    ∃ n ≤ recordCost (SubexpSymbolicCost.fixedKey key)
        (SubexpSymbolicCost.fixedKey query) payload + 1, ∃ regs',
      Trace oneRecordProgram n
        ((recordState regs
          (Encoding.frame (SubexpSymbolicCost.fixedKey key) ++ (Encoding.frame payload ++ tail))
          [] (SubexpSymbolicCost.fixedKey query).reverse [] [] output).withPC
            (some oneRecordProgram.entry))
        ((recordState regs' tail [] (SubexpSymbolicCost.fixedKey query).reverse [] []
          (if key = query then Encoding.frame payload ++ output else output)).withPC none) ∧
      regs' 4 = decide (key = query) := by
  simpa only [SubexpSymbolicCost.fixedKey_injective.eq_iff] using
    oneRecord_trace regs (SubexpSymbolicCost.fixedKey key)
      (SubexpSymbolicCost.fixedKey query) payload tail output

/-- The fixed-table trace also lowers to the actual primitive bit-machine
model, with the compiler's proved constant overhead. This is a component
configuration boundary, not a claim about a complete raw-input SAT solver. -/
theorem oneRecord_primitive_runs (regs : Fin 5 → Bool)
    (key query payload tail output : List Bool) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive oneRecordProgram).step
      (BitProgram.primitiveOverhead oneRecordProgram * (recordCost key query payload + 1))
      (BitProgram.primitiveCfg oneRecordProgram
        ((recordState regs (Encoding.frame key ++ (Encoding.frame payload ++ tail))
          [] query.reverse [] [] output).withPC (some oneRecordProgram.entry)))
      (BitProgram.primitiveCfg oneRecordProgram
        ((recordState regs' tail [] query.reverse [] []
          (if key = query then Encoding.frame payload ++ output else output)).withPC none)) ∧
      regs' 4 = decide (key = query) := by
  obtain ⟨n, hn, regs', ht, hans⟩ := oneRecord_trace regs key query payload tail output
  exact ⟨regs', BitProgram.primitive_execution oneRecordProgram ⟨n, hn, ht⟩, hans⟩

end SubexponentialSAT.SubexpRecordScan

end OAI.Algorithms
