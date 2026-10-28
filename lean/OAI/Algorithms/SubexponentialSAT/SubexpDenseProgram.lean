import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Finite control for dense coefficient projection

The controller below is an actual finite instruction table. Its local callback
contract is deliberately an actual `StructuredCalls.Eval` of a fixed program:
it must be discharged by the concrete lookup and record-emission programs.
It is not an assumption that an abstract ring operation takes one machine step.
The concrete callback integration and product-pair builder are separate stages.
-/

namespace SubexponentialSAT.SubexpDenseProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def prependRecord (record acc : List Bool) : List Bool :=
  true :: (Encoding.frame record ++ acc)

theorem fold_prependRecord (f : List Bool → List Bool)
    (records tail : List (List Bool)) :
    records.foldl (fun acc item => prependRecord (f item) acc)
      (Encoding.encodeList id tail) =
      Encoding.encodeList id (records.reverse.map f ++ tail) := by
  induction records generalizing tail with
  | nil => rfl
  | cons record records ih =>
    change records.foldl (fun acc item => prependRecord (f item) acc)
      (Encoding.encodeList id (f record :: tail)) = _
    rw [ih]
    simp [List.reverse_cons, List.map_append, List.append_assoc]

def PrependEffect {r s : ℕ} (output : Fin s) (f : List Bool → List Bool)
    (item : List Bool) (before after : State r s) : Prop :=
  after.stacks output = prependRecord (f item) (before.stacks output)

/-- The program is independent of the number of retained slots. Its callback
is a fixed finite subprogram, not a run-time supplied operation oracle. -/
abbrev projectionController {r s : ℕ} (ports : RecordPrograms.Ports r s)
    (slotCallback : Cmd r s) := RecordPrograms.program ports slotCallback

theorem unread_false (slots : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) slots suffix = suffix := by
  induction slots with
  | nil => rfl
  | cons item slots ih => simp [RecordPrograms.unread]

theorem any_false (slots : List (List Bool)) : slots.any (fun _ => false) = false := by
  induction slots with
  | nil => rfl
  | cons item slots ih => simp

/-- This theorem contributes the entire measured outer slot loop, including
frame parsing, list markers, guards, and termination. The only local premise
is the actual trace of the fixed lookup/emission callback on one slot. -/
theorem projectionController_run {r s : ℕ} (ports : RecordPrograms.Ports r s)
    (slotCallback : Cmd r s) (output : Fin s)
    (_houtSource : output ≠ ports.source) (_houtPayload : output ≠ ports.payload)
    (f : List Bool → List Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop)
    (callback : RecordPrograms.CallbackContractWith ports slotCallback (fun _ => false)
      cost invariant (PrependEffect output f))
    (slots suffix : List (List Bool)) (inputSuffix : List Bool) (base : State r s)
    (valid : invariant base) (houtput : base.stacks output = Encoding.encodeList id suffix)
    (v pr found : Bool) :
    ∃ next : State r s, invariant next ∧
      next.stacks output = Encoding.encodeList id (slots.reverse.map f ++ suffix) ∧
      RunsIn (projectionController ports slotCallback) (4 + RecordPrograms.budget cost slots)
        ((RecordPrograms.state ports base v pr found
          (Encoding.encodeList id slots ++ inputSuffix) []).withPC
          (some (projectionController ports slotCallback).entry))
        ((RecordPrograms.state ports next false true false inputSuffix []).withPC none) := by
  obtain ⟨n, next, hn, hnext, hvisit, hrun⟩ :=
    RecordPrograms.iterate_run_with ports slotCallback (fun _ => false) cost invariant
      (PrependEffect output f) callback slots inputSuffix base valid v pr found
  have hfold := hvisit.fold_of_false (fun _ _ => rfl) (fun st => st.stacks output)
    (fun acc item => prependRecord (f item) acc) (fun _ _ _ h => h)
  rw [houtput, fold_prependRecord] at hfold
  refine ⟨next, hnext, hfold, n + 1, by omega, ?_⟩
  simpa [projectionController, RecordPrograms.program, unread_false, any_false] using
    StructuredCalls.compiled_halt_trace hrun ports.source ports.source

theorem sum_lengths_le (slots : List (List Bool)) (I : ℕ)
    (hI : ∀ item ∈ slots, item.length ≤ I) :
    (slots.map List.length).sum ≤ slots.length * I := by
  induction slots with
  | nil => simp
  | cons item slots ih =>
    have hh := hI item (by simp)
    have ht := ih (fun x hx => hI x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A fixed per-slot lookup bound is charged once per actual parsed slot. -/
theorem projectionController_cost (slots : List (List Bool))
    (cost : List Bool → ℕ) (I U : ℕ)
    (hI : ∀ item ∈ slots, item.length ≤ I) (hU : ∀ item ∈ slots, cost item ≤ U) :
    4 + RecordPrograms.budget cost slots ≤ 4 + slots.length * (6 * I + U + 7) := by
  have hb := RecordPrograms.budget_le_linear cost slots 0 U (by simpa using hU)
  have hs := Nat.mul_le_mul_left 6 (sum_lengths_le slots I hI)
  simp only [Nat.zero_add] at hb
  calc
    _ ≤ 4 + (6 * (slots.length * I) + (U + 7) * slots.length) := by omega
    _ = _ := by ring

section ProjectionSemantics

open SubexponentialSAT.SubexpSymbolicCost

variable {C : Type*} (ops : RingProgram C) (encodeCoefficient : C → List Bool)

def projectedRecord (input : BitCoeffList C) (key : List Bool) : List Bool :=
  framedRecord key (encodeCoefficient (bitScan ops input key).1)

def encodeTerm (term : List Bool × C) : List Bool :=
  framedRecord term.1 (encodeCoefficient term.2)

/-- Exact relation between the per-slot emitted record and the already
verified bit-key projection algorithm, in the same slot order. -/
theorem bitProject_records (slots : List (List Bool)) (input : BitCoeffList C) :
    ((bitProject ops slots input).1.map (encodeTerm encodeCoefficient)) =
      slots.map (projectedRecord ops encodeCoefficient input) := by
  induction slots with
  | nil => rfl
  | cons key slots ih =>
    simp only [bitProject, List.map_cons, encodeTerm, projectedRecord, ih]

end ProjectionSemantics

namespace RawEmitter

open SubexponentialSAT.SubexpRecordScan SubexponentialSAT.SubexpArgumentProgram

def rawWriterStacks : Fin 4 → Fin 6 := ![1, 2, 0, 4]

theorem rawWriterStacks_injective : Function.Injective rawWriterStacks := by decide

abbrev rawWriter : Program 5 6 17 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram writerRegs rawWriterStacks

theorem rawWriter_eval (key coefficient spare output : List Bool) (regs : Fin 5 → Bool) :
    Eval (.call rawWriter) (5 * coefficient.length + 7)
      (recordState regs [] key.reverse spare output coefficient.reverse [])
      (recordState (finishedRegs regs) (true :: Encoding.frame coefficient)
        key.reverse spare output [] []) := by
  let before := recordState regs [] key.reverse spare output coefficient.reverse []
  let after := recordState (finishedRegs regs) (true :: Encoding.frame coefficient)
    key.reverse spare output [] []
  let a := SubexpNormalizeProgram.filterState (regs 0) (regs 1) (regs 2)
    key.reverse spare [] coefficient.reverse
  let b := SubexpNormalizeProgram.filterState true false (regs 2)
    key.reverse spare (true :: Encoding.frame coefficient) []
  have ha : embedState writerRegs rawWriterStacks before a = before := by
    apply embedState_eq_of_ports _ _ _ _ _ writerRegs_injective rawWriterStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState writerRegs rawWriterStacks before b = after := by
    apply embedState_eq_of_ports _ _ _ _ _ writerRegs_injective rawWriterStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := by
        intro h; apply hi; exact ⟨0, by simp [writerRegs, h]⟩
      have h1 : i ≠ 1 := by
        intro h; apply hi; exact ⟨1, by simp [writerRegs, h]⟩
      simp [before, after, finishedRegs, h0, h1]
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := by
        intro h; apply hi; exact ⟨2, by simp [rawWriterStacks, h]⟩
      have h4 : i ≠ 4 := by
        intro h; apply hi; exact ⟨3, by simp [rawWriterStacks, h]⟩
      fin_cases i <;> simp_all [before, after, recordState, storage]
  have ht : Trace SubexpNormalizeProgram.emitRecordProgram (5 * coefficient.length + 7)
      (a.withPC (some SubexpNormalizeProgram.emitRecordProgram.entry)) (b.withPC none) := by
    simpa [a, b] using SubexpNormalizeProgram.emitRecord_trace coefficient key.reverse spare []
      (regs 0) (regs 1) (regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram writerRegs rawWriterStacks
    before writerRegs_injective rawWriterStacks_injective
    (a := a) (b := b) ht
  simpa only [ha, hb, rawWriter] using h

abbrev emitRawTerm : Cmd 5 6 :=
  .seq (.call (StackRoutines.transferProgram 0 4 0 1))
    (.seq (.call rawWriter)
      (.seq (SubexpArgumentProgram.atom (.pop 0 0 1)) emitTerm))

@[simp] theorem storage_update_four (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 4 x = storage a b c d x f := by
  funext i
  fin_cases i <;> rfl

theorem emitRawTerm_eval (key coefficient spare output : List Bool) (regs : Fin 5 → Bool) :
    Eval emitRawTerm (37 * coefficient.length + 21 * key.length + 56)
      (recordState regs coefficient key.reverse spare output [] [])
      (recordState (finishedRegs regs) [] [] spare
        (true :: (Encoding.frame (recordBody key coefficient) ++ output)) [] []) := by
  let r₀ := readRegs regs 0 1 none
  let r₁ := finishedRegs r₀
  let r₂ := readRegs r₁ 0 1 (some true)
  have hreverse : Eval (.call (StackRoutines.transferProgram 0 4 0 1))
      (3 * coefficient.length + 3)
      (recordState regs coefficient key.reverse spare output [] [])
      (recordState r₀ [] key.reverse spare output coefficient.reverse []) := by
    apply Eval.call
    simpa [ListRegisterProgram.Run, StackRoutines.transferStacks, recordState,
      r₀, StructuredProgram.State.withPC] using
      ListRegisterProgram.transfer_run (0 : Fin 6) 4 (0 : Fin 5) 1
        (by decide) (by decide) regs (storage coefficient key.reverse spare output [] [])
  have hwrite := rawWriter_eval key coefficient spare output r₀
  have hpop : Eval (SubexpArgumentProgram.atom (.pop 0 0 1)) 1
      (recordState r₁ (true :: Encoding.frame coefficient) key.reverse spare output [] [])
      (recordState r₂ (Encoding.frame coefficient) key.reverse spare output [] []) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (0 : Fin 6) (0 : Fin 5) 1)
      (recordState r₁ (true :: Encoding.frame coefficient) key.reverse spare output [] [])
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
      recordState, r₂] using h
  have hemit := emitTerm_eval key coefficient [] spare output r₂
  simp only [List.append_nil] at hemit
  have hr : finishedRegs r₂ = finishedRegs regs := by
    funext i
    fin_cases i <;> simp [r₂, r₁, r₀, finishedRegs, readRegs]
  have hn : (3 * coefficient.length + 3) + ((5 * coefficient.length + 7) +
      (1 + (29 * coefficient.length + 21 * key.length + 45))) =
      37 * coefficient.length + 21 * key.length + 56 := by omega
  simpa only [emitRawTerm, hn, hr, List.append_nil] using
    Eval.seq hreverse (Eval.seq hwrite (Eval.seq hpop hemit))

def emitRawTermProgram := StructuredCalls.compiled emitRawTerm 0 3

theorem emitRawTerm_trace (key coefficient spare output : List Bool) (regs : Fin 5 → Bool) :
    Trace emitRawTermProgram (37 * coefficient.length + 21 * key.length + 57)
      ((recordState regs coefficient key.reverse spare output [] []).withPC
        (some emitRawTermProgram.entry))
      ((recordState (finishedRegs regs) [] [] spare
        (true :: (Encoding.frame (recordBody key coefficient) ++ output)) [] []).withPC none) := by
  simpa [emitRawTermProgram, Nat.add_assoc] using
    StructuredCalls.compiled_halt_trace (emitRawTerm_eval key coefficient spare output regs) 0 3

end RawEmitter

end SubexponentialSAT.SubexpDenseProgram
namespace SubexponentialSAT.SubexpDenseProgram.RawParser

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

/-- Unpack the reversed payload supplied by the outer record iterator.
Both output fields are forward bit lists. Port 5 is arbitrary preserved data. -/
abbrev unpack : Cmd 5 6 :=
  .seq (.call (StackRoutines.transferProgram 0 3 0 1))
    (.seq (.call (parseFrame 3 4))
      (.seq (.call (StackRoutines.transferProgram 4 1 0 1))
        (.seq (.call (parseFrame 3 4)) (.call (StackRoutines.transferProgram 4 2 0 1)))))

theorem unpack_eval (regs : Fin 5 → Bool) (key coefficient spare : List Bool) :
    Eval unpack (15 * key.length + 15 * coefficient.length + 23)
      (recordState regs (SubexpArgumentProgram.recordBody key coefficient).reverse [] [] [] [] spare)
      (recordState (readRegs regs 0 1 none) [] key coefficient [] [] spare) := by
  let body := SubexpArgumentProgram.recordBody key coefficient
  let d₀ := recordState regs body.reverse [] [] [] [] spare
  let d₁ := SubexpScanPrimitives.afterTransfer d₀ 0 3 0 1
  have h₀ := SubexpScanPrimitives.transfer_eval d₀ 0 3 0 1 (by decide) (by decide)
  have hi₁ : d₁.stacks 3 = Encoding.frame key ++ Encoding.frame coefficient := by
    simp [d₁, d₀, body, SubexpArgumentProgram.recordBody,
      SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, storage]
  let d₂ := afterFrame d₁ 3 4 key (Encoding.frame coefficient)
  have h₁ := parseFrame_eval d₁ 3 4 (by decide) key (Encoding.frame coefficient) hi₁
  let d₃ := SubexpScanPrimitives.afterTransfer d₂ 4 1 0 1
  have h₂ := SubexpScanPrimitives.transfer_eval d₂ 4 1 0 1 (by decide) (by decide)
  have hi₃ : d₃.stacks 3 = Encoding.frame coefficient ++ [] := by
    simp [d₃, d₂, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, afterFrame]
  let d₄ := afterFrame d₃ 3 4 coefficient []
  have h₃ := parseFrame_eval d₃ 3 4 (by decide) coefficient [] hi₃
  let d₅ := SubexpScanPrimitives.afterTransfer d₄ 4 2 0 1
  have h₄ := SubexpScanPrimitives.transfer_eval d₄ 4 2 0 1 (by decide) (by decide)
  have he : d₅ = recordState (readRegs regs 0 1 none) [] key coefficient [] [] spare := by
    apply SubexpScanPrimitives.state_ext
    · simp [d₅, d₄, d₃, d₂, d₁, d₀, SubexpScanPrimitives.afterTransfer, afterFrame, StackRoutines.readRegs_reset]
    · funext i
      fin_cases i <;>
        simp [d₅, d₄, d₃, d₂, d₁, d₀, SubexpScanPrimitives.afterTransfer, afterFrame,
          StackRoutines.transferStacks, storage]
  have h := Eval.seq h₀ (Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄)))
  change Eval unpack _ d₀ d₅ at h
  rw [he] at h
  have hc₀ : (d₀.stacks 0).length = 2 * key.length + 2 * coefficient.length + 2 := by
    simp [d₀, body, SubexpArgumentProgram.recordBody, Encoding.length_frame]
    omega
  have hc₂ : (d₂.stacks 4).length = key.length := by
    simp [d₂, d₁, d₀, afterFrame, SubexpScanPrimitives.afterTransfer,
      StackRoutines.transferStacks, storage]
  have hc₄ : (d₄.stacks 4).length = coefficient.length := by
    simp [d₄, d₃, d₂, d₁, d₀, afterFrame, SubexpScanPrimitives.afterTransfer,
      StackRoutines.transferStacks, storage]
  have htime : (3 * (d₀.stacks 0).length + 3) +
      ((6 * key.length + 4) + ((3 * (d₂.stacks 4).length + 3) +
        ((6 * coefficient.length + 4) + (3 * (d₄.stacks 4).length + 3)))) =
      15 * key.length + 15 * coefficient.length + 23 := by
    rw [hc₀, hc₂, hc₄]
    omega
  rw [htime] at h
  exact h

def unpackProgram := StructuredCalls.compiled unpack 0 2

theorem unpack_trace (regs : Fin 5 → Bool) (key coefficient spare : List Bool) :
    Trace unpackProgram (15 * key.length + 15 * coefficient.length + 24)
      ((recordState regs (SubexpArgumentProgram.recordBody key coefficient).reverse [] [] [] [] spare).withPC
        (some unpackProgram.entry))
      ((recordState (readRegs regs 0 1 none) [] key coefficient [] [] spare).withPC none) := by
  simpa [unpackProgram, Nat.add_assoc] using
    StructuredCalls.compiled_halt_trace (unpack_eval regs key coefficient spare) 0 2

end SubexponentialSAT.SubexpDenseProgram.RawParser
namespace SubexponentialSAT.SubexpDenseProgram.KeyWidth

open BitProgram

@[simp] theorem update_zero {α : Type*} (a b c x : α) :
    Function.update (![a,b,c] : Fin 3 → α) 0 x = ![x,b,c] := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_one {α : Type*} (a b c x : α) :
    Function.update (![a,b,c] : Fin 3 → α) 1 x = ![a,x,c] := by
  funext i; fin_cases i <;> rfl
@[simp] theorem update_two {α : Type*} (a b c x : α) :
    Function.update (![a,b,c] : Fin 3 → α) 2 x = ![a,b,x] := by
  funext i; fin_cases i <;> rfl

theorem replicate_push (n : ℕ) (b : Bool) (xs : List Bool) :
    List.replicate n b ++ b :: xs = b :: (List.replicate n b ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons b) ih

def cfg {l : ℕ} (pc : Option (Fin l)) (v pr c : Bool)
    (key width scratch : List Bool) : Cfg 3 3 l :=
  ⟨pc, ![v, pr, c], ![key, width, scratch]⟩

/-- Count the actual key bits into a unary width, retaining the original key.
The table is fixed; no numeric width is compiled into its instructions. -/
abbrev program : Program 3 3 9 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code i := match i.val with
    | 0 => .set 2 true 1
    | 1 => .pop 0 0 1 2
    | 2 => .branch 1 3 5
    | 3 => .push 2 0 4
    | 4 => .push 1 2 1
    | 5 => .pop 2 0 1 6
    | 6 => .branch 1 7 8
    | 7 => .push 0 0 5
    | _ => .halt

theorem scan_trace (key width scratch : List Bool) (v pr : Bool) :
    Trace program (4 * key.length + 2)
      (cfg (some 1) v pr true key width scratch)
      (cfg (some 5) false false true []
        (List.replicate key.length true ++ width) (key.reverse ++ scratch)) := by
  induction key generalizing width scratch v pr with
  | nil =>
      refine .cons (b := cfg (some 2) false false true [] width scratch) ?_ ?_
      · simp [step, cfg, execInstr, readRegs]
      simpa using (Computation.Trace.cons
        (by simp [step, cfg, execInstr])
        (Computation.Trace.refl (cfg (some 5) false false true [] width scratch)))
  | cons b key ih =>
      have h : Trace program 4 (cfg (some 1) v pr true (b :: key) width scratch)
          (cfg (some 1) b true true key (true :: width) (b :: scratch)) := by
        refine .cons (b := cfg (some 2) b true true key width scratch) ?_ ?_
        · simp [step, cfg, execInstr, readRegs]
        refine .cons (b := cfg (some 3) b true true key width scratch) ?_ ?_
        · simp [step, cfg, execInstr]
        refine .cons (b := cfg (some 4) b true true key width (b :: scratch)) ?_ ?_
        · simp [step, cfg, execInstr]
        exact .cons (by simp [step, cfg, execInstr]) (.refl _)
      have ht := h.trans (ih (true :: width) (b :: scratch) b true)
      have hn : 4 + (4 * key.length + 2) = 4 * (b :: key).length + 2 := by simp; omega
      rw [hn] at ht
      simpa only [List.length_cons, List.replicate_succ, replicate_push,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append] using ht

theorem restore_trace (scratch key width : List Bool) (v pr : Bool) :
    Trace program (3 * scratch.length + 2)
      (cfg (some 5) v pr true key width scratch)
      (cfg (some 8) false false true (scratch.reverse ++ key) width []) := by
  induction scratch generalizing key v pr with
  | nil =>
      refine .cons (b := cfg (some 6) false false true key width []) ?_ ?_
      · simp [step, cfg, execInstr, readRegs]
      simpa using (Computation.Trace.cons
        (by simp [step, cfg, execInstr])
        (Computation.Trace.refl (cfg (some 8) false false true key width [])))
  | cons b scratch ih =>
      have h : Trace program 3 (cfg (some 5) v pr true key width (b :: scratch))
          (cfg (some 5) b true true (b :: key) width scratch) := by
        refine .cons (b := cfg (some 6) b true true key width scratch) ?_ ?_
        · simp [step, cfg, execInstr, readRegs]
        refine .cons (b := cfg (some 7) b true true key width scratch) ?_ ?_
        · simp [step, cfg, execInstr]
        exact .cons (by simp [step, cfg, execInstr]) (.refl _)
      have ht := h.trans (ih (b :: key) b true)
      have hn : 3 + (3 * scratch.length + 2) = 3 * (b :: scratch).length + 2 := by simp; omega
      rw [hn] at ht
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ht

theorem program_trace (key width : List Bool) (v pr c : Bool) :
    Trace program (7 * key.length + 6)
      (cfg (some program.entry) v pr c key width [])
      (cfg none false false true key (List.replicate key.length true ++ width) []) := by
  have h₀ : Trace program 1 (cfg (some program.entry) v pr c key width [])
      (cfg (some 1) v pr true key width []) :=
    .cons (by simp [step, cfg, execInstr]) (.refl _)
  have h₁ := scan_trace key width [] v pr
  simp only [List.append_nil] at h₁
  have h₂ := restore_trace key.reverse [] (List.replicate key.length true ++ width)
    false false
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  have h₃ : Trace program 1
      (cfg (some 8) false false true key (List.replicate key.length true ++ width) [])
      (cfg none false false true key (List.replicate key.length true ++ width) []) :=
    .cons (by simp [step, cfg, execInstr]) (.refl _)
  convert h₀.trans (h₁.trans (h₂.trans h₃)) using 1 ; omega

theorem fixedKey_trace {D : ℕ} (a : SymbolicCost.RawIndex D)
    (ha : SymbolicCost.Retained D a) (width : List Bool) (v pr c : Bool) :
    Trace program (7 * SubexpSymbolicCost.indexBits D + 6)
      (cfg (some program.entry) v pr c (SubexpSymbolicCost.fixedKey a) width [])
      (cfg none false false true (SubexpSymbolicCost.fixedKey a)
        (List.replicate (SubexpSymbolicCost.indexBits D) true ++ width) []) := by
  simpa only [SubexpSymbolicCost.fixedKey_length a ha] using
    program_trace (SubexpSymbolicCost.fixedKey a) width v pr c

end SubexponentialSAT.SubexpDenseProgram.KeyWidth

end OAI.Algorithms
