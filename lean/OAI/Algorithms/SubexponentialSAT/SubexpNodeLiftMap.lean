import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFlatLift
import OAI.Algorithms.SubexponentialSAT.SubexpNodeLiftData
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram

namespace OAI.Algorithms

/-!
# Actual record mapping of generated field nodes into the lift ring

The scalar modulus and the two word-width shapes are explicit preserved tape
inputs. Parser registers are disjoint from the eight registers used by the
four-word arithmetic conversion.
-/

namespace SubexponentialSAT.SubexpNodeLiftMap

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open Subexp.TupleProgram (pushConst pushedState pushConst_eval escape escapedState
  escape_eval_state prependRecord)

abbrev Data := State 11 20

def liftRegisters (i : Fin 8) : Fin 11 := ⟨i.val, by omega⟩

theorem liftRegisters_injective : Function.Injective liftRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)

def ports : RecordPrograms.Ports 11 20 :=
  ⟨8, 9, 10, 14, 15, by decide, by decide, by decide, by decide⟩

def emitPorts : RecordPrograms.Ports 11 20 :=
  ⟨0, 1, 2, 15, 16, by decide, by decide, by decide, by decide⟩

def flatState (regs : Fin 11 → Bool) (modulus sourceWidth targetWidth raw : List Bool)
    (frame : Fin 6 → List Bool) : Data :=
  ⟨regs, SubexpFlatLift.stackArray [] modulus [] [] raw [] sourceWidth targetWidth [] [] frame⟩

abbrev lift : Cmd 11 20 :=
  .call (ProgramLinking.liftProgram SubexpFlatLift.program liftRegisters id)

theorem encode_eq {B : ℕ} (a : Quad (Word B)) :
    SubexpFlatLift.encode a = SubexpNodeLiftData.encode a := by
  simp [SubexpFlatLift.encode, SubexpFlatLift.flatten, SubexpFlatLift.quadWords,
    SubexpNodeLiftData.encode, List.append_assoc]

theorem readRegs_frame (regs : Fin 11 → Bool) (i : Fin 11) (hi : 8 ≤ i.val) :
    readRegs regs 0 1 none i = regs i := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
  simp [readRegs, h0, h1]

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)

theorem lift_eval (hμ : 0 < μ) (regs : Fin 11 → Bool)
    (a : Quad (Word (baseWidth p 1))) (sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sourceWidth.length = baseWidth p 1) (hB : targetWidth.length = baseWidth p μ) :
    ∃ n ≤ 2100 * (baseWidth p 1 + baseWidth p μ + 2)^2, ∃ rf,
      (∀ i : Fin 11, 8 ≤ i.val → rf i = regs i) ∧
      Eval lift n
        (flatState regs M.bits sourceWidth targetWidth (SubexpNodeLiftData.encode a) frame)
        (flatState rf M.bits sourceWidth targetWidth
          (SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M a).1) frame) := by
  obtain ⟨smallRegs, n, hn, ht⟩ := SubexpFlatLift.program_runs p μ M hμ
    (regs ∘ liftRegisters) a sourceWidth targetWidth frame hb hB
  let before := SubexpFlatLift.ready (regs ∘ liftRegisters) M.bits
    (SubexpFlatLift.encode a) [] sourceWidth targetWidth frame
  let after := SubexpFlatLift.ready smallRegs M.bits
    (SubexpFlatLift.encode (SubexpWordLift.liftQuadRun p μ M a).1) []
    sourceWidth targetWidth frame
  let big := flatState regs M.bits sourceWidth targetWidth (SubexpNodeLiftData.encode a) frame
  let rf := Function.extend liftRegisters smallRegs regs
  have ha : embedState liftRegisters id big before = big := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases h : ∃ j, liftRegisters j = i
      · obtain ⟨j, rfl⟩ := h
        exact liftRegisters_injective.extend_apply _ _ j
      · exact Function.extend_apply' _ _ _ h
    · simp only [ProgramLinking.extend_id]
      exact congrArg (fun raw => SubexpFlatLift.stackArray [] M.bits [] [] raw []
        sourceWidth targetWidth [] [] frame) (encode_eq a)
  have he : embedState liftRegisters id big after =
      flatState rf M.bits sourceWidth targetWidth
        (SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M a).1) frame := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · simp only [ProgramLinking.extend_id]
      exact congrArg (fun raw => SubexpFlatLift.stackArray [] M.bits [] [] raw []
        sourceWidth targetWidth [] [] frame) (encode_eq _)
  refine ⟨n, hn, rf, ?_, ?_⟩
  · intro i hi
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    have h := congrArg (fun x : Fin 11 => x.val) hj
    simp only [liftRegisters] at h
    omega
  · have hh := eval_call_lifted SubexpFlatLift.program liftRegisters id big
      liftRegisters_injective Function.injective_id (a := before) (b := after) ht
    simpa only [ha, he] using hh

theorem transfer_in_eval (regs : Fin 11 → Bool) (modulus sw tw bits : List Bool)
    (frame : Fin 6 → List Bool) (hf : frame 1 = []) :
    Eval (.call (StackRoutines.transferProgram 15 8 (0 : Fin 11) 1))
      (3 * bits.length + 3)
      (flatState regs modulus sw tw [] (Function.update frame 1 bits.reverse))
      (flatState (readRegs regs 0 1 none) modulus sw tw bits frame) := by
  have h := Subexp.TupleProgram.transfer_eval 15 8 0 1 (by decide) (by decide)
    (flatState regs modulus sw tw [] (Function.update frame 1 bits.reverse))
  convert h using 1
  · simp [flatState, SubexpFlatLift.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [flatState, SubexpFlatLift.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
          StackRoutines.transferStacks, hf]

theorem transfer_out_eval (regs : Fin 11 → Bool) (modulus sw tw bits : List Bool)
    (frame : Fin 6 → List Bool) (hf : frame 1 = []) :
    Eval (.call (StackRoutines.transferProgram 8 15 (0 : Fin 11) 1))
      (3 * bits.length + 3)
      (flatState regs modulus sw tw bits frame)
      (flatState (readRegs regs 0 1 none) modulus sw tw []
        (Function.update frame 1 bits.reverse)) := by
  have h := Subexp.TupleProgram.transfer_eval 8 15 0 1 (by decide) (by decide)
    (flatState regs modulus sw tw bits frame)
  convert h using 1
  · simp [flatState, SubexpFlatLift.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [flatState, SubexpFlatLift.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
          StackRoutines.transferStacks, hf]

abbrev emit : Cmd 11 20 :=
  .seq (pushConst 16 0 false) (.seq (escape emitPorts) (pushConst 16 0 true))

def emitted (a : Data) : Data :=
  pushedState 16 0 true (escapedState emitPorts (pushedState 16 0 false a))

theorem emit_eval_state (a : Data) :
    Eval emit (5 * (a.stacks 15).length + 7) a (emitted a) := by
  have h := (pushConst_eval 16 0 false a).seq
    ((escape_eval_state emitPorts (pushedState 16 0 false a)).seq
      (pushConst_eval 16 0 true (escapedState emitPorts (pushedState 16 0 false a))))
  convert h using 1
  · simp [emitPorts]
    omega
  · simp [emitted, emitPorts, pushedState]

theorem emit_eval (regs : Fin 11 → Bool) (modulus sw tw bits : List Bool)
    (frame : Fin 6 → List Bool) (hf : frame 1 = []) :
    ∃ rf, (∀ i : Fin 11, 8 ≤ i.val → rf i = regs i) ∧
      Eval emit (5 * bits.length + 7)
        (flatState regs modulus sw tw [] (Function.update frame 1 bits.reverse))
        (flatState rf modulus sw tw []
          (Function.update frame 2 (prependRecord bits (frame 2)))) := by
  let a := flatState regs modulus sw tw [] (Function.update frame 1 bits.reverse)
  let rf := (emitted a).regs
  have he : emitted a = flatState rf modulus sw tw []
      (Function.update frame 2 (prependRecord bits (frame 2))) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [a, flatState, SubexpFlatLift.stackArray, Fin.addCases,
          Fin.coe_ofNat_eq_mod, emitPorts, hf, prependRecord, Subexp.TupleProgram.frame_eq_escaped,
          List.append_assoc]
  refine ⟨rf, ?_, ?_⟩
  · intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    simp [rf, emitted, a, flatState, pushedState, emitPorts,
      readRegs, h0, h1]
  · have h := emit_eval_state a
    rw [he] at h
    simpa [a, flatState, SubexpFlatLift.stackArray, Fin.addCases,
      Fin.coe_ofNat_eq_mod] using h

abbrev callback : Cmd 11 20 :=
  .seq (.call (StackRoutines.transferProgram 15 8 (0 : Fin 11) 1))
    (.seq lift (.seq (.call (StackRoutines.transferProgram 8 15 (0 : Fin 11) 1)) emit))

theorem callback_eval (hμ : 0 < μ) (regs : Fin 11 → Bool)
    (a : Quad (Word (baseWidth p 1))) (sourceWidth targetWidth : List Bool)
    (frame : Fin 6 → List Bool) (hf : frame 1 = [])
    (hb : sourceWidth.length = baseWidth p 1) (hB : targetWidth.length = baseWidth p μ) :
    ∃ n ≤ 2200 * (baseWidth p 1 + baseWidth p μ + 2)^2, ∃ rf,
      (∀ i : Fin 11, 8 ≤ i.val → rf i = regs i) ∧
      Eval callback n
        (flatState regs M.bits sourceWidth targetWidth []
          (Function.update frame 1 (SubexpNodeLiftData.encode a).reverse))
        (flatState rf M.bits sourceWidth targetWidth []
          (Function.update frame 2 (prependRecord
            (SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M a).1) (frame 2)))) := by
  let bits := SubexpNodeLiftData.encode a
  let out := SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M a).1
  let r₁ := readRegs regs 0 1 none
  have h₁ := transfer_in_eval regs M.bits sourceWidth targetWidth bits frame hf
  obtain ⟨n, hn, r₂, hr₂, h₂⟩ := lift_eval p μ M hμ r₁ a sourceWidth targetWidth frame hb hB
  let r₃ := readRegs r₂ 0 1 none
  have h₃ := transfer_out_eval r₂ M.bits sourceWidth targetWidth out frame hf
  obtain ⟨rf, hrf, h₄⟩ := emit_eval r₃ M.bits sourceWidth targetWidth out frame hf
  refine ⟨(3 * bits.length + 3) + (n + ((3 * out.length + 3) + (5 * out.length + 7))),
    ?_, rf, ?_, h₁.seq (h₂.seq (h₃.seq h₄))⟩
  · have hb' : bits.length = 4 * baseWidth p 1 := SubexpNodeLiftData.encode_length a
    have hB' : out.length = 4 * baseWidth p μ := SubexpNodeLiftData.encode_length _
    have hsq : baseWidth p 1 + baseWidth p μ + 2 ≤
        (baseWidth p 1 + baseWidth p μ + 2)^2 := by
      nlinarith
    rw [hb', hB']
    omega
  · intro i hi
    calc
      rf i = r₃ i := hrf i hi
      _ = r₂ i := readRegs_frame r₂ i hi
      _ = r₁ i := hr₂ i hi
      _ = regs i := readRegs_frame regs i hi

def invariant (modulus sw tw : List Bool) (a : Data) : Prop :=
  ∃ frame, a.stacks = (flatState a.regs modulus sw tw [] frame).stacks

def effect (bits : List Bool) (before after : Data) : Prop :=
  ∀ q : Quad (Word (baseWidth p 1)), SubexpNodeLiftData.encode q = bits →
    after.stacks 16 = prependRecord
      (SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M q).1) (before.stacks 16)

def validPayload (bits : List Bool) : Prop :=
  ∃ q : Quad (Word (baseWidth p 1)), SubexpNodeLiftData.encode q = bits

theorem callback_contract (hμ : 0 < μ) (sw tw : List Bool)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (fun _ => 2200 * (baseWidth p 1 + baseWidth p μ + 2)^2)
      (invariant M.bits sw tw) (effect p μ M) (validPayload p) := by
  intro bits tail base hv hi
  obtain ⟨q, rfl⟩ := hv
  obtain ⟨frame, hframe⟩ := hi
  let parsed := RecordPrograms.state ports base false true false tail
    (SubexpNodeLiftData.encode q).reverse
  let f := Function.update (Function.update frame 0 tail) 1 []
  have hf : f 1 = [] := by simp [f]
  have hparsed : parsed = flatState parsed.regs M.bits sw tw []
      (Function.update f 1 (SubexpNodeLiftData.encode q).reverse) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [ports, flatState, SubexpFlatLift.stackArray,
          Fin.addCases, Fin.coe_ofNat_eq_mod, f, hframe]
  obtain ⟨n, hn, rf, hrf, hrun⟩ := callback_eval p μ M hμ parsed.regs q sw tw f hf hb hB
  let f' := Function.update f 2 (prependRecord
    (SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M q).1) (f 2))
  let next := flatState rf M.bits sw tw [] f'
  have hnext : RecordPrograms.state ports next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · exact (hrf 8 (by decide)).trans (RecordPrograms.state_tag ports base _ _ _ _ _)
    · exact (hrf 9 (by decide)).trans (RecordPrograms.state_present ports base _ _ _ _ _)
    · exact (hrf 10 (by decide)).trans (RecordPrograms.state_found ports base _ _ _ _ _)
    · simp [next, flatState, SubexpFlatLift.stackArray, Fin.addCases,
        Fin.coe_ofNat_eq_mod, ports, f', f]
    · simp [next, flatState, SubexpFlatLift.stackArray, Fin.addCases,
        Fin.coe_ofNat_eq_mod, ports, f', f]
  refine ⟨n, next, hn, ⟨f', rfl⟩, ?_, ?_⟩
  · intro q' heq
    have hwidth : 0 < baseWidth p 1 := by simp [baseWidth]
    have hsame := SubexpNodeLiftData.encode_injective hwidth heq
    subst q'
    change next.stacks 16 = _
    simp [next, flatState, SubexpFlatLift.stackArray, Fin.addCases,
      Fin.coe_ofNat_eq_mod, f', f, hframe]
  · rw [hnext]
    simpa only [← hparsed] using hrun

omit [Fact p.Prime] in
theorem visits_result (xs : List (Quad (Word (baseWidth p 1))))
    (before after : Data) (acc : List (List Bool))
    (hacc : before.stacks 16 = ProgramEncoding.encodeRecords acc)
    (hv : RecordPrograms.Visits (fun _ => false) (effect p μ M)
      (xs.map SubexpNodeLiftData.encode) before after) :
    after.stacks 16 = ProgramEncoding.encodeRecords
      ((xs.map (fun q => SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M q).1)).reverse ++ acc) := by
  induction xs generalizing before acc with
  | nil =>
      cases hv
      simpa using hacc
  | cons q qs ih =>
      cases hv with
      | hit h _ => cases h
      | @miss _ _ _ middle _ _ he ht =>
          have hmiddle : middle.stacks 16 = ProgramEncoding.encodeRecords
              (SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M q).1 :: acc) := by
            rw [he q rfl, hacc]
            rfl
          have hrest := ih middle _ hmiddle ht
          simpa [List.map_cons, List.reverse_cons, List.append_assoc] using hrest

theorem invariant_recordState (modulus sw tw : List Bool) (a : Data)
    (hi : invariant modulus sw tw a) (v pr f : Bool) (source payload : List Bool) :
    invariant modulus sw tw (RecordPrograms.state ports a v pr f source payload) := by
  obtain ⟨frame, hframe⟩ := hi
  refine ⟨Function.update (Function.update frame 0 source) 1 payload, ?_⟩
  funext i
  fin_cases i <;>
    simp [RecordPrograms.state, ports, flatState, SubexpFlatLift.stackArray,
      Fin.addCases, Fin.coe_ofNat_eq_mod, hframe]

def mapCost (b B n : ℕ) : ℕ := 3 + n * (2200 * (b + B + 2)^2 + 24 * b + 7)

theorem budget_quads (b cost : ℕ) (xs : List (Quad (Word b))) :
    RecordPrograms.budget (fun _ => cost) (xs.map SubexpNodeLiftData.encode) =
      xs.length * (cost + 24 * b + 7) := by
  induction xs with
  | nil => simp [RecordPrograms.budget]
  | cons q qs ih =>
      simp only [List.map_cons, RecordPrograms.budget, SubexpNodeLiftData.encode_length,
        List.length_cons, ih]
      ring

theorem iterate_eval (hμ : 0 < μ) (xs : List (Quad (Word (baseWidth p 1))))
    (sw tw : List Bool) (base : Data)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ)
    (hi : invariant M.bits sw tw base)
    (hsource : base.stacks 14 = ProgramEncoding.encodeRecords (xs.map SubexpNodeLiftData.encode))
    (hpayload : base.stacks 15 = []) (hacc : base.stacks 16 = ProgramEncoding.encodeRecords []) :
    ∃ n ≤ mapCost (baseWidth p 1) (baseWidth p μ) xs.length, ∃ next,
      invariant M.bits sw tw next ∧ next.stacks 14 = [] ∧ next.stacks 15 = [] ∧
      next.stacks 16 = ProgramEncoding.encodeRecords
        ((xs.map (fun q => SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M q).1)).reverse) ∧
      Eval (RecordPrograms.iterate ports callback) n base next := by
  have hv : ∀ bits ∈ xs.map SubexpNodeLiftData.encode, validPayload p bits := by
    intro bits h
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp h
    exact ⟨q, rfl⟩
  obtain ⟨n, next, hn, hnext, hvisit, hrun⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (fun _ => 2200 * (baseWidth p 1 + baseWidth p μ + 2)^2)
    (invariant M.bits sw tw) (effect p μ M) (validPayload p)
    (callback_contract p μ M hμ sw tw hb hB)
    (xs.map SubexpNodeLiftData.encode) [] base hv hi (base.regs 8) (base.regs 9) (base.regs 10)
  have hstart : RecordPrograms.state ports base (base.regs 8) (base.regs 9) (base.regs 10)
      (Encoding.encodeList id (xs.map SubexpNodeLiftData.encode) ++ []) [] = base := by
    apply RecordPrograms.state_eq_self <;> try rfl
    · change base.stacks 14 = _
      simpa only [ProgramEncoding.encodeRecords, List.append_nil] using hsource
    · exact hpayload
  have hfinish :
      (xs.map SubexpNodeLiftData.encode).any (fun _ => false) = false := by simp
  have hunread : RecordPrograms.unread (fun _ => false)
      (xs.map SubexpNodeLiftData.encode) [] = [] := by
    induction xs <;> simp_all
  rw [hstart, hfinish, hunread] at hrun
  let final := RecordPrograms.state ports next false true false [] []
  have hout := visits_result p μ M xs base next [] hacc hvisit
  have hbudget : RecordPrograms.budget
      (fun _ => 2200 * (baseWidth p 1 + baseWidth p μ + 2)^2)
      (xs.map SubexpNodeLiftData.encode) =
      xs.length * (2200 * (baseWidth p 1 + baseWidth p μ + 2)^2 + 24 * baseWidth p 1 + 7) := by
    exact budget_quads _ _ xs
  refine ⟨n, ?_, final, invariant_recordState _ _ _ next hnext _ _ _ _ _,
    RecordPrograms.state_source _ _ _ _ _ _ _, RecordPrograms.state_payload _ _ _ _ _ _ _, ?_, hrun⟩
  · simpa only [hbudget, mapCost] using hn
  · simpa [final, RecordPrograms.state, ports] using hout

def reverseRegisters : Fin 3 → Fin 11 := ![8, 9, 10]
def reverseStacks : Fin 4 → Fin 20 := ![16, 17, 14, 15]

theorem reverseRegisters_injective : Function.Injective reverseRegisters := by decide
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev reverseRecords : Cmd 11 20 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    reverseRegisters reverseStacks)

def reversed (a : Data) (output : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 8 false) 9 true) 10 false,
    Function.update (Function.update a.stacks 16 []) 14 output⟩

theorem reverse_eval (a : Data) (records : List (List Bool))
    (hin : a.stacks 16 = ProgramEncoding.encodeRecords records)
    (hout : a.stacks 14 = ProgramEncoding.encodeRecords []) (hpayload : a.stacks 15 = []) :
    ∃ n ≤ 10 * (ProgramEncoding.encodeRecords records).length,
      Eval reverseRecords n a (reversed a (ProgramEncoding.encodeRecords records.reverse)) := by
  let small := SubexpNormalizeProgram.filterState (a.regs 8) (a.regs 9) (a.regs 10)
    (ProgramEncoding.encodeRecords records) (a.stacks 17) (ProgramEncoding.encodeRecords []) []
  let result := SubexpNormalizeProgram.filterState false true false [] (a.stacks 17)
    (ProgramEncoding.encodeRecords records.reverse) []
  have hs : embedState reverseRegisters reverseStacks a small = a := by
    apply SubexpScanPrimitives.embedState_eq _ _ reverseRegisters_injective reverseStacks_injective
    · intro i; fin_cases i <;> simp [small, reverseRegisters, SubexpNormalizeProgram.filterState]
    · intro i; fin_cases i <;> simp [small, reverseStacks, SubexpNormalizeProgram.filterState,
        hin, hout, hpayload]
    · intros; rfl
    · intros; rfl
  have ht : embedState reverseRegisters reverseStacks a result =
      reversed a (ProgramEncoding.encodeRecords records.reverse) := by
    apply SubexpScanPrimitives.embedState_eq _ _ reverseRegisters_injective reverseStacks_injective
    · intro i; fin_cases i <;> simp [result, reverseRegisters, reversed,
        SubexpNormalizeProgram.filterState]
    · intro i; fin_cases i <;> simp [result, reverseStacks, reversed,
        SubexpNormalizeProgram.filterState, hpayload]
    · intro i hi
      have h8 : i ≠ 8 := fun h => hi ⟨0, by simpa [reverseRegisters] using h.symm⟩
      have h9 : i ≠ 9 := fun h => hi ⟨1, by simpa [reverseRegisters] using h.symm⟩
      have h10 : i ≠ 10 := fun h => hi ⟨2, by simpa [reverseRegisters] using h.symm⟩
      simp [reversed, h8, h9, h10]
    · intro i hi
      have h16 : i ≠ 16 := fun h => hi ⟨0, by simpa [reverseStacks] using h.symm⟩
      have h14 : i ≠ 14 := fun h => hi ⟨2, by simpa [reverseStacks] using h.symm⟩
      simp [reversed, h16, h14]
  obtain ⟨n, hn, hrun⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] []
    (a.stacks 17) (a.regs 8) (a.regs 9) (a.regs 10)
  have hrun' : Trace SubexpNormalizeProgram.reverseRecordsProgram n
      (small.withPC (some SubexpNormalizeProgram.reverseRecordsProgram.entry))
      (result.withPC none) := by simpa only [List.append_nil] using hrun
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters
    reverseStacks a reverseRegisters_injective reverseStacks_injective hrun'
  exact ⟨n, hn, by simpa only [hs, ht, reverseRecords] using he⟩

abbrev cmd : Cmd 11 20 :=
  .seq (pushConst 16 0 false)
    (.seq (RecordPrograms.iterate ports callback) (.seq (pushConst 14 0 false) reverseRecords))

def program := StructuredCalls.compiled cmd 14 14

def runtime (b B n : ℕ) : ℕ := mapCost b B n + 10 * ((8 * B + 2) * n + 1) + 5

theorem program_runs (hμ : 0 < μ) (xs : List (Quad (Word (baseWidth p 1))))
    (sw tw : List Bool) (base : Data)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ)
    (hi : invariant M.bits sw tw base)
    (hsource : base.stacks 14 = ProgramEncoding.encodeRecords (xs.map SubexpNodeLiftData.encode))
    (hpayload : base.stacks 15 = []) (hacc : base.stacks 16 = []) :
    ∃ next : Data,
      next.stacks 14 = ProgramEncoding.encodeRecords
        (xs.map (fun q => SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M q).1)) ∧
      RunsIn program (runtime (baseWidth p 1) (baseWidth p μ) xs.length)
        (base.withPC (some program.entry)) (next.withPC none) := by
  let a := pushedState 16 0 false base
  have ha : invariant M.bits sw tw a := by
    obtain ⟨frame, hframe⟩ := hi
    refine ⟨Function.update frame 2 (false :: frame 2), ?_⟩
    funext i
    fin_cases i <;>
      simp [a, flatState, SubexpFlatLift.stackArray, Fin.addCases,
        Fin.coe_ofNat_eq_mod, hframe]
  have ha14 : a.stacks 14 = ProgramEncoding.encodeRecords (xs.map SubexpNodeLiftData.encode) := by
    simpa [a, pushedState] using hsource
  have ha15 : a.stacks 15 = [] := by simpa [a, pushedState] using hpayload
  have ha16 : a.stacks 16 = ProgramEncoding.encodeRecords [] := by
    simp [a, hacc, ProgramEncoding.encodeRecords, Encoding.encodeList]
  obtain ⟨nm, hnm, b, _, hb14, hb15, hb16, hm⟩ :=
    iterate_eval p μ M hμ xs sw tw a hb hB ha ha14 ha15 ha16
  let c := pushedState 14 0 false b
  let result := xs.map (fun q => SubexpNodeLiftData.encode (SubexpWordLift.liftQuadRun p μ M q).1)
  have hc16 : c.stacks 16 = ProgramEncoding.encodeRecords result.reverse := by
    simpa [c, pushedState, result] using hb16
  have hc14 : c.stacks 14 = ProgramEncoding.encodeRecords [] := by
    simp [c, hb14, ProgramEncoding.encodeRecords, Encoding.encodeList]
  have hc15 : c.stacks 15 = [] := by simpa [c, pushedState] using hb15
  obtain ⟨nr, hnr, hr⟩ := reverse_eval c result.reverse hc16 hc14 hc15
  have hlen : (ProgramEncoding.encodeRecords result.reverse).length ≤
      (8 * baseWidth p μ + 2) * xs.length + 1 := by
    have hw : ∀ bits ∈ result.reverse, bits.length ≤ 4 * baseWidth p μ := by
      intro bits hbits
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hbits)
      exact le_of_eq (SubexpNodeLiftData.encode_length _)
    have h := ProgramEncoding.encodeRecords_length_le result.reverse (4 * baseWidth p μ) hw
    convert h using 1
    all_goals simp [result]
    all_goals ring
  refine ⟨reversed c (ProgramEncoding.encodeRecords result.reverse.reverse), ?_,
    2 + (nm + (2 + nr)) + 1, ?_, ?_⟩
  · simp [reversed, result]
  · unfold runtime
    omega
  · exact compiled_halt_trace ((pushConst_eval 16 0 false base).seq
      (hm.seq ((pushConst_eval 14 0 false b).seq hr))) 14 14

theorem runtime_le (b B n : ℕ) : runtime b B n ≤ 2500 * (n + 1) * (b + B + 2)^2 := by
  have hs : b + B + 2 ≤ (b + B + 2)^2 := by nlinarith
  have hrow : 2200 * (b + B + 2)^2 + 24 * b + 80 * B + 27 ≤
      2400 * (b + B + 2)^2 := by omega
  have hm := Nat.mul_le_mul_left n hrow
  have hr : runtime b B n = 18 + n * (2200 * (b + B + 2)^2 + 24 * b + 80 * B + 27) := by
    unfold runtime mapCost
    ring
  rw [hr]
  nlinarith

theorem node_program_runs (hμ : 0 < μ) (sw tw : List Bool) (base : Data)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ)
    (hi : invariant M.bits sw tw base)
    (hsource : base.stacks 14 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p))
    (hpayload : base.stacks 15 = []) (hacc : base.stacks 16 = []) :
    ∃ next : Data,
      next.stacks 14 = ProgramEncoding.encodeRecords (SubexpNodeLiftData.liftedNodeWords p μ M) ∧
      RunsIn program (2500 * (p^4 - 1 + 1) * (baseWidth p 1 + baseWidth p μ + 2)^2)
        (base.withPC (some program.entry)) (next.withPC none) := by
  have hs : base.stacks 14 = ProgramEncoding.encodeRecords
      ((SubexpNodeLiftData.nodeQuads p).map SubexpNodeLiftData.encode) := by
    rw [SubexpNodeLiftData.nodeQuads_encoded]
    exact hsource
  obtain ⟨next, hout, hr⟩ := program_runs p μ M hμ (SubexpNodeLiftData.nodeQuads p)
    sw tw base hb hB hi hs hpayload hacc
  refine ⟨next, hout, hr.mono ?_⟩
  simpa [SubexpNodeLiftData.nodeQuads] using
    runtime_le (baseWidth p 1) (baseWidth p μ) (SubexpNodeLiftData.nodeQuads p).length

theorem node_program_primitive (hμ : 0 < μ) (sw tw : List Bool) (base : Data)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ)
    (hi : invariant M.bits sw tw base)
    (hsource : base.stacks 14 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p))
    (hpayload : base.stacks 15 = []) (hacc : base.stacks 16 = []) :
    ∃ next : Data,
      next.stacks 14 = ProgramEncoding.encodeRecords (SubexpNodeLiftData.liftedNodeWords p μ M) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          (2500 * (p^4 - 1 + 1) * (baseWidth p 1 + baseWidth p μ + 2)^2))
        (primitiveCfg program (base.withPC (some program.entry)))
        (primitiveCfg program (next.withPC none)) := by
  obtain ⟨next, hout, hr⟩ := node_program_runs p μ M hμ sw tw base hb hB hi hsource hpayload hacc
  exact ⟨next, hout, primitive_execution program hr⟩

end SubexponentialSAT.SubexpNodeLiftMap

end OAI.Algorithms
