import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumerationCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchControl
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

abbrev Data := State 19 24

def lowRegs (i : Fin 16) : Fin 19 := Fin.castAdd 3 i
def lowStacks (i : Fin 18) : Fin 24 := Fin.castAdd 6 i

def splitStacks : Fin 6 → Fin 24 := ![1,22,2,3,0,4]

theorem lowRegs_injective : Function.Injective lowRegs := Fin.castAdd_injective _ _
theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _
theorem splitStacks_injective : Function.Injective splitStacks := by decide

def ports : RecordPrograms.Ports 19 24 :=
  ⟨16,17,18,18,19,by decide,by decide,by decide,by decide⟩

def wide (low : State 16 18) (tag present found : Bool)
    (source payload saved count extra : List Bool) : Data :=
  ⟨Fin.addCases (m := 16) (n := 3) (motive := fun _ => Bool)
      low.regs ![tag,present,found],
    Fin.addCases (m := 18) (n := 6) (motive := fun _ => List Bool)
      low.stacks ![source,payload,saved,[],count,extra]⟩

theorem embed_wide (before after : State 16 18) (tag present found : Bool)
    (source payload saved count extra : List Bool) :
    embedState lowRegs lowStacks (wide before tag present found source payload saved count extra)
      after = wide after tag present found source payload saved count extra := by
  apply SubexpScanPrimitives.embedState_eq lowRegs lowStacks lowRegs_injective lowStacks_injective
  · intro i; simp [wide, lowRegs]
  · intro i; simp [wide, lowStacks]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 16) (n := 3) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 18) (n := 6) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]

abbrev split : Cmd 19 24 := .call (ProgramLinking.liftProgram
  IrreducibleSearchPairAdapter.program lowRegs splitStacks)
abbrev checkPair : Cmd 19 24 := .call (ProgramLinking.liftProgram pairProgram lowRegs lowStacks)
abbrev unpack : Cmd 19 24 := .call (StackRoutines.transferProgram 19 1 16 17)
abbrev clear (i : Fin 24) : Cmd 19 24 := .call (StackRoutines.clearProgram i 16 17)
abbrev saveResult : Cmd 19 24 := .base (.atom (.copy 18 3))
abbrev presentTrue : Cmd 19 24 := .base (.atom (.set 17 true))
abbrev callback : Cmd 19 24 :=
  .seq unpack (.seq split (.seq checkPair
    (.seq saveResult (.seq (clear 0) (.seq (clear 1) presentTrue)))))
abbrev allCommand : Cmd 19 24 := Subexp.BlockSearchProgram.allCommand ports callback
def program := compiled allCommand 18 18

private theorem split_restrict (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (regs : Fin 16 → Bool) :
    restrictState lowRegs splitStacks
      (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra) =
    IrreducibleSearchPairAdapter.input as bs count regs := by
  apply SubexpScanPrimitives.state_ext
  · funext i; simp [restrictState, lowRegs, wide, IrreducibleSearchPairAdapter.input, pairState]
  · funext i; fin_cases i <;>
      simp [restrictState, splitStacks, wide, pairState, IrreducibleSearchPairAdapter.input]

private theorem split_embed (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (regs rf : Fin 16 → Bool) :
    embedState lowRegs splitStacks
      (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra)
      (IrreducibleSearchPairAdapter.output as bs count rf) =
      wide (pairState as bs cs depth [] [] [] rf)
        false false false source [] saved count extra := by
  apply SubexpScanPrimitives.embedState_eq lowRegs splitStacks lowRegs_injective splitStacks_injective
  · intro i; simp [wide, lowRegs, IrreducibleSearchPairAdapter.output, pairState]
  · intro i; fin_cases i <;>
      simp [wide, splitStacks, IrreducibleSearchPairAdapter.output, pairState]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 16) (n := 3) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]
  · intro j hj
    have h0 : j ≠ 0 := fun h => hj ⟨4, by simpa [splitStacks] using h.symm⟩
    have h1 : j ≠ 1 := fun h => hj ⟨0, by simpa [splitStacks] using h.symm⟩
    fin_cases j <;> simp_all [wide, pairState]

theorem split_eval (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (hc : count.length = as.length)
    (regs : Fin 16 → Bool) :
    ∃ n rf, n ≤ 28 * count.length + 17 ∧ Eval split n
      (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra)
      (wide (pairState as bs cs depth [] [] [] rf)
        false false false source [] saved count extra) := by
  obtain ⟨rf, hr⟩ := IrreducibleSearchPairAdapter.program_runsIn as bs count hc regs
  obtain ⟨n, hn, he⟩ := lifted_call IrreducibleSearchPairAdapter.program lowRegs splitStacks
    lowRegs_injective splitStacks_injective
    (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
      false false false source [] saved count extra)
    (IrreducibleSearchPairAdapter.output as bs count rf) (28 * count.length + 17)
    (by rw [split_restrict]; exact hr)
  exact ⟨n, rf, hn, by simpa only [split, split_embed] using he⟩

theorem pair_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (hd : depth.length = d)
    (regs : Fin 16 → Bool) :
    ∃ n rf, n ≤ 14000 * (d + 1)^2 + 1 ∧ rf 3 = IrreducibleSearch.pairPass c (a,b) ∧
      Eval checkPair n
      (wide (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        false false false source [] saved count extra)
      (wide (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf)
        false false false source [] saved count extra) := by
  obtain ⟨rf, hv, hr⟩ := pairProgram_run c a b depth hd regs
  have hrestrict : restrictState lowRegs lowStacks
      (wide (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        false false false source [] saved count extra) =
      pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs := by
    apply SubexpScanPrimitives.state_ext
    · funext i; simp [restrictState, wide, lowRegs]
    · funext i; simp [restrictState, wide, lowStacks]
  obtain ⟨n, hn, he⟩ := lifted_call pairProgram lowRegs lowStacks lowRegs_injective
    lowStacks_injective _ _ _ (by rw [hrestrict]; exact hr)
  exact ⟨n, rf, hn, hv, by simpa only [checkPair, embed_wide] using he⟩


private theorem unpack_eval (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (regs : Fin 16 → Bool) :
    Eval unpack (3 * (coefficientArray (as ++ bs)).length + 3)
      (wide (pairState [] [] cs depth [] [] [] regs)
        false true false source (coefficientArray (as ++ bs)).reverse saved count extra)
      (wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra) := by
  let before := wide (pairState [] [] cs depth [] [] [] regs)
    false true false source (coefficientArray (as ++ bs)).reverse saved count extra
  have he := Subexp.TupleProgram.transfer_eval (19 : Fin 24) 1 (16 : Fin 19) 17
    (by decide) (by decide) before
  have hend : (⟨readRegs before.regs 16 17 none,
      StackRoutines.transferStacks 19 1 before.stacks⟩ : Data) =
      wide (pairState [] (as ++ bs) cs depth [] [] [] regs)
        false false false source [] saved count extra := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [before, wide, pairState, readRegs]
    · funext i; fin_cases i <;>
        simp [before, wide, pairState, StackRoutines.transferStacks]
  rw [hend] at he
  simpa [unpack, before, wide, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using he

private theorem tail_eval (as bs cs : List IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (regs : Fin 16 → Bool) :
    Eval (.seq saveResult (.seq (clear 0) (.seq (clear 1) presentTrue)))
      (4 * as.length + 4 * bs.length + 8)
      (wide (pairState as bs cs depth [] [] [] regs)
        false false false source [] saved count extra)
      (wide (pairState [] [] cs depth [] [] [] regs)
        false true (regs 3) source [] saved count extra) := by
  let d0 := wide (pairState as bs cs depth [] [] [] regs)
    false false false source [] saved count extra
  let d1 := (StructuredProgram.Atom.copy (18 : Fin 19) 3).eval d0
  let d2 : Data := ⟨readRegs d1.regs 16 17 none, StackRoutines.clearStacks 0 d1.stacks⟩
  let d3 : Data := ⟨readRegs d2.regs 16 17 none, StackRoutines.clearStacks 1 d2.stacks⟩
  let d4 := (StructuredProgram.Atom.set (17 : Fin 19) true).eval d3
  have e1 : Eval saveResult 1 d0 d1 := .base (.atom _ _)
  have e2 := Subexp.TupleProgram.clear_eval (0 : Fin 24) (16 : Fin 19) 17 d1
  have e3 := Subexp.TupleProgram.clear_eval (1 : Fin 24) (16 : Fin 19) 17 d2
  have e4 : Eval presentTrue 1 d3 d4 := .base (.atom _ _)
  have he := e1.seq (e2.seq (e3.seq e4))
  have hend : d4 = wide (pairState [] [] cs depth [] [] [] regs)
      false true (regs 3) source [] saved count extra := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;>
        simp [d4, d3, d2, d1, d0, wide, pairState, readRegs,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    · funext i; fin_cases i <;>
        simp [d4, d3, d2, d1, d0, wide, pairState, StackRoutines.clearStacks,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  rw [hend] at he
  convert he using 1 ;
    simp [ d2, d1, d0, wide, pairState, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      coefficientArray_length] ; omega

theorem callback_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (hd : depth.length = d)
    (hc : count.length = d + 1) (regs : Fin 16 → Bool) :
    ∃ n rf, n ≤ 15000 * (d + 1)^2 ∧ Eval callback n
      (wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
        false true false source
        (coefficientArray (List.ofFn a ++ List.ofFn b)).reverse saved count extra)
      (wide (pairState [] [] (List.ofFn c) depth [] [] [] rf)
        false true (IrreducibleSearch.pairPass c (a,b)) source [] saved count extra) := by
  have e1 := unpack_eval (List.ofFn a) (List.ofFn b) (List.ofFn c)
    depth count source saved extra regs
  obtain ⟨m, r2, hm, e2⟩ := split_eval (List.ofFn a) (List.ofFn b) (List.ofFn c)
    depth count source saved extra (by simpa using hc) regs
  obtain ⟨n, r3, hn, hv, e3⟩ := pair_eval c a b depth count source saved extra hd r2
  have e4 := tail_eval (List.ofFn a) (List.ofFn b) (List.ofFn c)
    depth count source saved extra r3
  rw [hv] at e4
  refine ⟨_, r3, ?_, e1.seq (e2.seq (e3.seq e4))⟩
  simp only [coefficientArray_length, List.length_append, List.length_ofFn, hc] at *
  have hd : d ≤ (d + 1) ^ 2 := by nlinarith
  have hone : 1 ≤ (d + 1) ^ 2 := by nlinarith
  omega


theorem record_state_wide (low : State 16 18) (tag present found v pr f : Bool)
    (source payload saved count extra newSource newPayload : List Bool) :
    RecordPrograms.state ports (wide low tag present found source payload saved count extra)
      v pr f newSource newPayload = wide low v pr f newSource newPayload saved count extra := by
  apply SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, wide]
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, wide]

def Ready {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count saved extra : List Bool) (base : Data) : Prop :=
  ∃ regs tag present found source payload,
    base = wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
      tag present found source payload saved count extra

def pairEncode {d : ℕ}
    (ab : (Fin (d + 1) → IrreducibleSearch.F) × (Fin (d + 1) → IrreducibleSearch.F)) : List Bool :=
  coefficientArray (List.ofFn ab.1 ++ List.ofFn ab.2)

theorem pairEncode_injective (d : ℕ) : Function.Injective (pairEncode (d := d)) := by
  intro ab cd h
  apply SubexpTupleRefinement.encodePair_injective (SubexpEnumerationPayload.scalarCode 3)
    (d + 1) (d + 1)
  simpa only [pairEncode, coefficientArray_append, coefficientArray_ofFn] using h

/-- This observer labels executions on valid records. The program never calls
it: the preceding measured arithmetic proof establishes the label. -/
noncomputable def factorTest {d : ℕ} (c : Fin d → IrreducibleSearch.F) : List Bool → Bool :=
  Function.extend pairEncode (IrreducibleSearch.pairPass c) (fun _ => false)

theorem factorTest_encode {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (ab : (Fin (d + 1) → IrreducibleSearch.F) × (Fin (d + 1) → IrreducibleSearch.F)) :
    factorTest c (pairEncode ab) = IrreducibleSearch.pairPass c ab :=
  (pairEncode_injective d).extend_apply _ _ _

def factorRecords (d : ℕ) : List (List Bool) :=
  (IrreducibleSearch.factorPairs d).map pairEncode

theorem factorRecords_all {d : ℕ} (c : Fin d → IrreducibleSearch.F) :
    (factorRecords d).all (factorTest c) = IrreducibleSearch.passes c := by
  simp only [factorRecords, List.all_map, Function.comp_def, factorTest_encode,
    IrreducibleSearch.passes]

theorem callback_contract {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count saved extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1) :
    RecordPrograms.CallbackContractOn ports callback (factorTest c)
      (fun _ => 15000 * (d + 1)^2) (Ready c depth count saved extra)
      (fun bits => ∃ ab, pairEncode (d := d) ab = bits) := by
  intro bits tail base hb hbase
  obtain ⟨⟨a,b⟩, rfl⟩ := hb
  obtain ⟨regs, tag, present, found, source, payload, rfl⟩ := hbase
  obtain ⟨n, rf, hn, he⟩ := callback_eval c a b depth count tail saved extra hd hc regs
  let next := wide (pairState [] [] (List.ofFn c) depth [] [] [] rf)
    false true false [] [] saved count extra
  refine ⟨n, next, hn, ?_, ?_⟩
  · exact ⟨rf, false, true, false, [], [], rfl⟩
  · have hv : factorTest c (coefficientArray (List.ofFn a ++ List.ofFn b)) =
        IrreducibleSearch.pairPass c (a,b) := factorTest_encode c (a,b)
    simpa only [record_state_wide, next, pairEncode, hv] using he

def savedPorts : Subexp.BlockSearchProgram.SavedPorts 19 24 where
  toPorts := ports
  saved := 20
  temporary := 21
  saved_ne_source := by decide
  saved_ne_payload := by decide
  temporary_ne_source := by decide
  temporary_ne_payload := by decide
  saved_ne_temporary := by decide

abbrev savedAll : Cmd 19 24 := Subexp.BlockSearchProgram.savedAllCommand savedPorts callback
def savedProgram := compiled savedAll 20 13

def scanCost (d : ℕ) : ℕ :=
  9 * (ProgramEncoding.encodeRecords (factorRecords d)).length +
    RecordPrograms.budget (fun _ => 15000 * (d + 1)^2 + 2) (factorRecords d) + 14

theorem savedAll_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    ∃ n rf, n ≤ scanCost d ∧ Eval savedAll n
      (wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
        tag present found [] [] (ProgramEncoding.encodeRecords (factorRecords d)) count extra)
      (wide (pairState [] [] (List.ofFn c) depth [] [] [] rf)
        false true (IrreducibleSearch.passes c) [] []
        (ProgramEncoding.encodeRecords (factorRecords d)) count extra) := by
  let saved := ProgramEncoding.encodeRecords (factorRecords d)
  let base := wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
    tag present found [] [] saved count extra
  have hbase : Ready c depth count saved extra base :=
    ⟨regs, tag, present, found, [], [], rfl⟩
  have hr : ∀ bits ∈ factorRecords d, ∃ ab, pairEncode (d := d) ab = bits := by
    intro bits hb
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hb
    exact ⟨ab, rfl⟩
  obtain ⟨n, next, hn, hnext, he⟩ := Subexp.BlockSearchProgram.savedAllCommand_eval
    savedPorts callback (factorTest c) (fun _ => 15000 * (d + 1)^2)
    (Ready c depth count saved extra) (fun bits => ∃ ab, pairEncode (d := d) ab = bits)
    (callback_contract c depth count saved extra hd hc) (factorRecords d) base hr hbase
    (by simp [base, wide, savedPorts, saved]) (by simp [base, wide, savedPorts]) tag present found
  obtain ⟨rf, nt, np, nf, ns, no, rfl⟩ := hnext
  refine ⟨n, rf, hn, ?_⟩
  simpa only [savedAll, savedPorts, record_state_wide, factorRecords_all, base] using he

theorem savedProgram_runsIn {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    ∃ rf, RunsIn savedProgram (scanCost d + 1)
      ((wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
        tag present found [] [] (ProgramEncoding.encodeRecords (factorRecords d)) count extra).withPC
          (some savedProgram.entry))
      ((wide (pairState [] [] (List.ofFn c) depth [] [] [] rf)
        false true (IrreducibleSearch.passes c) [] []
        (ProgramEncoding.encodeRecords (factorRecords d)) count extra).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := savedAll_eval c depth count extra hd hc regs tag present found
  exact ⟨rf, n + 1, by omega, compiled_halt_trace he 20 13⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open IrreducibleSearchProgram

@[simp] theorem factorRecords_length (d : ℕ) :
    (factorRecords d).length = 3 ^ (2 * (d + 1)) := by
  simp [factorRecords]

theorem factorRecords_volume (d : ℕ) :
    ((factorRecords d).map List.length).sum =
      4 * (d + 1) * 3 ^ (2 * (d + 1)) := by
  have he : (fun ab : (Fin (d + 1) → IrreducibleSearch.F) ×
      (Fin (d + 1) → IrreducibleSearch.F) => (pairEncode ab).length) =
      (fun _ => 4 * (d + 1)) := by
    funext ab
    simp only [pairEncode, coefficientArray_length, List.length_append, List.length_ofFn]
    omega
  rw [factorRecords, List.map_map]
  change ((IrreducibleSearch.factorPairs d).map (fun ab => (pairEncode ab).length)).sum = _
  rw [he]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, IrreducibleSearch.length_factorPairs]
  ring

theorem scanCost_eq (d : ℕ) : scanCost d =
    (15000 * (d + 1)^2 + 96 * (d + 1) + 27) * 3 ^ (2 * (d + 1)) + 23 := by
  rw [scanCost, ProgramEncoding.encodeRecords_length, RecordPrograms.budget_eq,
    factorRecords_volume, factorRecords_length]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, factorRecords_length]
  ring

theorem scanCost_le (d : ℕ) : scanCost d ≤
    16000 * (d + 1)^2 * 3 ^ (2 * (d + 1)) + 23 := by
  rw [scanCost_eq]
  have hc : 15000 * (d + 1)^2 + 96 * (d + 1) + 27 ≤ 16000 * (d + 1)^2 := by
    nlinarith
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) 23

/-- The factor-list input to the universal scan is itself produced by the
same fixed ordered generator, at the supplied runtime depth `2(d+1)`. -/
theorem factorRecords_generated (d : ℕ) :
    ∃ next : StructuredProgram.State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords (factorRecords d) ∧
      next.stacks 8 = [] ∧
      BitProgram.RunsIn IrreducibleSearchEnumeration.program
        (IrreducibleSearchEnumeration.cost ((d + 1) + (d + 1)))
        ((IrreducibleSearchEnumeration.input ((d + 1) + (d + 1))).withPC
          (some IrreducibleSearchEnumeration.program.entry)) (next.withPC none) := by
  obtain ⟨next, hout, hd, hr⟩ :=
    IrreducibleSearchEnumeration.selected_runsIn ((d + 1) + (d + 1))
  refine ⟨next, ?_, hd, hr⟩
  rw [IrreducibleSearch.encoded_factorPairs] at hout
  have hencode : (pairEncode (d := d)) = (fun ab =>
      SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) ab.1 ++
      SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) ab.2) := by
    funext ab
    simp only [pairEncode, coefficientArray_append, coefficientArray_ofFn]
  simpa only [factorRecords, hencode] using hout

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

abbrev Data := State 22 28

def lowRegs (i : Fin 19) : Fin 22 := Fin.castAdd 3 i
def lowStacks (i : Fin 24) : Fin 28 := Fin.castAdd 4 i

theorem lowRegs_injective : Function.Injective lowRegs := Fin.castAdd_injective _ _
theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _

def ports : RecordPrograms.Ports 22 28 :=
  ⟨19,20,21,24,25,by decide,by decide,by decide,by decide⟩

def wide (low : State 19 24) (tag present found : Bool)
    (source payload extra : List Bool) : Data :=
  ⟨Fin.addCases (m := 19) (n := 3) (motive := fun _ => Bool) low.regs ![tag,present,found],
    Fin.addCases (m := 24) (n := 4) (motive := fun _ => List Bool)
      low.stacks ![source,payload,[],extra]⟩

def readyLow (cs : List IrreducibleSearch.F) (depth count : List Bool) (d : ℕ)
    (regs : Fin 16 → Bool) (tag present found : Bool) : State 19 24 :=
  IrreducibleSearchFactorControl.wide (pairState [] [] cs depth [] [] [] regs)
    tag present found [] []
    (ProgramEncoding.encodeRecords (IrreducibleSearchFactorControl.factorRecords d)) count []

theorem embed_wide (before after : State 19 24) (tag present found : Bool)
    (source payload extra : List Bool) :
    embedState lowRegs lowStacks (wide before tag present found source payload extra) after =
      wide after tag present found source payload extra := by
  apply SubexpScanPrimitives.embedState_eq lowRegs lowStacks lowRegs_injective lowStacks_injective
  · intro i; simp [wide, lowRegs]
  · intro i; simp [wide, lowStacks]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 19) (n := 3) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 24) (n := 4) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]

abbrev clearCandidate : Cmd 22 28 := .call (StackRoutines.clearProgram 13 19 20)
abbrev unpack : Cmd 22 28 := .call (StackRoutines.transferProgram 25 13 19 20)
abbrev checkCandidate : Cmd 22 28 := .call (ProgramLinking.liftProgram
  IrreducibleSearchFactorControl.savedProgram lowRegs lowStacks)
abbrev saveResult : Cmd 22 28 := .base (.atom (.copy 21 18))
abbrev presentTrue : Cmd 22 28 := .base (.atom (.set 20 true))
abbrev callback : Cmd 22 28 :=
  .seq (.seq clearCandidate unpack) (.seq checkCandidate (.seq saveResult presentTrue))
abbrev command : Cmd 22 28 := RecordPrograms.iterate ports callback
def program := compiled command 24 13

def candidateCost (d : ℕ) := IrreducibleSearchFactorControl.scanCost d + 20 * (d + 1) + 10

private theorem prepare_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (old : List IrreducibleSearch.F) (depth count source extra : List Bool)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    Eval (.seq clearCandidate unpack) (4 * old.length + 6 * d + 6)
      (wide (readyLow old depth count d regs tag present found)
        false true false source (coefficientArray (List.ofFn c)).reverse extra)
      (wide (readyLow (List.ofFn c) depth count d regs tag present found)
        false false false source [] extra) := by
  let d0 := wide (readyLow old depth count d regs tag present found)
    false true false source (coefficientArray (List.ofFn c)).reverse extra
  let d1 : Data := ⟨readRegs d0.regs 19 20 none, StackRoutines.clearStacks 13 d0.stacks⟩
  let d2 : Data := ⟨readRegs d1.regs 19 20 none, StackRoutines.transferStacks 25 13 d1.stacks⟩
  have e1 := Subexp.TupleProgram.clear_eval (13 : Fin 28) (19 : Fin 22) 20 d0
  have e2 := Subexp.TupleProgram.transfer_eval (25 : Fin 28) 13 (19 : Fin 22) 20
    (by decide) (by decide) d1
  have he := e1.seq e2
  have hend : d2 = wide (readyLow (List.ofFn c) depth count d regs tag present found)
      false false false source [] extra := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;>
        simp [d2, d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide,
          pairState, readRegs]
    · funext i; fin_cases i <;>
        simp [d2, d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide,
          pairState, StackRoutines.clearStacks, StackRoutines.transferStacks]
  change Eval (.seq clearCandidate unpack) _ d0 d2 at he
  rw [hend] at he
  convert he using 1 ;
    simp [d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide, pairState,
      StackRoutines.clearStacks, coefficientArray_length] ; omega

private theorem check_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count source extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    ∃ n rf, n ≤ IrreducibleSearchFactorControl.scanCost d + 1 ∧ Eval checkCandidate n
      (wide (readyLow (List.ofFn c) depth count d regs tag present found)
        false false false source [] extra)
      (wide (readyLow (List.ofFn c) depth count d rf false true (IrreducibleSearch.passes c))
        false false false source [] extra) := by
  obtain ⟨rf, hr⟩ := IrreducibleSearchFactorControl.savedProgram_runsIn
    c depth count [] hd hc regs tag present found
  have hrestrict : restrictState lowRegs lowStacks
      (wide (readyLow (List.ofFn c) depth count d regs tag present found)
        false false false source [] extra) = readyLow (List.ofFn c) depth count d regs tag present found := by
    apply SubexpScanPrimitives.state_ext
    · funext i; simp [restrictState, wide, lowRegs]
    · funext i; simp [restrictState, wide, lowStacks]
  obtain ⟨n, hn, he⟩ := lifted_call IrreducibleSearchFactorControl.savedProgram
    lowRegs lowStacks lowRegs_injective lowStacks_injective _ _ _
    (by rw [hrestrict]; exact hr)
  exact ⟨n, rf, hn, by simpa only [checkCandidate, embed_wide, readyLow] using he⟩

private theorem finish_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count source extra : List Bool) (regs : Fin 16 → Bool) :
    Eval (.seq saveResult presentTrue) 2
      (wide (readyLow (List.ofFn c) depth count d regs false true (IrreducibleSearch.passes c))
        false false false source [] extra)
      (wide (readyLow (List.ofFn c) depth count d regs false true (IrreducibleSearch.passes c))
        false true (IrreducibleSearch.passes c) source [] extra) := by
  let d0 := wide (readyLow (List.ofFn c) depth count d regs false true (IrreducibleSearch.passes c))
    false false false source [] extra
  let d1 := (StructuredProgram.Atom.copy (21 : Fin 22) 18).eval d0
  let d2 := (StructuredProgram.Atom.set (20 : Fin 22) true).eval d1
  have e1 : Eval saveResult 1 d0 d1 := .base (.atom _ _)
  have e2 : Eval presentTrue 1 d1 d2 := .base (.atom _ _)
  have he := e1.seq e2
  convert he using 1
  apply SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;>
      simp [d2, d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  · funext i; fin_cases i <;>
      simp [d2, d1, d0, wide, readyLow, IrreducibleSearchFactorControl.wide,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]

theorem callback_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (old : List IrreducibleSearch.F) (hold : old.length ≤ d)
    (depth count source extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    ∃ n rf, n ≤ candidateCost d ∧ Eval callback n
      (wide (readyLow old depth count d regs tag present found)
        false true false source (coefficientArray (List.ofFn c)).reverse extra)
      (wide (readyLow (List.ofFn c) depth count d rf false true (IrreducibleSearch.passes c))
        false true (IrreducibleSearch.passes c) source [] extra) := by
  have ep := prepare_eval c old depth count source extra regs tag present found
  obtain ⟨n, rf, hn, ec⟩ := check_eval c depth count source extra hd hc regs tag present found
  have ef := finish_eval c depth count source extra rf
  exact ⟨_, rf, by dsimp [candidateCost]; omega, ep.seq (ec.seq ef)⟩


theorem record_state_wide (low : State 19 24) (tag present found v pr f : Bool)
    (source payload extra newSource newPayload : List Bool) :
    RecordPrograms.state ports (wide low tag present found source payload extra)
      v pr f newSource newPayload = wide low v pr f newSource newPayload extra := by
  apply SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, wide]
  · funext i; fin_cases i <;> simp [RecordPrograms.state, ports, wide]

def Ready (d : ℕ) (depth count extra : List Bool) (base : Data) : Prop :=
  ∃ old : List IrreducibleSearch.F, old.length ≤ d ∧
    ∃ regs it ip iff ot op ofd source payload,
      base = wide (readyLow old depth count d regs it ip iff) ot op ofd source payload extra

theorem Ready.record_state {d : ℕ} {depth count extra : List Bool} {base : Data}
    (h : Ready d depth count extra base) (v pr f : Bool) (source payload : List Bool) :
    Ready d depth count extra (RecordPrograms.state ports base v pr f source payload) := by
  obtain ⟨old, hold, regs, it, ip, found, ot, op, ofd, src, out, rfl⟩ := h
  rw [record_state_wide]
  exact ⟨old, hold, regs, it, ip, found, v, pr, f, source, payload, rfl⟩

theorem Ready.controls {d : ℕ} {depth count extra : List Bool} {base : Data}
    (h : Ready d depth count extra base) :
    base.stacks 14 = depth ∧ base.stacks 22 = count ∧ base.stacks 27 = extra := by
  obtain ⟨old, hold, regs, it, ip, found, ot, op, ofd, source, payload, rfl⟩ := h
  simp [wide, readyLow, IrreducibleSearchFactorControl.wide, pairState]

theorem Ready.scratch {d : ℕ} {depth count extra : List Bool} {base : Data}
    (h : Ready d depth count extra base) :
    base.stacks 15 = [] ∧ base.stacks 21 = [] ∧ base.stacks 23 = [] ∧ base.stacks 26 = [] := by
  obtain ⟨old, hold, regs, it, ip, found, ot, op, ofd, source, payload, rfl⟩ := h
  simp [wide, readyLow, IrreducibleSearchFactorControl.wide, pairState]

/-- A mathematical observer for the proof; every executed test is the concrete
factor-scan callback above. -/
noncomputable def candidateTest (d : ℕ) : List Bool → Bool :=
  Function.extend (encodeTuple (scalarCode 3) : (Fin d → IrreducibleSearch.F) → List Bool)
    IrreducibleSearch.passes (fun _ => false)

theorem candidateTest_encode {d : ℕ} (c : Fin d → IrreducibleSearch.F) :
    candidateTest d (encodeTuple (scalarCode 3) c) = IrreducibleSearch.passes c :=
  (encodeTuple_injective (scalarCode 3) d).extend_apply _ _ _

def candidateRecords (d : ℕ) :=
  (IrreducibleSearch.candidates d).map (encodeTuple (scalarCode 3))

theorem callback_contract (d : ℕ) (depth count extra : List Bool)
    (hd : depth.length = d) (hc : count.length = d + 1) :
    RecordPrograms.CallbackContractWithOn ports callback (candidateTest d)
      (fun _ => candidateCost d) (Ready d depth count extra)
      (fun bits _ next => next.stacks 13 = bits)
      (fun bits => ∃ c : Fin d → IrreducibleSearch.F, encodeTuple (scalarCode 3) c = bits) := by
  intro bits tail base hb hbase
  obtain ⟨c, rfl⟩ := hb
  obtain ⟨old, hold, regs, it, ip, iff, ot, op, ofd, source, payload, rfl⟩ := hbase
  obtain ⟨n, rf, hn, he⟩ := callback_eval c old hold depth count tail extra hd hc regs it ip iff
  let next := wide (readyLow (List.ofFn c) depth count d rf false true (IrreducibleSearch.passes c))
    false true (IrreducibleSearch.passes c) [] [] extra
  refine ⟨n, next, hn, ?_, ?_, ?_⟩
  · exact ⟨List.ofFn c, by simp, rf, false, true, IrreducibleSearch.passes c,
      false, true, IrreducibleSearch.passes c, [], [], rfl⟩
  · simp [next, wide, readyLow, IrreducibleSearchFactorControl.wide, pairState,
      coefficientArray_ofFn]
  · simpa only [record_state_wide, next, coefficientArray_ofFn, candidateTest_encode] using he

def input (d : ℕ) (depth count extra : List Bool) : Data :=
  wide (readyLow [] depth count d (fun _ => false) false false false)
    false false false (ProgramEncoding.encodeRecords (candidateRecords d)) [] extra

def searchCost (d : ℕ) := 4 + RecordPrograms.budget (fun _ => candidateCost d) (candidateRecords d)

theorem program_runsIn_ready {d : ℕ} (hd : 0 < d) (depth count extra : List Bool)
    (hdepth : depth.length = d) (hcount : count.length = d + 1) :
    ∃ final : Data, final.stacks 13 = encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients d) ∧
      Ready d depth count extra final ∧ final.stacks 25 = [] ∧ RunsIn program (searchCost d)
        ((input d depth count extra).withPC (some program.entry)) (final.withPC none) := by
  let base := wide (readyLow [] depth count d (fun _ => false) false false false)
    false false false [] [] extra
  have hb : Ready d depth count extra base :=
    ⟨[], by simp, (fun _ => false), false, false, false, false, false, false, [], [], rfl⟩
  obtain ⟨n, next, hn, hnext, hout, he⟩ := IrreducibleSearch.encoded_searchCommand_eval hd
    ports callback 13 (candidateTest d) (fun _ => candidateCost d) (Ready d depth count extra)
    (fun bits => ∃ c : Fin d → IrreducibleSearch.F, encodeTuple (scalarCode 3) c = bits)
    (callback_contract d depth count extra hdepth hcount) candidateTest_encode [] base
    (fun c => ⟨c, rfl⟩) hb false false false
  let final := RecordPrograms.state ports next false true true
    (RecordPrograms.unread (candidateTest d) (candidateRecords d) []) []
  have he' : Eval command n (input d depth count extra) final := by
    simpa only [command, Subexp.BlockSearchProgram.anyCommand, base, record_state_wide,
      List.append_nil, input, final, candidateRecords] using he
  refine ⟨final, ?_, ?_, ?_, n + 1, by dsimp [searchCost, candidateRecords]; omega, ?_⟩
  · simpa [final, RecordPrograms.state, ports] using hout
  · exact hnext.record_state false true true _ _
  · simp [final, RecordPrograms.state, ports]
  · exact compiled_halt_trace he' 24 13

theorem program_runsIn {d : ℕ} (hd : 0 < d) (depth count extra : List Bool)
    (hdepth : depth.length = d) (hcount : count.length = d + 1) :
    ∃ final : Data, final.stacks 13 = encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients d) ∧
      RunsIn program (searchCost d)
        ((input d depth count extra).withPC (some program.entry)) (final.withPC none) := by
  obtain ⟨final, hout, _, _, hr⟩ := program_runsIn_ready hd depth count extra hdepth hcount
  exact ⟨final, hout, hr⟩

theorem program_runsIn_controls {d : ℕ} (hd : 0 < d) (depth count extra : List Bool)
    (hdepth : depth.length = d) (hcount : count.length = d + 1) :
    ∃ final : Data, final.stacks 13 = encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients d) ∧
      final.stacks 14 = depth ∧ final.stacks 22 = count ∧ final.stacks 27 = extra ∧
      RunsIn program (searchCost d)
        ((input d depth count extra).withPC (some program.entry)) (final.withPC none) := by
  obtain ⟨final, hout, hready, _, hr⟩ := program_runsIn_ready hd depth count extra hdepth hcount
  obtain ⟨hdepth', hcount', hextra'⟩ := hready.controls
  exact ⟨final, hout, hdepth', hcount', hextra', hr⟩

theorem program_primitive {d : ℕ} (hd : 0 < d) (depth count extra : List Bool)
    (hdepth : depth.length = d) (hcount : count.length = d + 1) :
    ∃ final : Data, final.stacks 13 = encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients d) ∧
      Computation.RunsIn (primitive program).step (primitiveOverhead program * searchCost d)
        (primitiveCfg program ((input d depth count extra).withPC (some program.entry)))
        (primitiveCfg program (final.withPC none)) := by
  obtain ⟨final, hout, hr⟩ := program_runsIn hd depth count extra hdepth hcount
  exact ⟨final, hout, primitive_execution program hr⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

@[simp] theorem candidateRecords_length (d : ℕ) :
    (candidateRecords d).length = 3 ^ d := by simp [candidateRecords]

theorem candidateRecords_volume (d : ℕ) :
    ((candidateRecords d).map List.length).sum = 2 * d * 3 ^ d := by
  have he : (fun c : Fin d → IrreducibleSearch.F =>
      (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) c).length) =
      (fun _ => 2 * d) := by
    funext c
    rw [← IrreducibleSearchProgram.coefficientArray_ofFn]
    simp only [IrreducibleSearchProgram.coefficientArray_length, List.length_ofFn]
  rw [candidateRecords, List.map_map]
  change ((IrreducibleSearch.candidates d).map (fun c =>
    (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) c).length)).sum = _
  rw [he]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, IrreducibleSearch.length_candidates]
  ring

theorem searchCost_eq (d : ℕ) : searchCost d = (candidateCost d + 12 * d + 7) * 3 ^ d + 4 := by
  rw [searchCost, RecordPrograms.budget_eq, candidateRecords_volume, candidateRecords_length]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, candidateRecords_length]
  ring

theorem searchCost_le (d : ℕ) : searchCost d ≤
    17000 * (d + 1)^2 * 3 ^ (3 * d + 2) + 4 := by
  have hscan := IrreducibleSearchFactorControl.scanCost_le d
  have hp : 1 ≤ 3 ^ (2 * (d + 1)) := Nat.one_le_pow _ _ (by decide)
  have hl : 32 * d + 60 ≤ 1000 * (d + 1)^2 := by nlinarith
  have hl' : 32 * d + 60 ≤ 1000 * (d + 1)^2 * 3 ^ (2 * (d + 1)) :=
    hl.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hc : candidateCost d + 12 * d + 7 ≤
      17000 * (d + 1)^2 * 3 ^ (2 * (d + 1)) := by
    dsimp [candidateCost]
    nlinarith
  rw [searchCost_eq]
  calc
    _ ≤ (17000 * (d + 1)^2 * 3 ^ (2 * (d + 1))) * 3 ^ d + 4 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) 4
    _ = _ := by
      rw [mul_assoc (17000 * (d + 1)^2), ← pow_add,
        show 2 * (d + 1) + d = 3 * d + 2 by omega]

theorem searchCost_exponential (d : ℕ) : searchCost d ≤ 3 ^ (5 * d + 12) := by
  have hs := Nat.pow_le_pow_left (IrreducibleSearch.succ_le_three_pow d) 2
  have hp : 1 ≤ 3 ^ (5 * d + 2) := Nat.one_le_pow _ _ (by decide)
  calc
    searchCost d ≤ 17000 * (d + 1)^2 * 3 ^ (3 * d + 2) + 4 := searchCost_le d
    _ ≤ 17000 * (3 ^ d)^2 * 3 ^ (3 * d + 2) + 4 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 17000 hs)) 4
    _ = 17000 * 3 ^ (5 * d + 2) + 4 := by
      rw [← pow_mul, mul_assoc, ← pow_add,
        show d * 2 + (3 * d + 2) = 5 * d + 2 by omega]
    _ ≤ 59049 * 3 ^ (5 * d + 2) := by omega
    _ = 3 ^ (5 * d + 12) := by
      have h : (59049 : ℕ) = 3 ^ 10 := by norm_num
      rw [h, ← pow_add, show 10 + (5 * d + 2) = 5 * d + 12 by omega]

theorem searchCost_cardinality (d : ℕ) :
    searchCost d ≤ 531441 * (3 ^ d)^5 := by
  calc
    searchCost d ≤ 3 ^ (5 * d + 12) := searchCost_exponential d
    _ = 531441 * (3 ^ d)^5 := by
      rw [pow_add, Nat.mul_comm 5 d, pow_mul]
      norm_num [Nat.mul_comm]

/-- Ancillary estimate under a stronger field-size premise. The implemented
`Nat.size Q + 1` degree uses `searchCost_sizeDegreeBound` below. -/
theorem searchCost_nodeBound {d Q : ℕ} (h : 3 ^ d ≤ 3 * (Q + 1)) :
    searchCost d ≤ 129140163 * (Q + 1)^5 := by
  calc
    searchCost d ≤ 531441 * (3 ^ d)^5 := searchCost_cardinality d
    _ ≤ 531441 * (3 * (Q + 1))^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 5)
    _ = 129140163 * (Q + 1)^5 := by ring

/-- The implemented degree is `Nat.size Q + 1`; its proved field-size bound
is quadratic in `Q + 1`, giving degree ten for the search. -/
theorem searchCost_sizeDegreeBound {d Q : ℕ} (h : 3 ^ d ≤ 16 * (Q + 1)^2) :
    searchCost d ≤ (531441 * 16^5) * (Q + 1)^10 := by
  calc
    searchCost d ≤ 531441 * (3 ^ d)^5 := searchCost_cardinality d
    _ ≤ 531441 * (16 * (Q + 1)^2)^5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 5)
    _ = (531441 * 16^5) * (Q + 1)^10 := by ring

/-- The translation overhead is one fixed constant, because the program has
no dimension-dependent code. All dimension data live on input stacks. -/
noncomputable def primitiveCost (d : ℕ) : ℕ := BitProgram.primitiveOverhead program * searchCost d

theorem primitiveCost_cardinality (d : ℕ) :
    primitiveCost d ≤ (BitProgram.primitiveOverhead program * 531441) * (3 ^ d)^5 := by
  unfold primitiveCost
  calc
    _ ≤ BitProgram.primitiveOverhead program * (531441 * (3 ^ d)^5) :=
      Nat.mul_le_mul_left _ (searchCost_cardinality d)
    _ = _ := by ring

theorem primitiveCost_sizeDegreeBound {d Q : ℕ} (h : 3 ^ d ≤ 16 * (Q + 1)^2) :
    primitiveCost d ≤
      (BitProgram.primitiveOverhead program * (531441 * 16^5)) * (Q + 1)^10 := by
  unfold primitiveCost
  calc
    _ ≤ BitProgram.primitiveOverhead program * ((531441 * 16^5) * (Q + 1)^10) :=
      Nat.mul_le_mul_left _ (searchCost_sizeDegreeBound h)
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
