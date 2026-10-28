import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedCleanup

/-! Concrete return from a completed marked high-assignment count. All fresh
query workspace is reclaimed, the complete count is moved to323, and the
collector parser registers are reset after cleanup. The compact boundary cap
is distinct from the transient query cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn

open BitProgram StructuredCalls RecordPrograms SqrtLog
open HashMarkedQueryAdapter
open HashGreedyProgram.NativeRound

private opaque upperPortsWrapped :
    {ports : List (Fin 896) //
      ports = (List.finRange 896).filter (fun i => decide (832 ≤ i.val ∧ i.val < 895))} :=
  ⟨(List.finRange 896).filter (fun i => decide (832 ≤ i.val ∧ i.val < 895)), rfl⟩

/-- This fixed range is the query-owned upper bank in the shared ABI. It is
opaque so unrelated proofs do not reduce the full finite instruction table. -/
def upperPorts : List (Fin 896) := upperPortsWrapped.1

theorem upperPorts_eq :
    upperPorts =
      (List.finRange 896).filter (fun i => decide (832 ≤ i.val ∧ i.val < 895)) :=
  upperPortsWrapped.2

@[simp] theorem mem_upperPorts (i : Fin 896) :
    i ∈ upperPorts ↔ 832 ≤ i.val ∧ i.val < 895 := by
  rw [upperPorts_eq]
  simp

theorem upperPorts_nodup : upperPorts.Nodup :=
  upperPorts_eq.symm ▸ (List.nodup_finRange 896).filter _

theorem upperPorts_length_le : upperPorts.length ≤ 896 := by
  rw [upperPorts_eq]
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := 896))

def upperClear : Code := BankRoutines.clearCmd 767 0 1 upperPorts
def upperCleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks upperPorts a.stacks⟩
def upperCost (a : Data) : ℕ :=
  2*(upperPorts.map (fun i => (a.stacks i).length)).sum+3*upperPorts.length+3

def command : Code := .seq finish
  (.seq HighMarkedFrontend.cleanupCommand (.seq upperClear resetParser))
noncomputable def result (a : Data) : Data :=
  parserReset (upperCleared (HighMarkedFrontend.cleaned (finishState a)))
noncomputable def cost (a : Data) : ℕ := finishSteps a+
  (LeafProgram.Query.cleanupCost (HighMarkedFrontend.project (finishState a))+1+
    (upperCost (HighMarkedFrontend.cleaned (finishState a))+3))

/-- Kept words are exactly the collector sources, immutable lower sources,
and selector/caller words outside the high-counter and query banks. -/
def kept (i : Fin 896) : Bool := decide
  (i=320 ∨ i=322 ∨ i=700 ∨ i=701 ∨ i=707 ∨ i=708 ∨ i=709 ∨
    (744 ≤ i.val ∧ i.val < 788) ∨ (795 ≤ i.val ∧ i.val < 832) ∨ i=895)

theorem lower_eval (a : Data) : Eval HighMarkedFrontend.cleanupCommand
    (LeafProgram.Query.cleanupCost (HighMarkedFrontend.project a)+1) a
    (HighMarkedFrontend.cleaned a) := by
  exact eval_call_from_state HighMarkedFrontend.cleanupLocalProgram id HighMarkedFrontend.stackMap a
    Function.injective_id (Fin.castAdd_injective _ _)
    (compiled_halt_trace (LeafProgram.Query.cleanup_eval (HighMarkedFrontend.project a)) 699 323)

theorem upper_eval (a : Data) (ht : a.stacks 767=[]) :
    Eval upperClear (upperCost a) a (upperCleared a) := by
  simpa only [upperClear,upperCost,upperCleared] using BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 upperPorts upperPorts_nodup
    a.regs a.stacks ht

theorem reset_eval (a : Data) : Eval resetParser 3 a (parserReset a) :=
  Eval.base (SubexpParameterProgram.atoms_eval
    [.set (16 : Fin 40) false,.set 17 true,.set 18 false] a)

theorem eval (a : Data) (ht : a.stacks 767=[]) : Eval command (cost a) a (result a) := by
  have hfinish := finish_eval a ht
  have hlower := lower_eval (finishState a)
  have hscratch : (HighMarkedFrontend.cleaned (finishState a)).stacks 767=[] := by
    rw [show (767 : Fin 896)=HighMarkedFrontend.stackMap 767 from rfl,
      HighMarkedFrontend.cleaned_lower]
    simp [LeafProgram.Query.Protected,finishState_stacks,BankRoutines.clearBankStacks,
      cleanupPorts,ht,HighMarkedFrontend.stackMap]
  exact hfinish.seq (hlower.seq ((upper_eval _ hscratch).seq (reset_eval _)))

/-- Every erased port has an actual clear operation. The single returned word
is the complete high-assignment count, with no Boolean or low-bit conversion. -/
private theorem parserReset_stacks (a : Data) : (parserReset a).stacks=a.stacks := rfl

private theorem kept_lower (j : Fin 768) :
    kept (HighMarkedFrontend.stackMap j)=decide (LeafProgram.Query.Protected j ∧ j≠323) := by
  unfold kept
  rw [decide_eq_decide]
  have hj := j.isLt
  simp only [LeafProgram.Query.Protected,HighMarkedFrontend.stackMap,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Fin.castAdd, Fin.val_castLE]
  norm_num only [Nat.reduceMod,Nat.reduceAdd]
  omega

private theorem protected_not_finish (j : Fin 768) (hp : LeafProgram.Query.Protected j) :
    HighMarkedFrontend.stackMap j ∉ cleanupPorts := by
  have hj := j.isLt
  simp only [LeafProgram.Query.Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hp
  simp only [cleanupPorts, List.mem_cons, List.not_mem_nil, or_false,
    HighMarkedFrontend.stackMap, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.castAdd,
    Fin.val_castLE]
  norm_num only [Nat.reduceMod,Nat.reduceAdd] at hp ⊢
  omega

theorem result_stacks (a : Data) (i : Fin 896) :
    (result a).stacks i = if i=323 then a.stacks 788 else if kept i then a.stacks i else [] := by
  rw [result,parserReset_stacks]
  simp only [upperCleared]
  by_cases hu : i ∈ upperPorts
  · have hv := mem_upperPorts i |>.mp hu
    have hnot : i ≠ 323 := by intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hv
    have hk : kept i=false := by
      simp only [kept,decide_eq_false_iff_not,Fin.ext_iff]
      omega
    simp [BankRoutines.clearBankStacks,hu,hnot,hk]
  · rw [BankRoutines.clearBankStacks_frame i upperPorts _ hu]
    by_cases hl : i.val < 768
    · let j : Fin 768 := ⟨i.val,hl⟩
      have hij : i=HighMarkedFrontend.stackMap j := rfl
      have heq : HighMarkedFrontend.stackMap j=323 ↔ j=323 := by
        simp only [HighMarkedFrontend.stackMap,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
          Fin.castAdd, Fin.val_castLE]
      rw [hij,HighMarkedFrontend.cleaned_lower,kept_lower]
      by_cases hp : LeafProgram.Query.Protected j
      · rw [ite_eq_left hp, finishState_stacks,
          BankRoutines.clearBankStacks_frame _ _ _ (protected_not_finish j hp)]
        by_cases hj : j=323
        · rw [hj]
          simp [HighMarkedFrontend.stackMap]
        · have hn : HighMarkedFrontend.stackMap j≠323 := heq.not.mpr hj
          simp [hp,hj,hn]
      · have hj : j≠323 := by intro h; apply hp; rw [h]; decide
        have hn : HighMarkedFrontend.stackMap j≠323 := heq.not.mpr hj
        simp [hp,hj,hn]
    · rw [HighMarkedFrontend.cleaned_upper _ i (by omega),finishState_stacks]
      have hv : ¬(832 ≤ i.val ∧ i.val < 895) := (mem_upperPorts i).not.mp hu
      simp only [BankRoutines.clearBankStacks, cleanupPorts, List.mem_cons,
        List.not_mem_nil, or_false, Function.update_apply, kept, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega

@[simp] theorem result_count (a : Data) : (result a).stacks 323=a.stacks 788 := by
  simp [result_stacks]

theorem result_parser (a : Data) : (result a).regs 16=false ∧ (result a).regs 17=true ∧
    (result a).regs 18=false := by
  simp [result,parserReset,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, execInstr, StructuredProgram.State.ofCfg]

/-- The returned boundary depends on retained words and the count length only;
large discarded query temporaries do not become the next query's input cap. -/
theorem result_bound (a : Data) (B : ℕ)
    (hkept : ∀ i, kept i=true → (a.stacks i).length≤B)
    (hcount : (a.stacks 788).length≤B) : ∀ i, ((result a).stacks i).length≤B := by
  intro i
  rw [result_stacks]
  split_ifs with hcountPort hkeep
  · exact hcount
  · exact hkept i hkeep
  · simp

private theorem finish_bound (a : Data) (D : ℕ) (hD : ∀ i, (a.stacks i).length≤D) :
    ∀ i, ((finishState a).stacks i).length≤D := by
  intro i
  rw [finishState_stacks]
  by_cases hc : i∈cleanupPorts
  · simp [BankRoutines.clearBankStacks,hc]
  · simp only [BankRoutines.clearBankStacks, ite_eq_right hc]
    by_cases hi : i=323
    · subst i; simpa using hD 788
    · simpa [hi] using hD i

private theorem lower_bound (a : Data) (D : ℕ) (hD : ∀ i, (a.stacks i).length≤D) :
    ∀ i, ((HighMarkedFrontend.cleaned a).stacks i).length≤D := by
  intro i
  by_cases hi : i.val<768
  · let j : Fin 768 := ⟨i.val,hi⟩
    have hij : i=HighMarkedFrontend.stackMap j := rfl
    rw [hij,HighMarkedFrontend.cleaned_lower]
    split_ifs
    · exact hD _
    · simp
  · rw [HighMarkedFrontend.cleaned_upper _ i (by omega)]
    exact hD i

private theorem upper_bound (a : Data) (D : ℕ) (hD : ∀ i, (a.stacks i).length≤D) :
    ∀ i, ((upperCleared a).stacks i).length≤D := by
  intro i
  by_cases hi : i∈upperPorts
  · simp [upperCleared,BankRoutines.clearBankStacks,hi]
  · simpa [upperCleared,BankRoutines.clearBankStacks,hi] using hD i

private theorem lower_scratch (a : Data) (ht : a.stacks 767=[]) :
    (HighMarkedFrontend.cleaned (finishState a)).stacks 767=[] := by
  rw [show (767 : Fin 896)=HighMarkedFrontend.stackMap 767 from rfl,
    HighMarkedFrontend.cleaned_lower]
  simp [LeafProgram.Query.Protected,finishState_stacks,BankRoutines.clearBankStacks,
    cleanupPorts,ht,HighMarkedFrontend.stackMap]

theorem upperCost_le (a : Data) (D : ℕ) (hD : ∀ i, (a.stacks i).length≤D) :
    upperCost a≤1792*D+2691 := by
  have hlen : upperPorts.length ≤ 896 := upperPorts_length_le
  have hsum : (upperPorts.map (fun i => (a.stacks i).length)).sum≤upperPorts.length*D := by
    have h := List.sum_le_length_nsmul
      (upperPorts.map (fun i => (a.stacks i).length)) D
      (by intro x hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact hD i)
    simpa using h
  have hprod := Nat.mul_le_mul_right D hlen
  unfold upperCost
  omega

/-- Only linear cleanup and fixed-bank scanning are charged here. -/
theorem cost_le (a : Data) (D : ℕ) (hD : ∀ i, (a.stacks i).length≤D) :
    cost a+1≤3400*D+5100 := by
  have hf := finish_steps_le a D hD
  have hl := (HighMarkedFrontend.cleanup_trace_space (finishState a) D (finish_bound a D hD)).2.1
  have hu := upperCost_le (HighMarkedFrontend.cleaned (finishState a)) D
    (lower_bound _ D (finish_bound a D hD))
  unfold cost
  omega

private theorem reset_space (a : Data) (D : ℕ) (hD : ∀ i, (a.stacks i).length≤D) :
    StageSpace resetParser 3 a (931*D+54) := by
  constructor
  intro k z hk hz i
  have hstart : dataBits (a.withPC (some (compiled resetParser 778 777).entry))≤896*D :=
    StreamResources.dataBits_le_mul _ hD
  have h := StructuredSpace.local_stack_bound (compiled resetParser 778 777)
    hstart k z hk hz i
  omega

/-- Every actual suffix prefix has a fixed polynomial cap independent of the
query runtime. The result_bound theorem supplies its separate compact boundary. -/
theorem trace_space (a : Data) (D : ℕ) (hD : ∀ i, (a.stacks i).length≤D)
    (ht : a.stacks 767=[]) :
    Trace (compiled command 778 777) (cost a+1)
      (a.withPC (some (compiled command 778 777).entry)) ((result a).withPC none) ∧
    cost a+1≤3400*D+5100 ∧
    StageSpace command (cost a+1) a (931*D+54) := by
  have hf := finish_eval a ht
  have hl := lower_eval (finishState a)
  have hu := upper_eval (HighMarkedFrontend.cleaned (finishState a)) (lower_scratch a ht)
  have hr := reset_eval (upperCleared (HighMarkedFrontend.cleaned (finishState a)))
  have hfinish : StageSpace finish (finishSteps a) a (931*D+54) := by
    constructor
    intro k z hk hz i
    exact (finish_trace_space a D hD ht).2 k z (by omega) hz i
  have hD1 := finish_bound a D hD
  have hD2 := lower_bound _ D hD1
  have hD3 := upper_bound _ D hD2
  have hlower : StageSpace HighMarkedFrontend.cleanupCommand
      (LeafProgram.Query.cleanupCost (HighMarkedFrontend.project (finishState a))+1)
      (finishState a) (931*D+54) := by
    constructor
    intro k z hk hz i
    have h := (HighMarkedFrontend.cleanup_trace_space (finishState a) D hD1).2.2
      k z (by omega) hz i
    omega
  have hupper : StageSpace upperClear (upperCost (HighMarkedFrontend.cleaned (finishState a)))
      (HighMarkedFrontend.cleaned (finishState a)) (931*D+54) := by
    constructor
    intro k z hk hz i
    have h := HighQuerySpace.clear_bank_bound (767 : Fin 896) (0 : Fin 40) 1
      upperPorts upperPorts_nodup (HighMarkedFrontend.cleaned (finishState a))
      (lower_scratch a ht) D hD2 778 777 k z hk hz i
    omega
  have hreset := reset_space (upperCleared (HighMarkedFrontend.cleaned (finishState a))) D hD3
  have hfull := hf.seq (hl.seq (hu.seq hr))
  have hp := StageSpace.seq hf (hl.seq (hu.seq hr)) hfinish
    (StageSpace.seq hl (hu.seq hr) hlower (StageSpace.seq hu hr hupper hreset))
  exact ⟨compiled_halt_trace hfull 778 777,cost_le a D hD,
    ⟨StructuredSpace.compiled_halt_stack_bound hfull 778 777 hp.bound⟩⟩

@[simp] theorem result_collector_source (a : Data) : (result a).stacks 320=a.stacks 320 := by
  simp [result_stacks,kept,Fin.coe_ofNat_eq_mod]

@[simp] theorem result_accumulator (a : Data) : (result a).stacks 322=a.stacks 322 := by
  simp [result_stacks,kept,Fin.coe_ofNat_eq_mod]

@[simp] theorem result_payload (a : Data) : (result a).stacks 321=[] := by
  simp [result_stacks,kept,Fin.coe_ofNat_eq_mod]

@[simp] theorem result_add_scratch (a : Data) : (result a).stacks 324=[] := by
  simp [result_stacks,kept,Fin.coe_ofNat_eq_mod]

/-- Exact parser-state presentation required by the measured marked collector. -/
theorem result_record (a : Data) :
    RecordPrograms.state HashMassAdapter.recordPorts (result a) false true false
      (a.stacks 320) [] = result a := by
  have hp := result_parser a
  exact RecordPrograms.state_eq_self HashMassAdapter.recordPorts (result a)
    false true false (a.stacks 320) [] hp.1 hp.2.1 hp.2.2
    (result_collector_source a) (result_payload a)

/-- Restores the entire 891-word callback workspace from the concrete retained
frame and the previously blank discarded banks. The five collector words are
handled separately by result_count and the collector-frame lemmas above. -/
theorem workspace_restore (entry a : Data)
    (hframe : ∀ i, kept i=true → a.stacks i=entry.stacks i)
    (hblank : ∀ i, kept i=false → (i.val < 320 ∨ 324 < i.val) → entry.stacks i=[]) :
    HashMassAdapter.workspace (result a)=HashMassAdapter.workspace entry := by
  funext j
  let i := HashMassAdapter.workPort j
  have hout : i.val < 320 ∨ 324 < i.val := by
    dsimp [i,HashMassAdapter.workPort]
    split_ifs <;> simp only <;> omega
  have hne : i≠323 := by
    intro he
    rw [he] at hout
    norm_num [Fin.coe_ofNat_eq_mod] at hout
  change (result a).stacks i=entry.stacks i
  rw [result_stacks, ite_eq_right hne]
  by_cases hk : kept i=true
  · rw [ite_eq_left hk]
    exact hframe i hk
  · rw [ite_eq_right hk]
    exact (hblank i (Bool.eq_false_iff.mpr hk) hout).symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
