import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramSize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputInstall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramMask

namespace OAI.Algorithms

/-! Entry from the actual descending high mask produced by the high-variable pass. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Entry
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := Install.Data
def sourceStacks (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Fin 48 → List Bool :=
  fun j => if j=32 then Scan.scopeBits scopes else if j=33 then Scan.unary n
    else if j=36 then mask else []
def input (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Data :=
  ⟨r,fun j => if j=37 then mask.reverse else if j=36 then [] else sourceStacks scopes n mask j⟩
def registers : Fin 2 → Fin 16 := Fin.castAdd 14
def ports : Fin 4 → Fin 48 := ![37,38,36,39]
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 2 14
theorem ports_injective : Function.Injective ports := by decide
abbrev maskCall : Cmd 16 48 := .call (ProgramLinking.liftProgram
  HighIncidenceProgram.Mask.program registers ports)
abbrev prepare : Cmd 16 48 := .seq maskCall (.call (StackRoutines.clearProgram 37 0 1))
abbrev command : Cmd 16 48 := .seq prepare Install.command
def program := compiled command 32 45
def budget (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  12*mask.length+12+Install.budget scopes n mask

theorem install_stacks (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Install.input r scopes n mask).stacks = sourceStacks scopes n mask := by
  let d := Scan.data r scopes n 0 0 mask []
  funext j
  by_cases hj : ∃ i, Install.ports i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [show (Install.input r scopes n mask).stacks (Install.ports i) = d.stacks i from
      Install.state_stack d i]
    fin_cases i <;> simp [d,Scan.data,Install.ports,sourceStacks]
  · rw [show (Install.input r scopes n mask).stacks j = [] from Install.state_frame d j hj]
    have h32 : j ≠ 32 := fun h => hj ⟨20,h.symm⟩
    have h33 : j ≠ 33 := fun h => hj ⟨21,h.symm⟩
    have h36 : j ≠ 36 := fun h => hj ⟨26,h.symm⟩
    simp [sourceStacks,h32,h33,h36]
theorem install_eq (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    Install.input r scopes n mask = ⟨r,sourceStacks scopes n mask⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    exact Install.state_register (Scan.data r scopes n 0 0 mask []) i
  · exact install_stacks r scopes n mask

theorem prepare_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ rf, Eval prepare (12*mask.length+12) (input r scopes n mask)
      (Install.input rf scopes n mask) := by
  let a := input r scopes n mask
  obtain ⟨rm,hm⟩ := HighIncidenceProgram.Mask.command_eval (r ∘ registers) mask.reverse
  let small := HighIncidenceProgram.Mask.state (r ∘ registers) mask.reverse [] [] []
  let smallOut := HighIncidenceProgram.Mask.state rm mask.reverse [] mask []
  have hin : embedState registers ports a small = a := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [small,ports,a,input,sourceStacks]
    · intros; rfl
  have hm' : Eval HighIncidenceProgram.Mask.command (10*mask.length+8) small smallOut := by
    simpa [small,smallOut] using hm
  let e := embedState registers ports a smallOut
  have he := eval_call_lifted HighIncidenceProgram.Mask.program registers ports a
    registers_injective ports_injective (compiled_halt_trace hm' 0 2)
  rw [hin] at he
  change Eval maskCall (10*mask.length+8+1) a e at he
  have hs : e.stacks = fun j => if j=37 then mask.reverse else sourceStacks scopes n mask j := by
    funext j
    by_cases hj : ∃ i, ports i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [show e.stacks (ports i) = smallOut.stacks i from
        embedState_stack registers ports a smallOut ports_injective i]
      fin_cases i <;> simp [smallOut,ports,sourceStacks]
    · rw [show e.stacks j = a.stacks j from
        embedState_stack_frame registers ports a smallOut j hj]
      have h36 : j ≠ 36 := fun h => hj ⟨2,h.symm⟩
      have h37 : j ≠ 37 := fun h => hj ⟨0,h.symm⟩
      simp [a,input,h36,h37]
  let rf := readRegs e.regs 0 1 none
  have hc := TupleProgram.clear_eval (37 : Fin 48) (0 : Fin 16) 1 e
  have hend : (⟨rf,StackRoutines.clearStacks 37 e.stacks⟩ : Data) =
      Install.input rf scopes n mask := by
    rw [install_eq]
    apply congrArg (StructuredProgram.State.mk rf)
    funext j
    by_cases h : j=37
    · subst j; simp [StackRoutines.clearStacks,sourceStacks]
    · simp [StackRoutines.clearStacks,hs,h]
  change Eval _ _ e (⟨rf,StackRoutines.clearStacks 37 e.stacks⟩ : Data) at hc
  rw [hend] at hc
  refine ⟨rf,?_⟩
  convert he.seq hc using 1 ; simp [hs] ; omega

theorem primitive_run (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*budget scopes n mask)
      (primitiveCfg program ((input r scopes n mask).withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks 45 = PairScoreProgram.pairRecords
        (PackingIncidenceProgram.generatedRawPairs (Install.plans scopes n mask)) := by
  obtain ⟨rf,hp⟩ := prepare_eval r scopes n mask
  obtain ⟨t,e,ht,he,hout⟩ := Install.command_eval rf scopes n mask
  have hr : RunsIn program (budget scopes n mask)
      ((input r scopes n mask).withPC (some program.entry)) (e.withPC none) :=
    ⟨12*mask.length+12+t+1,by dsimp [budget]; omega,compiled_halt_trace (hp.seq he) 32 45⟩
  exact ⟨e,BitProgram.primitive_execution program hr,hout⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Entry


/-! Raw scopes and the computed mask feed the actual incidence-pair producer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Finished
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

abbrev incidenceList (scopes : List (List ℕ)) (mask : List Bool) :=
  List.finRange (Semantics.nativeEntries scopes mask).length

theorem generated_pairs (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) :
    (PackingIncidenceProgram.generatedRawPairs (Install.plans scopes n mask)).Perm
      (PackingIncidenceProgram.rawPairs (Semantics.owner scopes n mask hm)
        (Semantics.factor scopes n mask hm)
        (Semantics.seedIndices n (Semantics.factorCount scopes mask))
        (incidenceList scopes mask)) := by
  rw [Install.plans, ← Semantics.incidencePlans_eq scopes n mask hm]
  exact PackingIncidenceProgram.generatedIncidencePairs_perm _ _ _ _

/-- The primitive output is the table whose order is accepted by the exact
conditional incidence scorer. No linear read-plan table is an input. -/
theorem primitive_pairs (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ)
    (mask : List Bool) (hm : mask.length ≤ n) :
    ∃ e : Entry.Data, ∃ raw : List PackingIncidenceProgram.PlanPair,
      Computation.RunsIn (primitive Entry.program).step
        (primitiveOverhead Entry.program * Entry.budget scopes n mask)
        (primitiveCfg Entry.program ((Entry.input r scopes n mask).withPC
          (some Entry.program.entry)))
        (primitiveCfg Entry.program (e.withPC none)) ∧
      e.stacks 45 = PairScoreProgram.pairRecords raw ∧
      raw.Perm (PackingIncidenceProgram.rawPairs (Semantics.owner scopes n mask hm)
        (Semantics.factor scopes n mask hm)
        (Semantics.seedIndices n (Semantics.factorCount scopes mask))
        (incidenceList scopes mask)) := by
  obtain ⟨e,he,hout⟩ := Entry.primitive_run r scopes n mask
  exact ⟨e,_,he,hout,generated_pairs scopes n mask hm⟩

/-- The very same generated plan order refines the exact Cinc score. -/
theorem score_refines (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) :
    let indices := Semantics.seedIndices n (Semantics.factorCount scopes mask)
    let incidences := incidenceList scopes mask
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (PackingIncidenceProgram.incidenceNumerator (Semantics.owner scopes n mask hm)
        (Semantics.factor scopes n mask hm) (a::tail) (incidences.product incidences) indices a)
      PackingIncidenceProgram.command
      (PackingIncidenceProgram.runtimeBound indices.length (incidences.length^2)
        (a::tail).length (ReadPlan.wordWidth r Q)) indices.length
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length
        (PackingIncidenceProgram.generatedRawPairs (Install.plans scopes n mask))) := by
  dsimp only
  rw [Install.plans, ← Semantics.incidencePlans_eq scopes n mask hm]
  exact PackingIncidenceProgram.generated_refines _ _ a tail _
    (Semantics.seedIndices_complete _ _) _

theorem output_bits_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) :
    (PairScoreProgram.pairRecords (PackingIncidenceProgram.generatedRawPairs
      (Install.plans scopes n mask))).length ≤
      1 + (32*(n+Semantics.factorCount scopes mask+1)+14)*
        (Semantics.nativeEntries scopes mask).length^2 := by
  rw [Install.plans, ← Semantics.incidencePlans_eq scopes n mask hm]
  have h := PackingIncidenceProgram.generatedPairRecords_length_le
    (Semantics.owner scopes n mask hm) (Semantics.factor scopes n mask hm)
    (Semantics.seedIndices n (Semantics.factorCount scopes mask))
    (Semantics.seedIndices_complete _ _) (incidenceList scopes mask)
  simpa [Semantics.seedIndices,Packing.headsFirst_length,incidenceList] using h
theorem pair_budget_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) :
    PackingIncidenceProgram.Install.budget (Install.plans scopes n mask) ≤
      100*(2400*((Semantics.nativeEntries scopes mask).length+1)^2*
        (24*(n+Semantics.factorCount scopes mask)+34)+11+
        (16*(n+Semantics.factorCount scopes mask)+24)*
          (Semantics.nativeEntries scopes mask).length) := by
  let S := n+Semantics.factorCount scopes mask
  let ps := Install.plans scopes n mask
  have hlen : ps.length = (Semantics.nativeEntries scopes mask).length := by
    simp [ps,Install.plans,Semantics.plans_eq,Semantics.nativeEntries]
  have hi : (Semantics.seedIndices n (Semantics.factorCount scopes mask)).length = S := by
    simp [Semantics.seedIndices,Packing.headsFirst_length,S]
  have hv := PackingIncidenceProgram.incidencePlans_valid
    (Semantics.owner scopes n mask hm) (Semantics.factor scopes n mask hm)
    (Semantics.seedIndices n (Semantics.factorCount scopes mask))
    (Semantics.seedIndices_complete _ _) (incidenceList scopes mask)
  rw [Semantics.incidencePlans_eq,hi] at hv
  have hb := PackingIncidenceProgram.planInput_length_le S ps hv.1 hv.2
  have hp : TupleProgram.powerCost (PackingIncidenceProgram.planAlphabet ps) 2 [[]]+9 ≤
      2400*(ps.length+1)^2*(24*S+34)+9 := by
    by_cases hn : ps = []
    · have hz : TupleProgram.powerCost [] 2 [[]]+9 ≤ 2400*34+9 := by decide
      simp only [hn,PackingIncidenceProgram.planAlphabet,List.map_nil,List.length_nil,
        zero_add,one_pow,mul_one]
      nlinarith
    · have h := PackingIncidenceProgram.rawPairProgram_cost S ps hn hv.1 hv.2
      have hsq : ps.length^2 ≤ (ps.length+1)^2 := by nlinarith
      have hmul := Nat.mul_le_mul_right (2400*(24*S+34)) hsq
      nlinarith
  change PackingIncidenceProgram.Install.budget ps ≤ _
  dsimp [PackingIncidenceProgram.Install.budget]
  rw [← hlen]
  change _ ≤ 100*(2400*(ps.length+1)^2*(24*S+34)+11+(16*S+24)*ps.length)
  omega

/-- Explicit polynomial bound for the whole descending-mask-to-pair-table path. -/
theorem entry_budget_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) :
    Entry.budget scopes n mask ≤
      4000*(Cost.inputSize scopes n mask)^3+12*mask.length+16+
      100*(2400*((Semantics.nativeEntries scopes mask).length+1)^2*
        (24*(n+Semantics.factorCount scopes mask)+34)+11+
        (16*(n+Semantics.factorCount scopes mask)+24)*
          (Semantics.nativeEntries scopes mask).length) := by
  have hn := Cost.native_cubic scopes n mask
  have hp := pair_budget_le scopes n mask hm
  dsimp [Entry.budget,Install.budget]
  omega

theorem whole_input_polynomial (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) :
    Entry.budget scopes n mask ≤ 60000000*(Cost.inputSize scopes n mask)^5 := by
  let W := Cost.inputSize scopes n mask
  let D := (Semantics.nativeEntries scopes mask).length
  let S := n+Semantics.factorCount scopes mask
  have hW : 1 ≤ W := by dsimp [W,Cost.inputSize]; omega
  have hq : scopes.length+1 ≤ (Scan.scopeBits scopes).length :=
    Encoding.length_encodeList_lower _ scopes
  have hcounter := Semantics.counter_le scopes mask 0 scopes.length
  have hS : S ≤ W := by dsimp [S,Semantics.factorCount,W,Cost.inputSize] at *; omega
  have hD : D ≤ W^2 := by
    have hd := Semantics.entries_length_le scopes mask 0 scopes.length
    have hmW : mask.length ≤ W := by dsimp [W,Cost.inputSize]; omega
    have hqW : scopes.length+1 ≤ W := by dsimp [W,Cost.inputSize]; omega
    calc
      D ≤ mask.length*(scopes.length+1) := hd
      _ ≤ W*W := Nat.mul_le_mul hmW hqW
      _ = W^2 := by ring
  have hW2 : 1 ≤ W^2 := by nlinarith
  have hD2 : (D+1)^2 ≤ 4*W^4 := by
    have hh := Nat.pow_le_pow_left (show D+1 ≤ 2*W^2 by omega) 2
    nlinarith
  have hcoef : 24*S+34 ≤ 58*W := by omega
  have hmain : 2400*(D+1)^2*(24*S+34) ≤ 556800*W^5 := by
    calc
      _ ≤ 2400*(4*W^4)*(58*W) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2400 hD2) hcoef
      _ = _ := by ring
  have hother : (16*S+24)*D ≤ 40*W^3 := by
    calc
      _ ≤ (40*W)*(W^2) := Nat.mul_le_mul (by omega) hD
      _ = _ := by ring
  have h05 : 1 ≤ W^5 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right hW (show 0 ≤ 5 by decide)
  have h15 : W ≤ W^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hW (show 1 ≤ 5 by decide)
  have h35 : W^3 ≤ W^5 := Nat.pow_le_pow_right hW (by decide)
  have hmask : mask.length ≤ W := by dsimp [W,Cost.inputSize]; omega
  have hb := entry_budget_le scopes n mask hm
  change Entry.budget scopes n mask ≤
    4000*W^3+12*mask.length+16+100*(2400*(D+1)^2*(24*S+34)+11+(16*S+24)*D) at hb
  change Entry.budget scopes n mask ≤ 60000000*W^5
  omega

theorem primitive_pairs_polynomial (r : Fin 16 → Bool) (scopes : List (List ℕ))
    (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n) :
    ∃ e : Entry.Data, ∃ raw : List PackingIncidenceProgram.PlanPair,
      Computation.RunsIn (primitive Entry.program).step
        (primitiveOverhead Entry.program * (60000000*(Cost.inputSize scopes n mask)^5))
        (primitiveCfg Entry.program ((Entry.input r scopes n mask).withPC
          (some Entry.program.entry)))
        (primitiveCfg Entry.program (e.withPC none)) ∧
      e.stacks 45 = PairScoreProgram.pairRecords raw ∧
      raw.Perm (PackingIncidenceProgram.rawPairs (Semantics.owner scopes n mask hm)
        (Semantics.factor scopes n mask hm)
        (Semantics.seedIndices n (Semantics.factorCount scopes mask))
        (incidenceList scopes mask)) := by
  obtain ⟨e,raw,hr,hout,hperm⟩ := primitive_pairs r scopes n mask hm
  exact ⟨e,raw,hr.mono (Nat.mul_le_mul_left _ (whole_input_polynomial scopes n mask hm)),
    hout,hperm⟩

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Finished

end OAI.Algorithms
