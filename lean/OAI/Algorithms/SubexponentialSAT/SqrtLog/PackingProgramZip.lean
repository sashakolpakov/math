import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramStreamBounds
import OAI.Algorithms.SubexponentialSAT.SubexpInputZip

namespace OAI.Algorithms

/-! Actual pairing and weighting of two candidate-ordered unary score streams.
This is one fixed finite program; no precomputed pair list is an input premise. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Zip
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 8 14

def zipPorts (i : Fin 8) : Fin 14 := i.castAdd 6
def scorePorts : Fin 12 → Fin 14 := ![12,0,13,1,2,3,4,5,6,7,8,9]

theorem zipPorts_injective : Function.Injective zipPorts := Fin.castAdd_injective _ _
theorem scorePorts_injective : Function.Injective scorePorts := by decide

def rawPairs (ps : List (ℕ × ℕ)) : List (List Bool × List Bool) :=
  ps.map (fun p => (List.replicate p.1 false,List.replicate p.2 false))

def firstScores (ps : List (ℕ × ℕ)) := ps.map (fun p => List.replicate p.1 false)
def secondScores (ps : List (ℕ × ℕ)) := ps.map (fun p => List.replicate p.2 false)

theorem rawPairs_bytes (ps : List (ℕ × ℕ)) :
    SubexponentialSAT.SubexpDotControl.encodePairs id (rawPairs ps) = Streams.pairsBytes ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [rawPairs,SubexponentialSAT.SubexpDotControl.encodePairs,SubexponentialSAT.SubexpDotControl.payload,
      Streams.pairsBytes,Streams.payload]
    exact ih

def base (regs : Fin 8 → Bool) (wi wh : List Bool) : Data :=
  ⟨regs, fun j => if j=12 then wi else if j=13 then wh else []⟩

noncomputable def input (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) : Data :=
  embedState id zipPorts (base regs wi wh)
    (SubexponentialSAT.SubexpInputZip.ready regs
      (SubexponentialSAT.ProgramEncoding.encodeRecords (firstScores ps))
      (SubexponentialSAT.ProgramEncoding.encodeRecords (secondScores ps)) [] [])

theorem input_regs (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    (input regs wi wh ps).regs = regs := by
  funext i
  exact embedState_register id zipPorts _ _ Function.injective_id i

theorem input_stacks (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    (input regs wi wh ps).stacks =
      ![SubexponentialSAT.ProgramEncoding.encodeRecords (firstScores ps),
        SubexponentialSAT.ProgramEncoding.encodeRecords (secondScores ps),[],[],[],[],[],[],[],[],[],[],wi,wh] := by
  have hz (i : Fin 8) := embedState_stack id zipPorts (base regs wi wh)
    (SubexponentialSAT.SubexpInputZip.ready regs
      (SubexponentialSAT.ProgramEncoding.encodeRecords (firstScores ps))
      (SubexponentialSAT.ProgramEncoding.encodeRecords (secondScores ps)) [] []) zipPorts_injective i
  have hf (j : Fin 14) (hj : 8 ≤ j.val) : (input regs wi wh ps).stacks j=(base regs wi wh).stacks j := by
    apply embedState_stack_frame
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    dsimp [zipPorts] at hv
    omega
  funext j
  fin_cases j <;> first
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 0
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 1
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 2
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 3
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 4
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 5
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 6
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 7
    | simpa [base] using hf (8 : Fin 14) (by decide)
    | simpa [base] using hf (9 : Fin 14) (by decide)
    | simpa [base] using hf (10 : Fin 14) (by decide)
    | simpa [base] using hf (11 : Fin 14) (by decide)
    | simpa [base] using hf (12 : Fin 14) (by decide)
    | simpa [base] using hf (13 : Fin 14) (by decide)

noncomputable def middle (regs initialRegs : Fin 8 → Bool) (wi wh : List Bool)
    (ps : List (ℕ × ℕ)) : Data :=
  embedState id zipPorts (base initialRegs wi wh)
    (SubexponentialSAT.SubexpInputZip.ready regs [] [] [] (Streams.pairsBytes ps))

 theorem middle_projection (regs initialRegs : Fin 8 → Bool) (wi wh : List Bool)
    (ps : List (ℕ × ℕ)) :
    projectState id scorePorts (middle regs initialRegs wi wh ps) =
      Streams.ready regs wi wh (Streams.pairsBytes ps) [] [] := by
  have hz (i : Fin 8) := embedState_stack id zipPorts (base initialRegs wi wh)
    (SubexponentialSAT.SubexpInputZip.ready regs [] [] [] (Streams.pairsBytes ps)) zipPorts_injective i
  have hw12 : (middle regs initialRegs wi wh ps).stacks 12 = wi := by
    apply (embedState_stack_frame id zipPorts _ _ 12 ?_).trans
    · rfl
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      dsimp [zipPorts] at hv
      omega
  have hw13 : (middle regs initialRegs wi wh ps).stacks 13 = wh := by
    apply (embedState_stack_frame id zipPorts _ _ 13 ?_).trans
    · rfl
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      dsimp [zipPorts] at hv
      omega
  have hz8 : (middle regs initialRegs wi wh ps).stacks 8 = [] := by
    apply (embedState_stack_frame id zipPorts _ _ 8 ?_).trans
    · rfl
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      dsimp [zipPorts] at hv
      omega
  have hz9 : (middle regs initialRegs wi wh ps).stacks 9 = [] := by
    apply (embedState_stack_frame id zipPorts _ _ 9 ?_).trans
    · rfl
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      dsimp [zipPorts] at hv
      omega
  apply SubexponentialSAT.CounterForPrograms.data_ext
  · funext i
    exact embedState_register id zipPorts _ _ Function.injective_id i
  · funext i
    fin_cases i <;> first
      | exact hw12
      | exact hw13
      | exact hz8
      | exact hz9
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 0
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 1
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 2
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 3
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 4
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 5
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 6
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 7

 def pair : Cmd 8 14 := .call
  (SubexponentialSAT.ProgramLinking.liftProgram SubexponentialSAT.SubexpInputZip.program id zipPorts)
 def weight : Cmd 8 14 := liftCommand Streams.command 8 10 id scorePorts
 def command : Cmd 8 14 := .seq pair weight
 def program := compiled command 0 8
 def budget (wi wh : List Bool) (ps : List (ℕ × ℕ)) :=
  26*SubexponentialSAT.SubexpInputZip.inputBits (rawPairs ps)+53*ps.length+12 +
    Streams.streamBudget wi wh ps+1

 theorem final_clean (rz initialRegs rf : Fin 8 → Bool) (wi wh : List Bool)
    (ps : List (ℕ × ℕ)) (j : Fin 14) (hj8 : j ≠ 8) (hj12 : j ≠ 12) (hj13 : j ≠ 13) :
    (embedState id scorePorts (middle rz initialRegs wi wh ps)
      (Streams.ready rf wi wh [] []
        (SubexponentialSAT.ProgramEncoding.encodeRecords (Streams.scores wi wh ps)))).stacks j = [] := by
  by_cases hs : ∃ i, scorePorts i = j
  · obtain ⟨i, rfl⟩ := hs
    rw [embedState_stack id scorePorts _ _ scorePorts_injective]
    fin_cases i <;> simp [scorePorts,Streams.ready,Streams.state] at hj8 hj12 hj13 ⊢
  · rw [embedState_stack_frame id scorePorts _ _ j hs]
    by_cases hz : ∃ k, zipPorts k = j
    · obtain ⟨k, rfl⟩ := hz
      change (embedState id zipPorts _ _).stacks (zipPorts k) = []
      rw [embedState_stack id zipPorts _ _ zipPorts_injective]
      by_cases hk : k = 6
      · subst k
        exact False.elim (hs ⟨8,rfl⟩)
      · fin_cases k <;> simp [] at hk ⊢
    · change (embedState id zipPorts _ _).stacks j = []
      rw [embedState_stack_frame id zipPorts _ _ j hz]
      simp [base,hj12,hj13]

 theorem command_eval (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    ∃ n ≤ budget wi wh ps, ∃ e : Data,
      Eval command n (input regs wi wh ps) e ∧
      e.stacks 8 = SubexponentialSAT.ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
      e.stacks 12 = wi ∧ e.stacks 13 = wh ∧
      (∀ j, j ≠ 8 → j ≠ 12 → j ≠ 13 → e.stacks j = []) := by
  obtain ⟨rz, hz⟩ := SubexponentialSAT.SubexpInputZip.program_trace (rawPairs ps) regs [] [] []
  have hf : SubexponentialSAT.SubexpInputZip.rowWords (rawPairs ps) = firstScores ps := by
    simp [SubexponentialSAT.SubexpInputZip.rowWords,rawPairs,firstScores,List.map_map,Function.comp_def]
  have hh : SubexponentialSAT.SubexpInputZip.inputWords (rawPairs ps) = secondScores ps := by
    simp [SubexponentialSAT.SubexpInputZip.inputWords,rawPairs,secondScores,List.map_map,Function.comp_def]
  rw [hf,hh,rawPairs_bytes] at hz
  simp only [List.append_nil] at hz
  have hzip := eval_call_lifted SubexponentialSAT.SubexpInputZip.program id zipPorts (base regs wi wh)
    Function.injective_id zipPorts_injective hz
  change Eval pair _ (input regs wi wh ps) (middle rz regs wi wh ps) at hzip
  obtain ⟨n, hn, rs, hs⟩ := Streams.command_eval rz wi wh ps
  have hs' : Eval Streams.command n (projectState id scorePorts (middle rz regs wi wh ps))
      (Streams.ready rs wi wh [] [] (SubexponentialSAT.ProgramEncoding.encodeRecords (Streams.scores wi wh ps))) := by
    rw [middle_projection]
    exact hs
  have hweight := eval_liftCommand_from_state Streams.command 8 10 id scorePorts
    (middle rz regs wi wh ps) Function.injective_id scorePorts_injective hs'
  refine ⟨_, ?_, _, hzip.seq hweight, ?_, ?_, ?_, ?_⟩
  · unfold budget
    simpa only [rawPairs,List.length_map,Nat.add_assoc] using Nat.add_le_add_left (Nat.add_le_add_right hn 1)
      (26*SubexponentialSAT.SubexpInputZip.inputBits (rawPairs ps)+53*(rawPairs ps).length+12)
  · exact embedState_stack id scorePorts _ _ scorePorts_injective 10
  · exact embedState_stack id scorePorts _ _ scorePorts_injective 0
  · exact embedState_stack id scorePorts _ _ scorePorts_injective 2
  · exact final_clean rz regs rs wi wh ps

 theorem program_primitive (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    ∃ e : Data, SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(budget wi wh ps+1))
      (primitiveCfg program ((input regs wi wh ps).withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks 8 = SubexponentialSAT.ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
      e.stacks 12 = wi ∧ e.stacks 13 = wh ∧
      (∀ j, j ≠ 8 → j ≠ 12 → j ≠ 13 → e.stacks j = []) := by
  obtain ⟨n, hn, e, he, ho, hi, hh, hclean⟩ := command_eval regs wi wh ps
  exact ⟨e,primitive_execution program ⟨n+1,by omega,compiled_halt_trace he 0 8⟩,ho,hi,hh,hclean⟩

 theorem inputBits_bound (ps : List (ℕ × ℕ)) (C : ℕ)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    SubexponentialSAT.SubexpInputZip.inputBits (rawPairs ps) ≤ 2*C*ps.length := by
  induction ps with
  | nil => simp [rawPairs,SubexponentialSAT.SubexpInputZip.inputBits]
  | cons p ps ih =>
    have hp := hc p (by simp)
    have ht := ih (fun a ha => hc a (by simp [ha]))
    simp only [rawPairs,List.map_cons,SubexponentialSAT.SubexpInputZip.inputBits,
      List.length_replicate,List.length_cons]
    simp only [rawPairs] at ht
    nlinarith

 theorem budget_bound (wi wh : List Bool) (ps : List (ℕ × ℕ)) (B W C : ℕ)
    (hbi : wi.length ≤ B) (hbh : wh.length ≤ B)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    budget wi wh ps+1 ≤ 500*(ps.length+1)*(W+1)*(B+C+1) := by
  have hz := inputBits_bound ps C hc
  have hs := Streams.streamBudget_bound wi wh ps B W C hbi hbh hi hh hc
  unfold budget
  nlinarith [Nat.zero_le (ps.length*W*B),Nat.zero_le (ps.length*W*C),
    Nat.zero_le (ps.length*B),Nat.zero_le (ps.length*C),Nat.zero_le (W*B),Nat.zero_le (W*C)]
end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
