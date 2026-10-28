import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFSemanticHelpers
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Actual stable subtraction of a core from an encoded clause. Membership
tests, core copies, record emission, and order restoration use finite code. -/
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

abbrev Regs := Fin 10 → Bool
abbrev Data := State 10 9

def smallState (regs : Regs) (source query output target : List Bool) : State 10 8 :=
  ⟨regs, ![source, query, output, target, [], [], [], []]⟩

def state (regs : Regs) (source query output target core : List Bool) : Data :=
  ⟨regs, ![source, query, output, target, [], [], [], [], core]⟩

def lowStack (i : Fin 8) : Fin 9 := Fin.castAdd 1 i
theorem lowStack_injective : Function.Injective lowStack := Fin.castAdd_injective 8 1

private theorem embed_small_state (frameRegs regs : Regs)
    (source₀ query₀ output₀ target₀ source query output target core : List Bool) :
    embedState id lowStack (state frameRegs source₀ query₀ output₀ target₀ core)
      (smallState regs source query output target) = state regs source query output target core := by
  apply embedState_eq_of_ports id lowStack _ _ _ Function.injective_id lowStack_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hlo : 8 ≤ i.val := by
      by_contra h
      have hil : i.val < 8 := by omega
      exact hi ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
    fin_cases i <;> simp_all [state]

abbrev probe : Cmd 10 8 :=
  .seq ExecCNFSubset.memberCall (.seq (ExecCNFSubset.clear 3) (ExecCNFSubset.clear 4))

def probeProgram := compiled probe 3 4

theorem probe_eval (bits : List Bool) (H : List (List Bool)) (regs : Regs)
    (source output : List Bool) :
    ∃ n ≤ (20 * bits.length + 32) * (Encoding.encodeList id H).length + 10,
      ∃ rf : Regs, rf 4 = decide (bits ∈ H) ∧
      Eval probe n (smallState regs source bits.reverse output (Encoding.encodeList id H))
        (smallState rf source bits.reverse output []) := by
  let d := smallState regs source bits.reverse output (Encoding.encodeList id H)
  obtain ⟨n, hn, e, he, ha, hs, hp, hq, hc, ht, h0, h2, h7, hreg7, hreg8, hreg9⟩ :=
    ExecCNFSubset.memberCall_eval bits H d rfl rfl rfl rfl rfl
  let result := ExecCNFSubset.cleared 4 (ExecCNFSubset.cleared 3 e)
  have hresult : result = smallState result.regs source bits.reverse output [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ smallState, StackRoutines.clearStacks,
        h0, h2, h7, hq, hc, ht, d]
  have hcost : (2 * ((ExecCNFSubset.cleared 3 e).stacks 4).length + 3) = 5 := by
    simp [ StackRoutines.clearStacks, hp]
  have hfull := he.seq ((ExecCNFSubset.clear_eval 3 e).seq
    (ExecCNFSubset.clear_eval 4 (ExecCNFSubset.cleared 3 e)))
  rw [hcost] at hfull
  change Eval probe _ d result at hfull
  rw [hresult] at hfull
  refine ⟨n + ((2 * (e.stacks 3).length + 3) + 5), ?_, result.regs, ?_, hfull⟩
  · nlinarith
  · simpa [result, ExecCNFSubset.cleared, readRegs] using ha

abbrev wideProbe : Cmd 10 9 := .call (ProgramLinking.liftProgram probeProgram id lowStack)

theorem wideProbe_eval (bits : List Bool) (H : List (List Bool)) (regs : Regs)
    (source output core : List Bool) :
    ∃ n ≤ (20 * bits.length + 32) * (Encoding.encodeList id H).length + 11,
      ∃ rf : Regs, rf 4 = decide (bits ∈ H) ∧
      Eval wideProbe n (state regs source bits.reverse output (Encoding.encodeList id H) core)
        (state rf source bits.reverse output [] core) := by
  obtain ⟨n, hn, rf, hr, he⟩ := probe_eval bits H regs source output
  have h := eval_call_lifted probeProgram id lowStack
    (state regs source bits.reverse output (Encoding.encodeList id H) core)
    Function.injective_id lowStack_injective (compiled_halt_trace he 3 4)
  rw [embed_small_state, embed_small_state] at h
  exact ⟨n + 1, by omega, rf, hr, h⟩

abbrev copyCore : Cmd 10 9 := .call (StackRoutines.copyProgram 8 3 7 0 1)

theorem copyCore_eval (regs : Regs) (source query output core : List Bool) :
    Eval copyCore (7 * core.length + 5)
      (state regs source query output [] core)
      (state (readRegs regs 0 1 none) source query output core core) := by
  have h := ListRegisterProgram.copy_run (r := 10) (s := 9) 8 3 7 0 1
    (by decide) (by decide) (by decide) (by decide) regs
    (state regs source query output [] core).stacks rfl
  have hs : StackRoutines.copyStacks 8 3 (state regs source query output [] core).stacks =
      (state (readRegs regs 0 1 none) source query output core core).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.copyStacks]
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state] using h

abbrev emit : Cmd 10 9 :=
  .call (ProgramLinking.liftProgram ExecLiteralDedupProgram.emitProgram id lowStack)

theorem emit_eval (selected : Bool) (bits : List Bool) (regs : Regs)
    (source output core : List Bool) (hr : regs 9 = selected) :
    ∃ rf : Regs, rf 7 = false ∧ rf 8 = true ∧ rf 9 = false ∧
      Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1)
        (state regs source bits.reverse output [] core)
        (state rf source []
          (if selected then true :: (Encoding.frame bits ++ output) else output) [] core) := by
  let d := smallState regs source bits.reverse output []
  obtain ⟨e, he, h0, h1, h2, h3, h4, h5, h6, h7, hr7, hr8, hr9⟩ :=
    ExecLiteralDedupProgram.emitCall_eval selected bits d rfl hr
  have heq : e = smallState e.regs source []
      (if selected then true :: (Encoding.frame bits ++ output) else output) [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [smallState, h0, h1, h2, h3, h4, h5, h6, h7, d]
  have ht : Trace ExecLiteralDedupProgram.emitProgram
      (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1)
      (d.withPC (some ExecLiteralDedupProgram.emitProgram.entry)) (e.withPC none) := by
    cases he with
    | call _ h => exact h
  rw [heq] at ht
  have h := eval_call_lifted ExecLiteralDedupProgram.emitProgram id lowStack
    (state regs source bits.reverse output [] core) Function.injective_id lowStack_injective ht
  change Eval emit _ (embedState id lowStack _ (smallState regs source bits.reverse output [])) _ at h
  rw [embed_small_state, embed_small_state] at h
  exact ⟨e.regs, hr7, hr8, hr9, h⟩

abbrev callback : Cmd 10 9 :=
  .seq copyCore (.seq wideProbe (.seq (RecordPrograms.atom (.bnot 9 4)) emit))

def callbackCost (H : List (List Bool)) (bits : List Bool) : ℕ :=
  60 * ((Encoding.encodeList id H).length + 1) * (bits.length + 1)

theorem callback_eval (bits : List Bool) (H : List (List Bool)) (regs : Regs)
    (source output : List Bool) :
    ∃ n ≤ callbackCost H bits, ∃ rf : Regs,
      rf 7 = false ∧ rf 8 = true ∧ rf 9 = false ∧
      Eval callback n (state regs source bits.reverse output [] (Encoding.encodeList id H))
        (state rf source []
          (if bits ∈ H then output else true :: (Encoding.frame bits ++ output))
          [] (Encoding.encodeList id H)) := by
  obtain ⟨n, hn, rf, hr, he⟩ := wideProbe_eval bits H (readRegs regs 0 1 none)
    source output (Encoding.encodeList id H)
  let selected := Function.update rf 9 (!(rf 4))
  have hs : selected 9 = !(decide (bits ∈ H)) := by simp [selected, hr]
  obtain ⟨final, hf7, hf8, hf9, hf⟩ := emit_eval (!(decide (bits ∈ H))) bits selected
    source output (Encoding.encodeList id H) hs
  have hselect : Eval (RecordPrograms.atom (.bnot 9 4)) 1
      (state rf source bits.reverse output [] (Encoding.encodeList id H))
      (state selected source bits.reverse output [] (Encoding.encodeList id H)) :=
    .base (.atom _ _)
  have hfull := (copyCore_eval regs source bits.reverse output (Encoding.encodeList id H)).seq
    (he.seq (hselect.seq hf))
  have hcost := SubexpNormalizeProgram.emitIfSelected_steps_le (!(decide (bits ∈ H))) bits
  refine ⟨(7 * (Encoding.encodeList id H).length + 5) +
    (n + (1 + (SubexpNormalizeProgram.emitIfSelectedSteps (!(decide (bits ∈ H))) bits + 1))),
    ?_, final, hf7, hf8, hf9, ?_⟩
  · dsimp [callbackCost]
    nlinarith
  · simpa using hfull

end SubexponentialSAT.ExecPetalProgram
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

def flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 7 v) 8 p) 9 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 7) (regs 8) (regs 9) = regs := by
  funext i
  by_cases h7 : i = 7 <;> by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;>
    simp_all [flags ]

def ports : RecordPrograms.Ports 10 9 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem record_state (regs : Regs) (src query output target core tail bits : List Bool)
    (v p f : Bool) :
    RecordPrograms.state ports (state regs src query output target core) v p f tail bits =
      state (flags regs v p f) tail bits output target core := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports, state]

def invariant (H : List (List Bool)) (d : Data) : Prop :=
  ∃ regs source output payload,
    d = state regs source payload output [] (Encoding.encodeList id H)

theorem state_invariant (H : List (List Bool)) (regs : Regs) (source output payload : List Bool) :
    invariant H (state regs source payload output [] (Encoding.encodeList id H)) :=
  ⟨regs, source, output, payload, rfl⟩

def keep (H : List (List Bool)) (bits : List Bool) : Bool := !decide (bits ∈ H)

def result {α : Type*} [DecidableEq α] (C H : List α) : List α :=
  C.filter (fun x => !decide (x ∈ H))

theorem result_eq_filter_keep (C H : List (List Bool)) :
    result C H = C.filter (keep H) := by
  unfold result
  apply List.filter_congr
  intro x hx
  simp [keep]

theorem result_encoded_length_le {α : Type*} [DecidableEq α]
    (enc : α → List Bool) (C H : List α) :
    (Encoding.encodeList enc (result C H)).length ≤ (Encoding.encodeList enc C).length :=
  Encoding.length_encodeList_filter_le enc _ C

theorem callback_contract (H : List (List Bool)) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false) (callbackCost H)
      (invariant H) (SubexpNormalizeProgram.FilterEffect 2 (keep H)) := by
  intro bits tail base hbase
  obtain ⟨regs, source, output, payload, rfl⟩ := hbase
  obtain ⟨n, hn, rf, h7, h8, h9, he⟩ :=
    callback_eval bits H (flags regs false true false) tail output
  let newOutput := if bits ∈ H then output else true :: (Encoding.frame bits ++ output)
  let next := state rf [] [] newOutput [] (Encoding.encodeList id H)
  have hflags : flags rf false true false = rf := by
    simpa only [h7, h8, h9] using flags_self rf
  refine ⟨n, next, hn, state_invariant _ _ _ _ _, ?_, ?_⟩
  · simp [SubexpNormalizeProgram.FilterEffect, keep, next, newOutput, state]
  · simpa only [next, record_state, hflags] using he

abbrev scan : Cmd 10 9 := RecordPrograms.iterate ports callback

theorem budget_le (C H : List (List Bool)) :
    3 + RecordPrograms.budget (callbackCost H) C ≤
      80 * ((Encoding.encodeList id H).length + 1) * ((Encoding.encodeList id C).length + 1) := by
  induction C with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]; omega
  | cons x xs ih =>
    simp only [RecordPrograms.budget, callbackCost, Encoding.length_encodeList_cons, id_eq]
    nlinarith

theorem scan_eval (C H acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 80 * ((Encoding.encodeList id H).length + 1) *
        ((Encoding.encodeList id C).length + 1), ∃ rf : Regs,
      Eval scan n
        (state regs (Encoding.encodeList id C) [] (Encoding.encodeList id acc) []
          (Encoding.encodeList id H))
        (state rf [] [] (Encoding.encodeList id ((result C H).reverse ++ acc)) []
          (Encoding.encodeList id H)) := by
  let d := state regs (Encoding.encodeList id C) [] (Encoding.encodeList id acc) []
    (Encoding.encodeList id H)
  obtain ⟨n, next, hn, hnext, hout, he⟩ := SubexpNormalizeProgram.filter_iterate_run
    ports callback (keep H) (callbackCost H) (invariant H) 2 (by decide) (by decide)
    (callback_contract H) C acc [] d (state_invariant _ _ _ _ _) rfl
    (regs 7) (regs 8) (regs 9)
  obtain ⟨rf, source, output, payload, rfl⟩ := hnext
  have hout' : output = Encoding.encodeList id ((result C H).reverse ++ acc) := by
    simpa [RecordPrograms.state, ports, state, result_eq_filter_keep] using hout
  refine ⟨n, hn.trans (budget_le C H), flags rf false true false, ?_⟩
  simpa only [d, record_state, flags_self, List.append_nil, hout'] using he

abbrev reverseCall : Cmd 10 9 :=
  .call (ProgramLinking.liftProgram ExecLiteralDedupProgram.reverseProgram id lowStack)

theorem reverse_eval (records acc : List (List Bool)) (regs : Regs) (core : List Bool) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ rf : Regs,
      Eval reverseCall n
        (state regs (Encoding.encodeList id acc) [] (Encoding.encodeList id records) [] core)
        (state rf (Encoding.encodeList id (records.reverse ++ acc)) [] [] [] core) := by
  let d := smallState regs (Encoding.encodeList id acc) [] (Encoding.encodeList id records) []
  obtain ⟨n, hn, e, he, h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    ExecLiteralDedupProgram.reverseCall_eval records acc d rfl rfl rfl
  have heq : e = smallState e.regs (Encoding.encodeList id (records.reverse ++ acc)) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [smallState, h0, h1, h2, h3, h4, h5, h6, h7, d]
  have ht : Trace ExecLiteralDedupProgram.reverseProgram n
      (d.withPC (some ExecLiteralDedupProgram.reverseProgram.entry)) (e.withPC none) := by
    cases he with
    | call _ h => exact h
  rw [heq] at ht
  have h := eval_call_lifted ExecLiteralDedupProgram.reverseProgram id lowStack
    (state regs (Encoding.encodeList id acc) [] (Encoding.encodeList id records) [] core)
    Function.injective_id lowStack_injective ht
  change Eval reverseCall n (embedState id lowStack _
    (smallState regs (Encoding.encodeList id acc) [] (Encoding.encodeList id records) [])) _ at h
  rw [embed_small_state, embed_small_state] at h
  exact ⟨n, hn, e.regs, h⟩

abbrev pushFalse (port : Fin 9) : Cmd 10 9 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push port 0))

def pushed (port : Fin 9) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks port (false :: d.stacks port)⟩

theorem pushFalse_eval (port : Fin 9) (d : Data) : Eval (pushFalse port) 2 d (pushed port d) := by
  have h := Eval.seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 10) (s := 9) 0 false) d))
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 10) (s := 9) port 0)
      ((StructuredProgram.Atom.set 0 false).eval d)))
  exact h

theorem pushOutput_eval (regs : Regs) (source output core : List Bool) :
    Eval (pushFalse 2) 2 (state regs source [] output [] core)
      (state (Function.update regs 0 false) source [] (false :: output) [] core) := by
  have h := pushFalse_eval 2 (state regs source [] output [] core)
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ state]

theorem pushSource_eval (regs : Regs) (source output core : List Bool) :
    Eval (pushFalse 0) 2 (state regs source [] output [] core)
      (state (Function.update regs 0 false) (false :: source) [] output [] core) := by
  have h := pushFalse_eval 0 (state regs source [] output [] core)
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ state]

abbrev command : Cmd 10 9 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

theorem command_eval (C H : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 100 * ((Encoding.encodeList id H).length + 1) *
        ((Encoding.encodeList id C).length + 1), ∃ rf : Regs,
      Eval command n (state regs (Encoding.encodeList id C) [] [] [] (Encoding.encodeList id H))
        (state rf (Encoding.encodeList id (result C H)) [] [] [] (Encoding.encodeList id H)) := by
  obtain ⟨n, hn, rf, hs⟩ := scan_eval C H [] (Function.update regs 0 false)
  simp only [List.append_nil] at hs
  obtain ⟨m, hm, final, hr⟩ := reverse_eval (result C H).reverse []
    (Function.update rf 0 false) (Encoding.encodeList id H)
  simp only [List.reverse_reverse, List.append_nil] at hr
  rw [ExecLiteralDedupProgram.encoded_reverse_length] at hm
  have hlen : (Encoding.encodeList id (result C H)).length ≤
      (Encoding.encodeList id C).length := result_encoded_length_le id C H
  refine ⟨2 + (n + (2 + m)), ?_, final, ?_⟩
  · nlinarith
  · exact (pushOutput_eval regs (Encoding.encodeList id C) [] (Encoding.encodeList id H)).seq
      (hs.seq ((pushSource_eval rf [] (Encoding.encodeList id (result C H).reverse)
        (Encoding.encodeList id H)).seq hr))

def program := compiled command 0 0

theorem program_runsIn (C H : List (List Bool)) (regs : Regs) :
    ∃ rf : Regs, RunsIn program
      (101 * ((Encoding.encodeList id H).length + 1) * ((Encoding.encodeList id C).length + 1))
      ((state regs (Encoding.encodeList id C) [] [] [] (Encoding.encodeList id H)).withPC
        (some program.entry))
      ((state rf (Encoding.encodeList id (result C H)) [] [] [] (Encoding.encodeList id H)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval C H regs
  exact ⟨rf, n + 1, by nlinarith, compiled_halt_trace he 0 0⟩

end SubexponentialSAT.ExecPetalProgram

end OAI.Algorithms
