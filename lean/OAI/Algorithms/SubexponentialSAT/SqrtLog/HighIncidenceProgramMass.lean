import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramRecords
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual two-level record scan counting explicit scope entries. The ghost
payload decoder occurs only in the loop specification; the executable callback
uses the existing physical record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 5 4
abbrev Code := Cmd 5 4
abbrev encode := Encoding.encodeList (id : List Bool → List Bool)

def state (regs : Fin 5 → Bool) (source payload acc work : List Bool) : Data :=
  ⟨regs, ![source, payload, acc, work]⟩
def ports : RecordPrograms.Ports 5 4 :=
  ⟨2, 3, 4, 0, 1, by decide, by decide, by decide, by decide⟩
def parserRegs (regs : Fin 5 → Bool) (t p f : Bool) :=
  Function.update (Function.update (Function.update regs 2 t) 3 p) 4 f

theorem parser_state (regs : Fin 5 → Bool) (s p a w src pay : List Bool) (t pr f : Bool) :
    RecordPrograms.state ports (state regs s p a w) t pr f src pay =
      state (parserRegs regs t pr f) src pay a w := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> rfl

def registers : Fin 2 → Fin 5 := Fin.castAdd 3
def counterPorts : Fin 2 → Fin 4 := ![3, 2]
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem counterPorts_injective : Function.Injective counterPorts := by decide

def counter : Code := .call (ProgramLinking.liftProgram
  SubexpScopeCountSetup.counterProgram registers counterPorts)

theorem counter_eval (regs : Fin 5 → Bool) (records : List (List Bool)) (source acc : List Bool) :
    ∃ rf, Eval counter (SubexpSunflowerProgram.CountRecords.loopSteps records)
      (state regs source [] acc (encode records))
      (state rf source [] (List.replicate records.length true ++ acc) []) ∧
      (∀ i : Fin 5, 2 ≤ i.val → rf i = regs i) := by
  let a := state regs source [] acc (encode records)
  let out : State 2 2 := ⟨ParserProgram.pair false false,
    ParserProgram.pair [] (List.replicate records.length true ++ acc)⟩
  have ht := SubexpSunflowerProgram.CountRecords.loop_trace records [] acc (regs 0) (regs 1)
  simp only [List.append_nil] at ht
  have hp : projectState registers counterPorts a =
      (⟨ParserProgram.pair (regs 0) (regs 1), ParserProgram.pair (encode records) acc⟩ : State 2 2) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have ht' : Trace SubexpScopeCountSetup.counterProgram (SubexpSunflowerProgram.CountRecords.loopSteps records)
      ((projectState registers counterPorts a).withPC (some SubexpScopeCountSetup.counterProgram.entry))
      (out.withPC none) := by
    rw [hp]
    exact ht
  let b := embedState registers counterPorts a out
  have he := eval_call_from_state SubexpScopeCountSetup.counterProgram registers counterPorts a
    registers_injective counterPorts_injective ht'
  have hs (i : Fin 2) : b.stacks (counterPorts i) = out.stacks i :=
    embedState_stack _ _ _ _ counterPorts_injective i
  have hb : b = state b.regs source [] (List.replicate records.length true ++ acc) [] := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    fin_cases i
    · exact embedState_stack_frame registers counterPorts a out 0 (by decide)
    · exact embedState_stack_frame registers counterPorts a out 1 (by decide)
    · exact hs 1
    · exact hs 0
  refine ⟨b.regs, ?_, ?_⟩
  · change Eval counter _ a b at he
    rw [hb] at he
    exact he
  · intro i hi
    exact embedState_register_frame registers counterPorts a out i (by
      rintro ⟨j, hj⟩
      fin_cases j <;> subst i <;> simp [registers] at hi)

def transfer : Code := .call (StackRoutines.transferProgram 1 3 0 1)
def callback : Code := .seq transfer counter

theorem callback_eval (regs : Fin 5 → Bool) (records : List (List Bool)) (source acc : List Bool) :
    ∃ rf, Eval callback
      (3 * (encode records).length + 3 + SubexpSunflowerProgram.CountRecords.loopSteps records)
      (state regs source (encode records).reverse acc [])
      (state rf source [] (List.replicate records.length true ++ acc) []) ∧
      (∀ i : Fin 5, 2 ≤ i.val → rf i = regs i) := by
  let r := readRegs regs 0 1 none
  have htransfer : Eval transfer (3 * (encode records).length + 3)
      (state regs source (encode records).reverse acc [])
      (state r source [] acc (encode records)) := by
    have h := ListRegisterProgram.transfer_run (1 : Fin 4) 3 (0 : Fin 5) 1
      (by decide) (by decide) regs (state regs source (encode records).reverse acc []).stacks
    have hs : StackRoutines.transferStacks 1 3
        (state regs source (encode records).reverse acc []).stacks =
        (state r source [] acc (encode records)).stacks := by
      funext i
      fin_cases i <;> simp [state, StackRoutines.transferStacks]
    apply Eval.call
    change Trace (StackRoutines.transferProgram 1 3 0 1) _
      ((state regs source (encode records).reverse acc []).withPC
        (some (StackRoutines.transferProgram 1 3 0 1).entry))
      ((⟨r, StackRoutines.transferStacks 1 3
        (state regs source (encode records).reverse acc []).stacks⟩ : Data).withPC none) at h
    rw [hs] at h
    simpa [state] using h
  obtain ⟨rf, hc, hr⟩ := counter_eval r records source acc
  refine ⟨rf, htransfer.seq hc, ?_⟩
  intro i hi
  rw [hr i hi]
  have h0 : i ≠ 0 := by intro h; subst i; contradiction
  have h1 : i ≠ 1 := by intro h; subst i; contradiction
  simp [r, readRegs, h0, h1]

noncomputable def payloadCount (bits : List Bool) : ℕ := by
  classical
  exact if h : ∃ rs, encode rs = bits then (Classical.choose h).length else 0

theorem payloadCount_encode (records : List (List Bool)) :
    payloadCount (encode records) = records.length := by
  classical
  unfold payloadCount
  split
  · rename_i h
    exact congrArg List.length (Encoding.encodeList_injective Function.injective_id
      (Classical.choose_spec h))
  · rename_i h
    exact (h ⟨records, rfl⟩).elim

def invariant (d : Data) : Prop := ∃ regs acc, d = state regs [] [] acc []
noncomputable def update (bits acc : List Bool) := List.replicate (payloadCount bits) true ++ acc
def read (d : Data) := d.stacks 2

theorem callback_contract : LeafProgram.FoldContract ports callback read update
    (fun bits => 6 * bits.length + 5) invariant (fun bits => ∃ rs, encode rs = bits) := by
  rintro bits tail base ⟨records, rfl⟩ ⟨regs, acc, rfl⟩
  obtain ⟨rf, he, hr⟩ := callback_eval (parserRegs regs false true false) records tail acc
  have h2 : rf 2 = false := by simpa [parserRegs] using hr 2 (by decide)
  have h3 : rf 3 = true := by simpa [parserRegs] using hr 3 (by decide)
  have h4 : rf 4 = false := by simpa [parserRegs] using hr 4 (by decide)
  have hreset : parserRegs rf false true false = rf := by
    funext i
    fin_cases i <;> simp [parserRegs, h2, h3, h4]
  refine ⟨3 * (encode records).length + 3 + SubexpSunflowerProgram.CountRecords.loopSteps records,
    state rf [] [] (List.replicate records.length true ++ acc) [], ?_,
    ⟨rf, _, rfl⟩, ?_, ?_⟩
  · have h := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    dsimp [SubexpSunflowerProgram.CountRecords.steps] at h
    change 3 * (Encoding.encodeList id records).length + 3 +
      SubexpSunflowerProgram.CountRecords.loopSteps records ≤
      6 * (Encoding.encodeList id records).length + 5
    omega
  · simp [LeafProgram.foldEffect, read, update, payloadCount_encode, state]
  · rw [parser_state, parser_state, hreset]
    exact he

def program := LeafProgram.foldProgram ports callback

theorem fold_update (records : List (List (List Bool))) (acc : List Bool) :
    (records.map encode).foldl (fun a bits => update bits a) acc =
      List.replicate ((records.map List.length).sum) true ++ acc := by
  induction records generalizing acc with
  | nil => simp
  | cons rs rss ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]
      simp only [update, payloadCount_encode, List.sum_cons]
      rw [Nat.add_comm rs.length, List.replicate_add, List.append_assoc]

theorem program_runsIn (regs : Fin 5 → Bool) (records : List (List (List Bool))) :
    ∃ rf, RunsIn program
      (4 + RecordPrograms.budget (fun bits => 6 * bits.length + 5) (records.map encode))
      ((RecordPrograms.state ports (state regs [] [] [] []) false true false
        (encode (records.map encode)) []).withPC (some program.entry))
      ((state rf [] [] (List.replicate ((records.map List.length).sum) true) []).withPC none) := by
  obtain ⟨next, hn, hv, he⟩ := LeafProgram.foldProgram_run ports callback read update
    (fun bits => 6 * bits.length + 5) invariant (fun bits => ∃ rs, encode rs = bits)
    callback_contract (records.map encode) [] (state regs [] [] [] [])
    (by intro bits hb; obtain ⟨rs, _, rfl⟩ := List.mem_map.mp hb; exact ⟨rs, rfl⟩)
    ⟨regs, [], rfl⟩ false true false
  obtain ⟨rf, acc, rfl⟩ := hn
  have hacc : acc = List.replicate ((records.map List.length).sum) true := by
    simpa [read, state, fold_update] using hv
  subst acc
  refine ⟨parserRegs rf false true false, ?_⟩
  simpa only [List.append_nil, parser_state, program] using he

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
