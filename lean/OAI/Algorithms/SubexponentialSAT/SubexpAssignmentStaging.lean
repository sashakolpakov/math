import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAssignmentStagingCore
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentFrontendProgram

namespace OAI.Algorithms

/-! Actual assignment frontend invocation with retained runtime outputs. -/

namespace SubexponentialSAT.SubexpAssignmentStaging

open BitProgram StructuredCalls SubexpSetupStorage SubexpAssignmentSetup
open SubexpPreparedSetupCalls (StackBound)
open Subexp

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

theorem prepared_project (a b : Data) (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (hb : b.stacks = preparedWords a.stacks scopes)
    (hv : ∀ i, CounterPrograms.value (a.stacks (source i)) = (![r, Q, Δ, D] : Fin 4 → ℕ) i) :
    project id callee b = AssignmentPairFrontend.inputState b.regs r Q Δ D scopes := by
  have h0 : CounterPrograms.value (a.stacks 51) = r := hv 0
  have h1 : CounterPrograms.value (a.stacks 52) = Q := hv 1
  have h2 : CounterPrograms.value (a.stacks 53) = Δ := hv 2
  have h3 : CounterPrograms.value (a.stacks 54) = D := hv 3
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    change b.stacks (callee j) = _
    rw [hb]
    fin_cases j <;> simp [preparedWords, seedWords, callee, source,
      AssignmentPairFrontend.unary, clearedPorts, mem_scratch, h0, h1, h2, h3,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod]

noncomputable abbrev frontend : Command :=
  @invoke 16 48 (size AssignmentFrontendProgram.command + 1) 63
    AssignmentFrontendProgram.program id callee
noncomputable abbrev command : Command := .seq preparation (.seq saveHeaders (.seq frontend finish))
noncomputable abbrev program : Program 16 63 (size command + 1) := compiled command 55 56

def prefixBudget (a : Data) (r Q Δ D : ℕ) (scopes : List (List ℕ)) : ℕ :=
  preparationBudget a scopes + 4 * (7 * (r + Q + Δ + D) + 5) +
    AssignmentFrontendProgram.sourceBudget r Q Δ D scopes

def runtimeBound (a : Data) (r Q Δ D : ℕ) (scopes : List (List ℕ)) : ℕ :=
  prefixBudget a r Q Δ D scopes +
    200 * (wordBound a + prefixBudget a r Q Δ D scopes + 2) + 1

def assignedBytes {r Q : ℕ} (Δ D : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q)) : List Bool :=
  ((NaturalAssignment.naturalValues
    (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
    first tail (List.finRange D)
    (AssignmentEnumeration.seedIndices (List.finRange D) (List.finRange scopes.length) Δ)).reverse.map
      ReadPlan.encodeWord).flatten

structure Result (a b : Data) (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q)) : Prop where
  wordOrder : (first :: tail).map ReadPlan.encodeWord = AssignmentAlphabetSemantics.wordBytes r Q
  assignment : b.stacks 56 = assignedBytes Δ D scopes hd first tail
  alphabet : b.stacks 57 = ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q)
  width : (b.stacks 58).length = Q * r
  inputs : ∀ i, b.stacks (input i) = a.stacks (input i)
  headers : ∀ i, b.stacks (headerTarget i) =
    List.replicate ((![r, Q, Δ, D] : Fin 4 → ℕ) i) true
  scratch : ∀ j : Fin 63, j.val < 51 → b.stacks j = []
  registers : ∀ j, b.regs j = false

theorem run (a : Data) (r Q Δ D : ℕ) [NeZero r] (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (hv : ∀ i, CounterPrograms.value (a.stacks (source i)) = (![r, Q, Δ, D] : Fin 4 → ℕ) i)
    (hs : a.stacks 55 = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ first : MulticolorTypes.Word r Q, ∃ tail : List (MulticolorTypes.Word r Q), ∃ b : Data,
      (first :: tail).Nodup ∧ (∀ w, w ∈ first :: tail) ∧
      RunsIn program (runtimeBound a r Q Δ D scopes)
        (a.withPC (some program.entry)) (b.withPC none) ∧ Result a b r Q Δ D scopes hd first tail := by
  obtain ⟨n, prepared, hp, hn, hwords⟩ := preparation_eval a scopes hs
  have hproject := prepared_project a prepared r Q Δ D scopes hwords hv
  have hheaders (i : Fin 4) : prepared.stacks (destination i) =
      List.replicate ((![r, Q, Δ, D] : Fin 4 → ℕ) i) true := by
    rw [hwords]
    have h0 : CounterPrograms.value (a.stacks 51) = r := hv 0
    have h1 : CounterPrograms.value (a.stacks 52) = Q := hv 1
    have h2 : CounterPrograms.value (a.stacks 53) = Δ := hv 2
    have h3 : CounterPrograms.value (a.stacks 54) = D := hv 3
    fin_cases i <;> simp [preparedWords, seedWords, destination, source, clearedPorts,
      mem_scratch, h0, h1, h2, h3, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  have h48prepared : prepared.stacks 48 = [] := by
    rw [hwords]; exact prepared_empty _ _ _ (Or.inl rfl)
  have hheaderBlank : ∀ p ∈ headerPairs, prepared.stacks p.2 = [] := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    rw [hwords]
    apply prepared_empty
    right; right; right
    simp only [headerTarget]
    omega
  let saved := copyManyState headerPairs prepared
  have hsave := copyMany_eval 48 headerPairs prepared headerPairs_good h48prepared
  have hsaveCost : copyManyCost headerPairs prepared ≤ 4 * (7 * (r + Q + Δ + D) + 5) := by
    have h := SubexpPreparedSetupCalls.copyManyCost_le headerPairs prepared (W := r + Q + Δ + D)
      (by
        intro p hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
        rw [hheaders, List.length_replicate]
        fin_cases i <;> simp <;> omega) headerPairs_separated
    simpa [headerPairs] using h
  have hsavedHeader (i : Fin 4) : saved.stacks (headerTarget i) =
      List.replicate ((![r, Q, Δ, D] : Fin 4 → ℕ) i) true := by
    exact (SubexpSetupStorage.copyMany_value headerPairs prepared headerPairs_nodup hheaderBlank
      headerPairs_separated (destination i, headerTarget i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).trans (hheaders i)
  have hsavedProject : project id callee saved =
      AssignmentPairFrontend.inputState saved.regs r Q Δ D scopes := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      change saved.stacks (callee j) = _
      rw [headerCopy_frame prepared _ (by have := j.isLt; simp only [callee, Fin.val_castAdd]; omega)]
      exact congrFun (congrArg StructuredProgram.State.stacks hproject) j
  obtain ⟨first, tail, e, hnodup, hfull, horder, ⟨t, ht, htrace⟩, hassigned, hready⟩ :=
    AssignmentFrontendProgram.program_run_framed saved.regs r Q Δ D scopes hd
  rw [← hsavedProject] at htrace
  have hfront := invoke_eval AssignmentFrontendProgram.program id callee
    Function.injective_id callee_injective saved e htrace
  let middle := embedState id callee saved e
  have hlow (i : Fin 48) : middle.stacks (callee i) = e.stacks i :=
    embedState_stack id callee saved e callee_injective i
  have hhigh (j : Fin 63) (hj : 48 ≤ j.val) : middle.stacks j = saved.stacks j := by
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    have hval := congrArg (fun z : Fin 63 => z.val) hi
    have hilow := i.isLt
    change i.val = j.val at hval
    omega
  have hprefix := hp.seq (hsave.seq hfront)
  have hprefixBound : n + (copyManyCost headerPairs prepared + t) ≤ prefixBudget a r Q Δ D scopes := by
    unfold prefixBudget
    omega
  let W := wordBound a + prefixBudget a r Q Δ D scopes + 1
  have hm : StackBound middle W := by
    intro j
    have h := SequentialProgram.trace_stack_length_le (compiled_halt_trace hprefix 55 56) j
    have hi := wordBound_spec a j
    change (middle.stacks j).length ≤ (a.stacks j).length +
      (n + (copyManyCost headerPairs prepared + t) + 1) at h
    dsimp [W]
    omega
  have h48 : middle.stacks 48 = [] := by
    rw [hhigh 48 (by decide), headerCopy_frame prepared _ (by decide)]
    exact h48prepared
  have hblank : ∀ i, middle.stacks (outputTarget i) = [] := by
    intro i
    rw [hhigh _ (by fin_cases i <;> decide),
      headerCopy_frame prepared _ (by fin_cases i <;> decide), hwords]
    apply prepared_empty
    right; right; right
    fin_cases i <;> decide
  obtain ⟨u, b, hfinish, hu, _, hresult⟩ := finish_eval middle W hm h48 hblank
  refine ⟨first, tail, b, hnodup, hfull, ⟨n + (copyManyCost headerPairs prepared + (t + u)) + 1, ?_, ?_⟩, ?_⟩
  · dsimp [runtimeBound, W] at *
    omega
  · exact compiled_halt_trace (hp.seq (hsave.seq (hfront.seq hfinish))) 55 56
  · constructor
    · exact horder
    · exact (hresult.outputs 0).trans ((hlow 8).trans hassigned)
    · have halphabet := hready.2.2.2.2 30 (by decide)
      have he : e.stacks 30 = ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q) := by
        simpa [ScoreBuilderProgram.environment, AssignmentInputProgram.context] using halphabet
      exact (hresult.outputs 1).trans ((hlow 30).trans he)
    · have he := hready.2.1
      have he' : (e.stacks 10).length = Q * r := by
        simpa [AssignmentInputProgram.context, AssignmentInputProgram.unary] using he
      exact (congrArg List.length ((hresult.outputs 2).trans (hlow 10))).trans he'
    · intro i
      rw [hresult.inputs, hhigh _ (by simp only [input]; omega),
        headerCopy_frame prepared _ (by have := i.isLt; simp only [input]; omega),
        hwords, prepared_input]
    · intro i
      rw [hresult.headers, hhigh _ (by simp only [headerTarget]; omega), hsavedHeader]
    · exact hresult.scratch
    · exact hresult.registers

end SubexponentialSAT.SubexpAssignmentStaging

end OAI.Algorithms
