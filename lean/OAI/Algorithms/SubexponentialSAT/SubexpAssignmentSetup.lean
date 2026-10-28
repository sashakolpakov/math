import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds
import OAI.Algorithms.SubexponentialSAT.SubexpPlanAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! Runtime binary metadata and encoded scopes are physically converted to
the six input words of the assignment frontend. -/

namespace SubexponentialSAT.SubexpAssignmentSetup

open BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := State 16 63
abbrev Command := Cmd 16 63

def source (i : Fin 4) : Fin 63 := ⟨51 + i.val, by omega⟩
def destination (i : Fin 4) : Fin 63 := ⟨1 + i.val, by omega⟩
def callee (i : Fin 48) : Fin 63 := i.castAdd 15
def scratch : List (Fin 63) := List.ofFn (fun i : Fin 51 => i.castAdd 12)
def clearedPorts : List (Fin 63) := scratch ++ [56, 57, 58, 59, 60, 61, 62]

def ScratchClear (a : Data) : Prop :=
  a.stacks 48 = [] ∧ a.stacks 49 = [] ∧ a.stacks 50 = []

theorem callee_injective : Function.Injective callee := Fin.castAdd_injective 48 15

theorem mem_scratch (j : Fin 63) : j ∈ scratch ↔ j.val < 51 := by
  simp only [scratch, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩; exact i.isLt
  · intro hj; exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩

def unaryRegisters : Fin 3 → Fin 16 := Fin.castAdd 13
def unaryPorts (i : Fin 4) : Fin 3 → Fin 63 := ![49, destination i, 50]

theorem unaryRegisters_injective : Function.Injective unaryRegisters := Fin.castAdd_injective 3 13
theorem unaryPorts_injective (i : Fin 4) : Function.Injective (unaryPorts i) := by
  fin_cases i <;> decide

def unaryAt (i : Fin 4) : Command :=
  .seq (copyCmd (source i) 49 48)
    (invoke CounterConversions.unaryProgram unaryRegisters (unaryPorts i))

def unaryBudget (bits : List Bool) : ℕ :=
  7 * bits.length + 5 + CounterConversions.runtimeBound bits

theorem unaryAt_eval (i : Fin 4) (a : Data) (hc : ScratchClear a)
    (hd : a.stacks (destination i) = []) :
    ∃ n b, Eval (unaryAt i) n a b ∧ n ≤ unaryBudget (a.stacks (source i)) ∧
      b.stacks = Function.update a.stacks (destination i)
        (List.replicate (CounterPrograms.value (a.stacks (source i))) true) ∧
      ScratchClear b := by
  let c := copyState (source i) 49 a
  let out := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (a.stacks (source i))) true)
  have hp : project unaryRegisters (unaryPorts i) c =
      CounterConversions.state (c.regs ∘ unaryRegisters) (a.stacks (source i)) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> fin_cases i <;>
        simp_all [unaryPorts, source, destination, c, copyState,
          StackRoutines.copyStacks, ScratchClear]
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs
    (c.regs ∘ unaryRegisters) (a.stacks (source i)) []
  simp only [List.append_nil] at ht
  rw [← hp] at ht
  have he := invoke_eval CounterConversions.unaryProgram unaryRegisters (unaryPorts i)
    unaryRegisters_injective (unaryPorts_injective i) c out ht
  let b := embedState unaryRegisters (unaryPorts i) c out
  have hs : b.stacks = Function.update a.stacks (destination i)
      (List.replicate (CounterPrograms.value (a.stacks (source i))) true) := by
    funext j
    by_cases hdj : j = destination i
    · subst j
      have h := embedState_stack unaryRegisters (unaryPorts i) c out (unaryPorts_injective i) 1
      simpa [b, unaryPorts, out, CounterConversions.state] using h
    by_cases h49 : j = 49
    · subst j
      have h := embedState_stack unaryRegisters (unaryPorts i) c out (unaryPorts_injective i) 0
      simpa [b, unaryPorts, out, CounterConversions.state, hdj, hc.2.1] using h
    by_cases h50 : j = 50
    · subst j
      have h := embedState_stack unaryRegisters (unaryPorts i) c out (unaryPorts_injective i) 2
      simpa [b, unaryPorts, out, CounterConversions.state, hdj, hc.2.2] using h
    · have hframe : ¬ ∃ k, unaryPorts i k = j := by
        rintro ⟨k, hk⟩
        fin_cases k
        · exact h49 hk.symm
        · exact hdj hk.symm
        · exact h50 hk.symm
      change (embedState unaryRegisters (unaryPorts i) c out).stacks j = _
      rw [embedState_stack_frame _ _ _ _ _ hframe]
      simp [c, copyState, StackRoutines.copyStacks, h49, hdj]
  have hcopy := copy_eval (source i) 49 48 a
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by decide) hc.1
  refine ⟨7 * (a.stacks (source i)).length + 5 + n, b, hcopy.seq he, ?_, hs, ?_⟩
  · exact Nat.add_le_add_left hn _
  · rcases hc with ⟨h48, h49, h50⟩
    dsimp [ScratchClear]
    rw [hs]
    fin_cases i <;> simp [destination, h48, h49, h50, Fin.ext_iff, Fin.coe_ofNat_eq_mod]

def scopeRecords (scopes : List (List ℕ)) : List (List Bool) :=
  scopes.map SubexpIncidencePlanScan.scopeBytes

theorem scopeRecords_encode (scopes : List (List ℕ)) :
    Encoding.encodeList id (scopeRecords scopes) = SubexpPlanAlphabetBase.scopeBytes scopes := by
  induction scopes with
  | nil => rfl
  | cons x xs ih =>
      simp only [scopeRecords, List.map_cons, SubexpPlanAlphabetBase.scopeBytes,
        Encoding.encodeList, id_eq] at *
      rw [ih]

def countRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def countPorts : Fin 15 → Fin 63 := ![0,55,5,3,4,48,6,7,8,9,10,11,12,13,49]

theorem countRegisters_injective : Function.Injective countRegisters := Fin.castAdd_injective 8 8
theorem countPorts_injective : Function.Injective countPorts := by decide

def countScopes : Command := liftCommand SubexpScopeCountSetup.countCommand 1 2
  countRegisters countPorts

def countBudget (scopes : List (List ℕ)) : ℕ :=
  SubexpScopeCountSetup.countBudget (scopeRecords scopes) + 1

theorem countScopes_eval (scopes : List (List ℕ)) (a : Data) (hc : ScratchClear a)
    (h5 : a.stacks 5 = []) (hs : a.stacks 55 = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ b, Eval countScopes (countBudget scopes) a b ∧
      b.stacks = Function.update a.stacks 5 (List.replicate scopes.length true) ∧ ScratchClear b := by
  let d := projectState countRegisters countPorts a
  obtain ⟨rf, ht⟩ := SubexpScopeCountSetup.count_eval (scopeRecords scopes) d
    (by simpa [d, projectState, countPorts, scopeRecords_encode] using hs)
    (by simpa [d, projectState, countPorts] using h5)
    (by simpa [d, projectState, countPorts] using hc.1)
    (by simpa [d, projectState, countPorts] using hc.2.1)
  let out : State 8 15 := ⟨rf, Function.update d.stacks 2
    (List.replicate (scopeRecords scopes).length true)⟩
  let b := embedState countRegisters countPorts a out
  have he := eval_liftCommand_from_state SubexpScopeCountSetup.countCommand 1 2
    countRegisters countPorts a countRegisters_injective countPorts_injective ht
  have hb : b.stacks = Function.update a.stacks 5 (List.replicate scopes.length true) := by
    change Function.extend countPorts (Function.update (a.stacks ∘ countPorts) 2
      (List.replicate (scopeRecords scopes).length true)) a.stacks = _
    rw [ProgramLinking.extend_update countPorts_injective]
    have hproject := congrArg StructuredProgram.State.stacks
      (embedState_project countRegisters countPorts a countRegisters_injective countPorts_injective)
    change Function.extend countPorts (a.stacks ∘ countPorts) a.stacks = a.stacks at hproject
    rw [hproject]
    simp [countPorts, scopeRecords]
  refine ⟨b, he, hb, ?_⟩
  rcases hc with ⟨h48, h49, h50⟩
  simp [ScratchClear, hb, h48, h49, h50]

def seed : Command :=
  .seq (unaryAt 0) (.seq (unaryAt 1) (.seq (unaryAt 2)
    (.seq (unaryAt 3) (.seq countScopes (copyCmd 55 6 48)))))

def seedBudget (a : Data) (scopes : List (List ℕ)) : ℕ :=
  unaryBudget (a.stacks (source 0)) + unaryBudget (a.stacks (source 1)) +
    unaryBudget (a.stacks (source 2)) + unaryBudget (a.stacks (source 3)) +
    countBudget scopes + 7 * (SubexpPlanAlphabetBase.scopeBytes scopes).length + 5

def seedWords (old : Fin 63 → List Bool) (scopes : List (List ℕ)) : Fin 63 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update old 1 (List.replicate (CounterPrograms.value (old (source 0))) true))
    2 (List.replicate (CounterPrograms.value (old (source 1))) true))
    3 (List.replicate (CounterPrograms.value (old (source 2))) true))
    4 (List.replicate (CounterPrograms.value (old (source 3))) true))
    5 (List.replicate scopes.length true)) 6 (SubexpPlanAlphabetBase.scopeBytes scopes)

theorem seed_eval (a : Data) (scopes : List (List ℕ))
    (hc : ∀ j : Fin 63, j.val < 51 → a.stacks j = [])
    (hs : a.stacks 55 = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ n b, Eval seed n a b ∧ n ≤ seedBudget a scopes ∧ b.stacks = seedWords a.stacks scopes := by
  have hclear : ScratchClear a := ⟨hc 48 (by decide), hc 49 (by decide), hc 50 (by decide)⟩
  obtain ⟨n1, a1, e1, b1, c1, s1⟩ := unaryAt_eval 0 a hclear (hc 1 (by decide))
  obtain ⟨n2, a2, e2, b2, c2, s2⟩ := unaryAt_eval 1 a1 s1 (by
    simpa [c1, destination] using hc 2 (by decide))
  obtain ⟨n3, a3, e3, b3, c3, s3⟩ := unaryAt_eval 2 a2 s2 (by
    simpa [c2, c1, destination] using hc 3 (by decide))
  obtain ⟨n4, a4, e4, b4, c4, s4⟩ := unaryAt_eval 3 a3 s3 (by
    simpa [c3, c2, c1, destination] using hc 4 (by decide))
  obtain ⟨a5, e5, c5, s5⟩ := countScopes_eval scopes a4 s4
    (by simpa [c4, c3, c2, c1, destination] using hc 5 (by decide))
    (by simpa [c4, c3, c2, c1, destination] using hs)
  have h6 : a5.stacks 6 = [] := by
    simpa [c5, c4, c3, c2, c1, destination] using hc 6 (by decide)
  have h55 : a5.stacks 55 = SubexpPlanAlphabetBase.scopeBytes scopes := by
    simpa [c5, c4, c3, c2, c1, destination] using hs
  have e6 := copy_eval (55 : Fin 63) 6 48 a5 (by decide) (by decide) (by decide) s5.1
  refine ⟨n1 + (n2 + (n3 + (n4 + (countBudget scopes +
    (7 * (a5.stacks 55).length + 5))))), copyState 55 6 a5,
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6)))), ?_, ?_⟩
  · have b2' : n2 ≤ unaryBudget (a.stacks (source 1)) := by
      simpa [c1, destination, source, Fin.ext_iff, Fin.coe_ofNat_eq_mod] using b2
    have b3' : n3 ≤ unaryBudget (a.stacks (source 2)) := by
      simpa [c2, c1, destination, source, Fin.ext_iff, Fin.coe_ofNat_eq_mod] using b3
    have b4' : n4 ≤ unaryBudget (a.stacks (source 3)) := by
      simpa [c3, c2, c1, destination, source, Fin.ext_iff, Fin.coe_ofNat_eq_mod] using b4
    unfold seedBudget
    rw [h55]
    omega
  · simp only [copyState_stack, h6, h55, List.append_nil]
    funext j
    simp [c5, c4, c3, c2, c1, seedWords, source, destination,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod]

def preparation : Command := .seq (clearMany clearedPorts) seed

def preparedWords (old : Fin 63 → List Bool) (scopes : List (List ℕ)) :=
  seedWords (fun j => if j ∈ clearedPorts then [] else old j) scopes

def preparationBudget (a : Data) (scopes : List (List ℕ)) : ℕ :=
  clearManyCost clearedPorts a + seedBudget a scopes

theorem preparation_eval (a : Data) (scopes : List (List ℕ))
    (hs : a.stacks 55 = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ n b, Eval preparation n a b ∧ n ≤ preparationBudget a scopes ∧
      b.stacks = preparedWords a.stacks scopes := by
  let c := clearManyState clearedPorts a
  have hc : ∀ j : Fin 63, j.val < 51 → c.stacks j = [] := by
    intro j hj
    simp [c, clearMany_stacks, clearedPorts, (mem_scratch j).mpr hj]
  have hs' : c.stacks 55 = SubexpPlanAlphabetBase.scopeBytes scopes := by
    simpa [c, clearMany_stacks, clearedPorts, mem_scratch] using hs
  obtain ⟨n, b, he, hn, hb⟩ := seed_eval c scopes hc hs'
  refine ⟨clearManyCost clearedPorts a + n, b, (clearMany_eval clearedPorts a).seq he, ?_, ?_⟩
  · have hcost : seedBudget c scopes = seedBudget a scopes := by
      simp [seedBudget, c, clearMany_stacks, clearedPorts, mem_scratch, source,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod]
    rw [hcost] at hn
    exact Nat.add_le_add_left hn _
  · exact hb.trans (congrArg (fun stk => seedWords stk scopes)
      (funext fun j => clearMany_stacks clearedPorts a j))

end SubexponentialSAT.SubexpAssignmentSetup

end OAI.Algorithms
