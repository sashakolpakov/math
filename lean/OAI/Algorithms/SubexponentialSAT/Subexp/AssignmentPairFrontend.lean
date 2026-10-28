import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpVertexPairProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputState
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-!
# Physical raw-pair input for assignment setup

The actual all-vertex pair producer runs in a fixed private bank. Two stack
transfers place its bytes, in their original order, on assignment input 45.
The scope source and private bank are then cleared by actual instructions.
-/

namespace SubexponentialSAT.Subexp.AssignmentPairFrontend

open BitProgram StructuredCalls

abbrev Data := State 16 48
abbrev Code := Cmd 16 48
abbrev unary (n : ℕ) := List.replicate n true

def registers : Fin 13 → Fin 16 := Fin.castAdd 3
def ports : Fin 25 → Fin 48 :=
  ![0,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,6,4,3,35,36,37,38,39,40]

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 13 3
theorem ports_injective : Function.Injective ports := by decide

def inputState (regs : Fin 16 → Bool) (r Q Δ D : ℕ) (scopes : List (List ℕ)) : Data :=
  ⟨regs, fun j => if j = 1 then unary r else if j = 2 then unary Q
    else if j = 3 then unary Δ else if j = 4 then unary D
    else if j = 5 then unary scopes.length else if j = 6 then
      SubexpPlanAlphabetBase.scopeBytes scopes else []⟩

def pairBytes (D Δ : ℕ) (scopes : List (List ℕ)) : List Bool :=
  ProgramEncoding.encodeRecords (SubexpVertexPairProgram.pairRows D Δ scopes)

def pairs : Code := .call
  (ProgramLinking.liftProgram SubexpVertexPairProgram.program registers ports)

def move : Code := .seq
  (.call (StackRoutines.transferProgram (0 : Fin 48) 7 (0 : Fin 16) 1))
  (.call (StackRoutines.transferProgram (7 : Fin 48) 45 (0 : Fin 16) 1))

def moved (d : Data) : Data :=
  ⟨readRegs (readRegs d.regs 0 1 none) 0 1 none,
    Function.update (Function.update (Function.update d.stacks 0 []) 7 []) 45 (d.stacks 0)⟩

def clearPorts : List (Fin 48) :=
  [6,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]

theorem clearPorts_length : clearPorts.length = 22 := rfl

theorem mem_clearPorts (j : Fin 48) :
    j ∈ clearPorts ↔ j = 6 ∨ (20 ≤ j.val ∧ j.val ≤ 40) := by
  fin_cases j <;> decide

def cleanup : Code := SequentialProgram.clearList clearPorts
def command : Code := .seq pairs (.seq move cleanup)
def program := compiled command 6 45

def Frame (a b : Data) : Prop :=
  ∀ j, j ≠ 0 → j ≠ 3 → j ≠ 4 → j ≠ 6 →
    (j.val < 20 ∨ 40 < j.val) → b.stacks j = a.stacks j

theorem pairs_eval (regs : Fin 16 → Bool) (r Q Δ D : ℕ)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ n b, n ≤ SubexpVertexPairProgram.bound D Δ scopes + 1 ∧
      Eval pairs n (inputState regs r Q Δ D scopes) b ∧
      b.stacks 0 = pairBytes D Δ scopes ∧
      b.stacks 3 = unary Δ ∧ b.stacks 4 = unary D ∧
      Frame (inputState regs r Q Δ D scopes) b := by
  obtain ⟨n, e, hn, ht, h0, _, hmasters⟩ :=
    SubexpVertexPairProgram.program_trace_framed (regs ∘ registers) D Δ scopes hd
  let a := inputState regs r Q Δ D scopes
  let b := embedState registers ports a e
  have ha : embedState registers ports a
      (SubexpPlanAlphabetBase.data (regs ∘ registers) D Δ scopes [] [] [] []) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i
      fin_cases i <;> simp [a, inputState, ports, SubexpPlanAlphabetBase.data]
    · intro i hi; rfl
  have he := eval_call_lifted SubexpVertexPairProgram.program registers ports a
    registers_injective ports_injective ht
  rw [ha] at he
  refine ⟨n, b, hn, he, ?_, ?_, ?_, ?_⟩
  · exact (embedState_stack registers ports a e ports_injective 0).trans h0
  · exact (embedState_stack registers ports a e ports_injective 18).trans hmasters.2.2
  · exact (embedState_stack registers ports a e ports_injective 17).trans hmasters.2.1
  · intro j h0j h3j h4j h6j hj
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    subst j
    fin_cases i <;> first
    | exact h0j rfl
    | exact h3j rfl
    | exact h4j rfl
    | exact h6j rfl
    | exact absurd hj (by decide)

theorem move_eval (d : Data) (h7 : d.stacks 7 = []) (h45 : d.stacks 45 = []) :
    Eval move (6 * (d.stacks 0).length + 6) d (moved d) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 0 7 d.stacks⟩
  have h1 := TupleProgram.transfer_eval (0 : Fin 48) 7 (0 : Fin 16) 1
    (by decide) (by decide) d
  have h2 := TupleProgram.transfer_eval (7 : Fin 48) 45 (0 : Fin 16) 1
    (by decide) (by decide) a
  have he : (⟨readRegs a.regs 0 1 none,
      StackRoutines.transferStacks 7 45 a.stacks⟩ : Data) = moved d := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases h0j : j = 0
      · subst j; simp [a, StackRoutines.transferStacks]
      by_cases h7j : j = 7
      · subst j; simp [a, StackRoutines.transferStacks]
      by_cases h45j : j = 45
      · subst j; simp [a, StackRoutines.transferStacks, h7, h45]
      · simp [a, StackRoutines.transferStacks, h0j, h7j, h45j]
  rw [he] at h2
  convert h1.seq h2 using 1 <;>
    simp [move, a, StackRoutines.transferStacks, h7] ; omega

def sourceBudget (D Δ : ℕ) (scopes : List (List ℕ)) : ℕ :=
  60 * (SubexpVertexPairProgram.bound D Δ scopes +
    (SubexpPlanAlphabetBase.scopeBytes scopes).length + 4)

theorem command_eval (regs : Fin 16 → Bool) (r Q Δ D : ℕ)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ n rf, n + 1 ≤ sourceBudget D Δ scopes ∧
      Eval command n (inputState regs r Q Δ D scopes)
        (AssignmentInputProgram.inputState rf r Q Δ D scopes.length (pairBytes D Δ scopes)) := by
  obtain ⟨n, b, hn, hb, h0, h3, h4, hf⟩ := pairs_eval regs r Q Δ D scopes hd
  dsimp only [Frame] at hf
  have h7 : b.stacks 7 = [] := by
    simpa [inputState] using hf 7 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h45 : b.stacks 45 = [] := by
    simpa [inputState] using hf 45 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hg (j : Fin 48) : (b.stacks j).length ≤
      ((inputState regs r Q Δ D scopes).stacks j).length + n + 1 := by
    have h := SequentialProgram.trace_stack_length_le (compiled_halt_trace hb 6 0) j
    simpa [StructuredProgram.State.withPC, Nat.add_assoc] using h
  have hlen : (b.stacks 0).length ≤ n + 1 := by simpa [inputState] using hg 0
  have hclean : ∀ j ∈ clearPorts, ((moved b).stacks j).length ≤
      (SubexpPlanAlphabetBase.scopeBytes scopes).length + n + 1 := by
    intro j hj
    have hj' := (mem_clearPorts j).mp hj
    have hj0 : j ≠ 0 := by intro h; subst j; exact absurd hj' (by decide)
    have hj7 : j ≠ 7 := by intro h; subst j; exact absurd hj' (by decide)
    have hj45 : j ≠ 45 := by intro h; subst j; exact absurd hj' (by decide)
    have hs : ((inputState regs r Q Δ D scopes).stacks j).length ≤
        (SubexpPlanAlphabetBase.scopeBytes scopes).length := by
      rcases hj' with h6 | hj'
      · subst j; simp [inputState]
      · have h1 : j ≠ 1 := by intro h; subst j; exact absurd hj' (by decide)
        have h2 : j ≠ 2 := by intro h; subst j; exact absurd hj' (by decide)
        have h3 : j ≠ 3 := by intro h; subst j; exact absurd hj' (by decide)
        have h4 : j ≠ 4 := by intro h; subst j; exact absurd hj' (by decide)
        have h5 : j ≠ 5 := by intro h; subst j; exact absurd hj' (by decide)
        have h6 : j ≠ 6 := by intro h; subst j; exact absurd hj' (by decide)
        simp [inputState, h1, h2, h3, h4, h5, h6]
    have hh := hg j
    simp only [moved, Function.update_of_ne hj45, Function.update_of_ne hj7,
      Function.update_of_ne hj0]
    omega
  obtain ⟨m, hm, e, he, hs⟩ := SequentialProgram.clearList_eval clearPorts (moved b)
    ((SubexpPlanAlphabetBase.scopeBytes scopes).length + n + 1) hclean
  have hout : e = AssignmentInputProgram.inputState e.regs r Q Δ D scopes.length
      (pairBytes D Δ scopes) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      rw [hs j]
      by_cases hj : j ∈ clearPorts
      · simp only [hj, ite_true]
        fin_cases j <;> first
        | exact absurd hj (by decide)
        | simp []
      · simp only [hj, ite_false]
        by_cases hj0 : j = 0
        · subst j; simp [moved]
        by_cases hj7 : j = 7
        · subst j; simp [moved]
        by_cases hj45 : j = 45
        · subst j; simp [moved, h0]
        by_cases hj3 : j = 3
        · subst j; simp [moved, h3]
        by_cases hj4 : j = 4
        · subst j; simp [moved, h4]
        have hj6 : j ≠ 6 := by intro h; subst j; simp [mem_clearPorts] at hj
        have hrange : j.val < 20 ∨ 40 < j.val := by
          have h : ¬(j = 6 ∨ (20 ≤ j.val ∧ j.val ≤ 40)) :=
            fun h => hj ((mem_clearPorts j).mpr h)
          omega
        simp only [moved, Function.update_of_ne hj45, Function.update_of_ne hj7,
          Function.update_of_ne hj0]
        rw [hf j hj0 hj3 hj4 hj6 hrange]
        simp [inputState, hj6, hj45]
  rw [hout] at he
  refine ⟨n + (6 * (b.stacks 0).length + 6 + m), e.regs, ?_, hb.seq ((move_eval b h7 h45).seq he)⟩
  rw [clearPorts_length] at hm
  unfold sourceBudget
  omega

theorem program_run (regs : Fin 16 → Bool) (r Q Δ D : ℕ)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ rf, RunsIn program (sourceBudget D Δ scopes)
      ((inputState regs r Q Δ D scopes).withPC (some program.entry))
      ((AssignmentInputProgram.inputState rf r Q Δ D scopes.length
        (pairBytes D Δ scopes)).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := command_eval regs r Q Δ D scopes hd
  exact ⟨rf, n + 1, hn, compiled_halt_trace he 6 45⟩

theorem primitive_run (regs : Fin 16 → Bool) (r Q Δ D : ℕ)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * sourceBudget D Δ scopes)
      (BitProgram.primitiveCfg program
        ((inputState regs r Q Δ D scopes).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((AssignmentInputProgram.inputState rf r Q Δ D scopes.length
          (pairBytes D Δ scopes)).withPC none)) := by
  obtain ⟨rf, ht⟩ := program_run regs r Q Δ D scopes hd
  exact ⟨rf, BitProgram.primitive_execution program ht⟩

theorem pairBytes_representation (D Δ : ℕ) (scopes : List (List ℕ)) :
    ∃ rawPlans : List PairScoreProgram.PlanPair,
      pairBytes D Δ scopes = PairScoreProgram.pairRecords rawPlans ∧
      rawPlans.Perm (SubexpVertexPairProgram.canonicalPairs D Δ scopes) := by
  obtain ⟨rawPlans, he, hp⟩ := SubexpVertexPairProgram.rawPlans_exists D Δ scopes
  exact ⟨rawPlans, congrArg ProgramEncoding.encodeRecords he, hp⟩

end SubexponentialSAT.Subexp.AssignmentPairFrontend

end OAI.Algorithms
