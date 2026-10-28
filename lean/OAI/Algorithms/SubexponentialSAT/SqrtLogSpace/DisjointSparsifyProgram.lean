import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointSparsify
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram
import OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram
import OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import Mathlib.Algebra.BigOperators.Fin

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

/-- The iterator prepends each generated unit, so the core order is reversed. -/
def negatedUnits {α : Type*} (negate : α → α) (H : List α) : List (List α) :=
  H.reverse.map fun l => [negate l]

/-- Units are inserted before the petal routine's actual absorption pass. -/
def resultB {α : Type*} [DecidableEq α] (negate : α → α)
    (F selected : List (List α)) (H : List α) : List (List α) :=
  ExecPetalChildProgram.result (negatedUnits negate H ++ F) selected H

theorem negatedUnits_set {V : Type*} [DecidableEq V] (H : List (Literal V)) :
    ExecCNF.formulaSet (negatedUnits Literal.negate H) =
      DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) := by
  ext C
  simp [negatedUnits, ExecCNF.formulaSet, ExecCNF.clauseSet,
    DisjointBranch.negatedCoreUnits, Finset.mem_image]

theorem resultA_set {V : Type*} [DecidableEq V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    ExecCNF.formulaSet (ExecCoreChildProgram.result F S H) =
      DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  simpa only [hS, DisjointBranch.childA, SAT.absorb] using
    ExecCoreChildProgram.result_set F S H

theorem units_disjoint_selected {V : Type*} [DecidableEq V]
    (F : CNF V) (c : ℕ) (H : Clause V) (hc : 2 ≤ c) :
    Disjoint (DisjointBranch.negatedCoreUnits H) (DisjointBranch.selected F c H) := by
  apply Finset.disjoint_left.mpr
  intro U hU hsel
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hU
  have hcard := (DisjointBranch.mem_selected.mp hsel).2.1
  rw [Finset.card_singleton] at hcard
  omega

theorem resultB_set {V : Type*} [DecidableEq V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ) (hc : 2 ≤ c)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    ExecCNF.formulaSet (resultB Literal.negate F S H) =
      DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  have hdisj := units_disjoint_selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) hc
  have hdiff :
      (DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) ∪ ExecCNF.formulaSet F) \
        DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) =
      DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) ∪
        (ExecCNF.formulaSet F \
          DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) := by
    rw [Finset.union_sdiff_distrib, hdisj.sdiff_eq_left]
  unfold resultB
  rw [ExecPetalChildProgram.result_set]
  change SAT.absorb (_ ∪ (_ \ _)) = _
  rw [ExecCNF.formulaSet_append, negatedUnits_set, hS, hdiff]
  unfold DisjointBranch.childB DisjointBranch.petals SunflowerBranch.petalFamily
  apply congrArg SAT.absorb
  ac_rfl

theorem count_results {V : Type*} [DecidableEq V] [Fintype V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ) (hc : 2 ≤ c)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    SAT.count (ExecCNF.formulaSet F) =
      SAT.count (ExecCNF.formulaSet (ExecCoreChildProgram.result F S H)) +
      SAT.count (ExecCNF.formulaSet (resultB Literal.negate F S H)) := by
  rw [resultA_set F S H c hS, resultB_set F S H c hc hS]
  exact DisjointBranch.count_children _ _ _

theorem resultA_clause_nodup {α : Type*} [DecidableEq α]
    (F S : List (List α)) (H : List α) :
    ((ExecCoreChildProgram.result F S H).map ExecCNF.clauseSet).Nodup :=
  ExecCNF.absorb_map_nodup _

theorem resultB_clause_nodup {α : Type*} [DecidableEq α]
    (negate : α → α) (F S : List (List α)) (H : List α) :
    ((resultB negate F S H).map ExecCNF.clauseSet).Nodup :=
  ExecCNF.absorb_map_nodup _

theorem resultA_literal_nodup {α : Type*} [DecidableEq α]
    (F S : List (List α)) (H : List α)
    (hF : ∀ C ∈ F, C.Nodup) (hH : H.Nodup) :
    ∀ C ∈ ExecCoreChildProgram.result F S H, C.Nodup := by
  intro C hC
  have h := ExecCNF.absorb_subset _ hC
  rcases List.mem_cons.mp h with rfl | h
  · exact hH
  · exact hF C (List.mem_filter.mp h).1

theorem resultB_literal_nodup {α : Type*} [DecidableEq α]
    (negate : α → α) (F S : List (List α)) (H : List α)
    (hF : ∀ C ∈ F, C.Nodup) (hS : ∀ C ∈ S, C.Nodup) :
    ∀ C ∈ resultB negate F S H, C.Nodup := by
  intro C hC
  have h := ExecCNF.absorb_subset _ hC
  rcases List.mem_append.mp h with h | h
  · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h
    exact (hS D hD).filter _
  · have hmem := (List.mem_filter.mp h).1
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hmem
      exact List.nodup_singleton _
    · exact hF C hmem

theorem negatedUnits_codes {n : ℕ} (H : List (Literal (Fin n))) :
    negatedUnits SubexpFrontend.negateCode (H.map Encoding.literalCode) =
      (negatedUnits Literal.negate H).map (List.map Encoding.literalCode) := by
  simp [negatedUnits, List.map_reverse, List.map_map, Function.comp_def,
    SubexpFrontend.literalCode_negate]

theorem resultB_codes {n : ℕ} (F S : List (List (Literal (Fin n))))
    (H : List (Literal (Fin n))) :
    resultB SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode))
      (S.map (List.map Encoding.literalCode)) (H.map Encoding.literalCode) =
      (resultB Literal.negate F S H).map (List.map Encoding.literalCode) := by
  unfold resultB
  rw [negatedUnits_codes, ← List.map_append]
  exact ExecPetalChildProgram.result_map Encoding.literalCode Encoding.literalCode_injective _ _ _

open BitProgram StructuredCalls

/-- The unit builder has eight scratch ports, disjoint from the retained core
and selected family. Its accumulator is the parent formula port. -/
def unitRegister (i : Fin 10) : Fin 15 := Fin.castAdd 5 i

def unitStack : Fin 8 → Fin 16 := ![0, 1, 13, 2, 3, 4, 5, 6]

theorem unitRegister_injective : Function.Injective unitRegister :=
  Fin.castAdd_injective 10 5

theorem unitStack_injective : Function.Injective unitStack := by decide

def copyCore : Cmd 15 16 := .call (StackRoutines.copyProgram 9 0 10 0 1)

theorem copyCore_eval (d : State 15 16) (h0 : d.stacks 0 = [])
    (h10 : d.stacks 10 = []) :
    Eval copyCore (7 * (d.stacks 9).length + 5) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks 0 (d.stacks 9)⟩ := by
  have h := ListRegisterProgram.copy_run (r := 15) (s := 16) 9 0 10 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h10
  apply Eval.call
  simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, h0, List.append_nil] using h

def prepareB : Cmd 15 16 := .seq copyCore
  (.call (ProgramLinking.liftProgram NegatedCoreProgram.program unitRegister unitStack))

theorem prepareB_eval (F S : List (List ℕ)) (H : List ℕ) (d : State 15 16)
    (hcore : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hselected : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hsource : d.stacks 13 = ExecCoreChildProgram.formulaCode F)
    (hready : ExecCoreChildProgram.InputReady d) :
    ∃ t ≤ 430 * ExecCoreChildProgram.inputVolume F S H, ∃ e : State 15 16,
      Eval prepareB t d e ∧ ExecCoreChildProgram.InputReady e ∧
      e.stacks 9 = ExecCoreChildProgram.clauseCode H ∧
      e.stacks 12 = ExecCoreChildProgram.formulaCode S ∧
      e.stacks 13 = ExecCoreChildProgram.formulaCode
        (negatedUnits SubexpFrontend.negateCode H ++ F) := by
  let a : State 15 16 :=
    ⟨readRegs d.regs 0 1 none, Function.update d.stacks 0 (d.stacks 9)⟩
  let small : State 10 8 := ⟨a.regs ∘ unitRegister, a.stacks ∘ unitStack⟩
  have hl0 : small.stacks 0 = NegatedCoreProgram.clauseCode H := by
    simpa [small, a, unitStack, NegatedCoreProgram.clauseCode,
      ExecCoreChildProgram.clauseCode, SubexpTautologyProgram.encodedClause,
      ExecCleanLiteralsProgram.clauseCode] using hcore
  have hl2 : small.stacks 2 = NegatedCoreProgram.formulaCode F := by
    change small.stacks 2 = Encoding.encodeList ExecCleanLiteralsProgram.clauseCode F
    change d.stacks 13 = Encoding.encodeList ExecCleanLiteralsProgram.clauseCode F at hsource
    simpa [small, a, unitStack] using hsource
  have hl1 : small.stacks 1 = [] := by
    simpa [small, a, unitStack] using hready 1 (by decide) (by decide) (by decide)
  have hlclean : ExecLiteralDedupProgram.Clean small := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [small, Function.comp_apply, unitStack, a]
      first
      | exact hready 2 (by decide) (by decide) (by decide)
      | exact hready 3 (by decide) (by decide) (by decide)
      | exact hready 4 (by decide) (by decide) (by decide)
      | exact hready 5 (by decide) (by decide) (by decide)
      | exact hready 6 (by decide) (by decide) (by decide)
  obtain ⟨b, hbout, hbclean, t, ht, htrace⟩ :=
    NegatedCoreProgram.program_runsIn H F small hl0 hl2 hl1 hlclean
  have ha : embedState unitRegister unitStack a small = a := by
    apply embedState_eq_of_ports _ _ _ _ _ unitRegister_injective unitStack_injective
    · intro i; rfl
    · intro i _; rfl
    · intro i; rfl
    · intro i _; rfl
  let e := embedState unitRegister unitStack a b
  have he := eval_call_lifted NegatedCoreProgram.program unitRegister unitStack a
    unitRegister_injective unitStack_injective htrace
  rw [ha] at he
  have heport (i : Fin 8) : e.stacks (unitStack i) = b.stacks i :=
    embedState_stack _ _ _ _ unitStack_injective i
  have heready : ExecCoreChildProgram.InputReady e := by
    intro i hi9 hi12 hi13
    by_cases hi : ∃ j, unitStack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (heport j).trans (hbclean j (fun hj => hi13 (hj ▸ rfl)))
    · have hi0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      rw [embedState_stack_frame _ _ _ _ _ hi]
      simpa [a, hi0] using hready i hi9 hi12 hi13
  have he9 : e.stacks 9 = ExecCoreChildProgram.clauseCode H := by
    rw [embedState_stack_frame _ _ _ _ _ (by decide)]
    simpa [a] using hcore
  have he12 : e.stacks 12 = ExecCoreChildProgram.formulaCode S := by
    rw [embedState_stack_frame _ _ _ _ _ (by decide)]
    simpa [a] using hselected
  have he13 : e.stacks 13 = ExecCoreChildProgram.formulaCode
      (negatedUnits SubexpFrontend.negateCode H ++ F) := by
    exact (heport 2).trans hbout
  have hcopy := copyCore_eval d (hready 0 (by decide) (by decide) (by decide))
    (hready 10 (by decide) (by decide) (by decide))
  refine ⟨7 * (d.stacks 9).length + 5 + t, ?_, e,
    hcopy.seq he, heready, he9, he12, he13⟩
  rw [hcore]
  change t ≤ 417 * ((ExecCoreChildProgram.clauseCode H).length + 1) at ht
  unfold ExecCoreChildProgram.inputVolume
  omega

theorem preparedB_volume_le (F S : List (List ℕ)) (H : List ℕ) :
    ExecPetalChildProgram.inputVolume
        (negatedUnits SubexpFrontend.negateCode H ++ F) S H ≤
      5 * ExecCoreChildProgram.inputVolume F S H := by
  have h := NegatedCoreProgram.output_length_le H F
  change (ExecCoreChildProgram.formulaCode
      (negatedUnits SubexpFrontend.negateCode H ++ F)).length ≤
    (ExecCoreChildProgram.formulaCode F).length +
      8 * (ExecCoreChildProgram.clauseCode H).length at h
  unfold ExecPetalChildProgram.inputVolume ExecCoreChildProgram.inputVolume
  dsimp only [ExecPetalChildProgram.formulaCode, ExecPetalChildProgram.clauseCode,
    ExecCoreChildProgram.formulaCode, ExecCoreChildProgram.clauseCode] at h ⊢
  omega

theorem resultB_length_le (F S : List (List ℕ)) (H : List ℕ) :
    (ExecCoreChildProgram.formulaCode (resultB SubexpFrontend.negateCode F S H)).length ≤
      5 * ExecCoreChildProgram.inputVolume F S H := by
  have h := ExecPetalChildProgram.result_length_le
    (negatedUnits SubexpFrontend.negateCode H ++ F) S H
  exact (Nat.le_add_right _ 1).trans (h.trans (preparedB_volume_le F S H))

def commandB : Cmd 15 16 := .seq prepareB ExecPetalChildProgram.command

theorem commandB_eval (F S : List (List ℕ)) (H : List ℕ) (d : State 15 16)
    (hcore : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hselected : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hsource : d.stacks 13 = ExecCoreChildProgram.formulaCode F)
    (hready : ExecCoreChildProgram.InputReady d) :
    ∃ t ≤ 500000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2, ∃ e : State 15 16,
      Eval commandB t d e ∧ SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = ExecCoreChildProgram.formulaCode
        (resultB SubexpFrontend.negateCode F S H) := by
  obtain ⟨t, ht, a, ha, haready, ha9, ha12, ha13⟩ :=
    prepareB_eval F S H d hcore hselected hsource hready
  obtain ⟨u, hu, e, he, heready, he13⟩ := ExecPetalChildProgram.command_eval
    (negatedUnits SubexpFrontend.negateCode H ++ F) S H a ha9 ha12 ha13 haready
  refine ⟨t + u, ?_, e, ha.seq he, heready, he13⟩
  have hvol := preparedB_volume_le F S H
  have hsq := Nat.pow_le_pow_left hvol 2
  have hv : 1 ≤ ExecCoreChildProgram.inputVolume F S H := by
    unfold ExecCoreChildProgram.inputVolume
    omega
  nlinarith [Nat.mul_le_mul_left (ExecCoreChildProgram.inputVolume F S H) hv]

def programB := compiled commandB 13 13

theorem programB_runsIn (F S : List (List ℕ)) (H : List ℕ) (d : State 15 16)
    (hcore : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hselected : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hsource : d.stacks 13 = ExecCoreChildProgram.formulaCode F)
    (hready : ExecCoreChildProgram.InputReady d) :
    ∃ e : State 15 16, SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = ExecCoreChildProgram.formulaCode
        (resultB SubexpFrontend.negateCode F S H) ∧
      RunsIn programB (600000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
        (d.withPC (some programB.entry)) (e.withPC none) := by
  obtain ⟨t, ht, e, he, heready, he13⟩ := commandB_eval F S H d hcore hselected hsource hready
  refine ⟨e, heready, he13, t + 1, ?_, compiled_halt_trace he 13 13⟩
  have hv : 0 < ExecCoreChildProgram.inputVolume F S H := by
    unfold ExecCoreChildProgram.inputVolume
    omega
  have hp := pow_pos hv 2
  omega

open ExecBranchControllerSupport

def inputFront (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ) : Front :=
  ![pending, header, [], [], ExecCoreChildProgram.formulaCode F,
    ExecCoreChildProgram.clauseCode H, ExecCoreChildProgram.formulaCode S]

def outputFront (pending header childA childB : List Bool) : Front :=
  ![pending, header, ExecWorklistProgram.record childA,
    ExecWorklistProgram.record childB, [], [], []]

def inputState (regs : Regs) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) : Data :=
  idle regs (inputFront pending header F S H)

def outputState (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ) : Data :=
  idle (fun _ => false) (outputFront pending header
    (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H))
    (ExecCoreChildProgram.formulaCode (resultB SubexpFrontend.negateCode F S H)))

theorem outputState_clean (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) (i : Fin 23) (hi : 4 ≤ i.val) :
    (outputState pending header F S H).stacks i = [] := by
  revert hi
  refine Fin.addCases (m := 7) (n := 16) (fun j => ?_) (fun j => ?_) i
  · intro hj
    simp only [outputState, idle, state, Fin.addCases_left]
    change 4 ≤ j.val at hj
    fin_cases j <;> simp_all [outputFront]
  · intro _
    simp [outputState, idle, state, emptyBank]

private theorem loaded_ready (regs : Regs) (front : Front) :
    ExecCoreChildProgram.InputReady (loaded regs front) := by
  intro i h9 h12 h13
  fin_cases i <;> first | exact False.elim (h9 rfl) | exact False.elim (h12 rfl) |
    exact False.elim (h13 rfl) | rfl

def command : Cmd 15 23 :=
  .seq (buildChild ExecCoreChildProgram.program 0)
    (.seq (buildChild programB 1) (.seq cleanInputs RegisterResetProgram.all))

theorem command_eval (regs : Regs) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) :
    ∃ t ≤ 610000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2,
      Eval command t (inputState regs pending header F S H)
        (outputState pending header F S H) := by
  let f0 := inputFront pending header F S H
  let wordA := ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)
  let wordB := ExecCoreChildProgram.formulaCode (resultB SubexpFrontend.negateCode F S H)
  obtain ⟨a, haReady, haOut, t, ht, ha⟩ :=
    ExecCoreChildProgram.program_runsIn F S H (loaded (reset regs) f0) rfl rfl rfl
      (loaded_ready (reset regs) f0)
  have haEq : a = ExecClauseFiltersProgram.state a.regs [] [] [] wordA [] [] := by
    simpa only [haOut] using ExecClauseFiltersProgram.ready_eq_state a haReady
  rw [haEq] at ha
  have hA := buildChild_eval ExecCoreChildProgram.program 0 regs f0 wordA a.regs ha
  simp only [show outputPort 0 = 2 from rfl, show f0 2 = [] from rfl, List.append_nil] at hA
  let ra := emittedRegs (reset a.regs)
  let fa : Front := Function.update f0 2 (ExecWorklistProgram.record wordA)
  obtain ⟨b, hbReady, hbOut, u, hu, hb⟩ :=
    programB_runsIn F S H (loaded (reset ra) fa) rfl rfl rfl (loaded_ready (reset ra) fa)
  have hbEq : b = ExecClauseFiltersProgram.state b.regs [] [] [] wordB [] [] := by
    simpa only [hbOut] using ExecClauseFiltersProgram.ready_eq_state b hbReady
  rw [hbEq] at hb
  have hB := buildChild_eval programB 1 ra fa wordB b.regs hb
  simp only [show outputPort 1 = 3 from rfl, show fa 3 = [] from rfl, List.append_nil] at hB
  let rb := emittedRegs (reset b.regs)
  let fb : Front := Function.update fa 3 (ExecWorklistProgram.record wordB)
  have hclean := cleanInputs_eval rb fb
  have hreset := RegisterResetProgram.all_eval (idle (reset rb) (cleanFront fb))
  have hfinal : cleanFront fb = outputFront pending header wordA wordB := by
    funext i
    fin_cases i <;> simp [cleanFront, fb, fa, f0, inputFront, outputFront]
  have hfull := hA.seq (hB.seq (hclean.seq hreset))
  rw [hfinal] at hfull
  change Eval command _ (inputState regs pending header F S H)
    (outputState pending header F S H) at hfull
  refine ⟨_, ?_, hfull⟩
  let V := ExecCoreChildProgram.inputVolume F S H
  have hv : 1 ≤ V := by dsimp [V, ExecCoreChildProgram.inputVolume]; omega
  have hsq : V ≤ V ^ 2 := by nlinarith [Nat.mul_le_mul_left V hv]
  have hsum : (ExecCoreChildProgram.formulaCode F).length +
      (ExecCoreChildProgram.clauseCode H).length +
      (ExecCoreChildProgram.formulaCode S).length ≤ V := by
    dsimp [V, ExecCoreChildProgram.inputVolume]
    omega
  have hlenA : wordA.length ≤ V := by
    have h := ExecCoreChildProgram.result_length_le F S H
    dsimp [wordA, V, ExecCoreChildProgram.inputVolume]
    omega
  have hlenB : wordB.length ≤ 5 * V := resultB_length_le F S H
  have hload0 : loadCost f0 ≤ 7 * V + 15 := by
    change 7 * ((ExecCoreChildProgram.formulaCode F).length +
      (ExecCoreChildProgram.clauseCode H).length +
      (ExecCoreChildProgram.formulaCode S).length) + 15 ≤ _
    omega
  have hloadA : loadCost fa = loadCost f0 := by simp [loadCost, fa]
  have hcleanup : 2 * ((fb 4).length + (fb 5).length + (fb 6).length) + 9 ≤ 2 * V + 9 := by
    change 2 * ((ExecCoreChildProgram.formulaCode F).length +
      (ExecCoreChildProgram.clauseCode H).length +
      (ExecCoreChildProgram.formulaCode S).length) + 9 ≤ _
    omega
  change t ≤ 3300 * V ^ 2 at ht
  change u ≤ 600000 * V ^ 2 at hu
  change loadCost f0 + (t + (8 * wordA.length + 10)) +
    (loadCost fa + (u + (8 * wordB.length + 10)) +
      (2 * ((fb 4).length + (fb 5).length + (fb 6).length) + 9 + 15)) ≤ 610000 * V ^ 2
  rw [hloadA]
  nlinarith

def program := compiled command 4 2

theorem program_runsIn (regs : Regs) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) :
    RunsIn program (620000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
      ((inputState regs pending header F S H).withPC (some program.entry))
      ((outputState pending header F S H).withPC none) := by
  obtain ⟨t, ht, he⟩ := command_eval regs pending header F S H
  refine ⟨t + 1, ?_, compiled_halt_trace he 4 2⟩
  have hv : 0 < ExecCoreChildProgram.inputVolume F S H := by
    unfold ExecCoreChildProgram.inputVolume
    omega
  have hp := pow_pos hv 2
  omega

/-- A local prefix bound for every stack in the finite splitter, including
the preserved caller words. Global tape spans require the compiler bridge. -/
theorem prefix_dataBits_le (regs : Regs) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ)
    {t : ℕ} {c : Cfg 15 23 (size command + 1)}
    (ht : t ≤ 620000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
    (htrace : Trace program t
      ((inputState regs pending header F S H).withPC (some program.entry)) c) :
    dataBits c ≤ pending.length + header.length +
      620001 * (ExecCoreChildProgram.inputVolume F S H) ^ 2 := by
  have h := trace_dataBits program htrace
  have hbits : dataBits
      ((inputState regs pending header F S H).withPC (some program.entry)) =
      pending.length + header.length + (ExecCoreChildProgram.formulaCode F).length +
        (ExecCoreChildProgram.clauseCode H).length +
        (ExecCoreChildProgram.formulaCode S).length := by
    unfold dataBits stackBits
    rw [Fin.sum_univ_add (a := 7) (b := 16)]
    simp [inputState, idle, state, inputFront, emptyBank,
      Fin.sum_univ_succ, Nat.add_assoc]
  rw [hbits] at h
  let V := ExecCoreChildProgram.inputVolume F S H
  have hv : 1 ≤ V := by dsimp [V, ExecCoreChildProgram.inputVolume]; omega
  have hsq : V ≤ V ^ 2 := by nlinarith [Nat.mul_le_mul_left V hv]
  have hsize : (ExecCoreChildProgram.formulaCode F).length +
      (ExecCoreChildProgram.clauseCode H).length +
      (ExecCoreChildProgram.formulaCode S).length ≤ V := by
    dsimp [V, ExecCoreChildProgram.inputVolume]
    omega
  dsimp only [V] at hsq hsize
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
