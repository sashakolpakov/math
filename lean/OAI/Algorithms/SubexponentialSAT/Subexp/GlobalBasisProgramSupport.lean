import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRowsFrame

namespace OAI.Algorithms

/-! Measured stack operations and concrete service lifts for the global
basis assembler. Every service below calls the published finite program. -/

namespace SubexponentialSAT.Subexp.GlobalBasisProgram

open BitProgram StructuredCalls

theorem regs8_injective : Function.Injective regs8 := Fin.castAdd_injective 8 8
theorem regs2_injective : Function.Injective regs2 := Fin.castAdd_injective 2 14
theorem low32_injective : Function.Injective low32 := Fin.castAdd_injective 32 32
theorem low11_injective : Function.Injective low11 := Fin.castAdd_injective 11 53

def copied (src dst : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst : Fin 64) (d : Data)
    (hsd : src ≠ dst) (hs31 : src ≠ 31) (h31d : (31 : Fin 64) ≠ dst)
    (h31 : d.stacks 31 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst 31 0 1 hsd hs31 h31d (by decide)
    d.regs d.stacks h31)

def transferred (src dst : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 64) (d : Data) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) d.regs d.stacks)

def cleared (src : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (src : Fin 64) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

theorem push_eval (dst : Fin 64) (value : Bool) (d : Data) :
    Eval (push dst value) 2 d (TupleProgram.pushedState dst 0 value d) :=
  TupleProgram.pushConst_eval dst 0 value d

theorem move_eval (src dst : Fin 64) (d : Data)
    (hsd : src ≠ dst) (hs31 : src ≠ 31) (h31d : (31 : Fin 64) ≠ dst)
    (h31 : d.stacks 31 = []) :
    ∃ e, Eval (move src dst) (6 * (d.stacks src).length + 6) d e ∧
      e.stacks = Function.update (Function.update d.stacks src []) dst
        (d.stacks src ++ d.stacks dst) := by
  let a := transferred src 31 d
  let e := transferred 31 dst a
  have h := (transfer_eval src 31 d hs31).seq (transfer_eval 31 dst a h31d)
  refine ⟨e, ?_, ?_⟩
  · convert h using 1
    all_goals first
      | rfl
      | (simp only [a, transferred, StackRoutines.transferStacks, Function.update_self,
          h31, List.append_nil, List.length_reverse]; omega)
  · funext i
    by_cases his : i = src <;> by_cases hid : i = dst <;> by_cases hi31 : i = 31 <;>
      simp_all [e, a, transferred, StackRoutines.transferStacks, Function.update_apply]

def clearBudget : List (Fin 64) → (Fin 64 → List Bool) → ℕ
  | [], _ => 0
  | i :: is, s => 2 * (s i).length + 3 + clearBudget is s

theorem clearBudget_mono (is : List (Fin 64)) (a b : Fin 64 → List Bool)
    (h : ∀ i, (a i).length ≤ (b i).length) : clearBudget is a ≤ clearBudget is b := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [clearBudget]
    have hi := h i
    omega

theorem clearList_eval (is : List (Fin 64)) (d : Data) :
    ∃ n e, n ≤ clearBudget is d.stacks ∧ Eval (clearList is) n d e ∧
      e.stacks = fun i => if i ∈ is then [] else d.stacks i := by
  induction is generalizing d with
  | nil =>
    refine ⟨0, d, by simp [clearBudget], .base (.skip _), ?_⟩
    simp
  | cons i is ih =>
    obtain ⟨n, e, hn, he, hs⟩ := ih (cleared i d)
    refine ⟨2 * (d.stacks i).length + 3 + n, e, ?_, (clear_eval i d).seq he, ?_⟩
    · have hm := clearBudget_mono is (cleared i d).stacks d.stacks (by
        intro j
        by_cases hj : j = i <;> simp [cleared, hj])
      simp only [clearBudget]
      omega
    · rw [hs]
      funext j
      by_cases hj : j = i <;> by_cases hjs : j ∈ is <;> simp [cleared, hj, hjs]

theorem getGroup_eval (before : List (List Bool)) (bits tail : List Bool) (d : Data)
    (h47 : d.stacks 47 = GlobalBasisRecordLookup.recordsPrefix before ++
      GlobalBasisRecordLookup.record bits ++ tail)
    (h32 : d.stacks 32 = GlobalBasisRecordLookup.unary before.length)
    (h40 : d.stacks 40 = []) (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = [])
    (h18 : d.stacks 18 = []) (h19 : d.stacks 19 = []) :
    ∃ n e, n ≤ 30 * ((d.stacks 47).length + (d.stacks 32).length + 1) ∧
      Eval getGroup n d e ∧ e.stacks = Function.update d.stacks 40 bits := by
  obtain ⟨b, ⟨n, hn, he⟩, hs⟩ := GlobalBasisRecordLookup.program_runsIn before bits tail
    (projectState regs8 groupPorts d) h47 h32 h40 h16 h17 h18 h19
  refine ⟨n, embedState regs8 groupPorts d b, hn,
    eval_call_from_state _ _ _ _ regs8_injective groupPorts_injective he, ?_⟩
  change Function.extend groupPorts b.stacks d.stacks = _
  rw [hs, ProgramLinking.extend_update groupPorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project regs8 groupPorts d regs8_injective groupPorts_injective)
  change Function.extend groupPorts (projectState regs8 groupPorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

theorem getSplit_eval (before : List (List Bool)) (N split : ℕ)
    (table tail : List Bool) (d : Data)
    (h40 : d.stacks 40 = GlobalBasisRecordLookup.recordsPrefix before ++
      GlobalBasisRecordLookup.record (SubexpLocalBatchParse.payload N split table) ++ tail)
    (h55 : d.stacks 55 = GlobalBasisRecordLookup.unary before.length)
    (hc : GlobalBasisDataLookup.Clean (projectState regs8 splitPorts d)) :
    ∃ n e, n ≤ 60 * ((d.stacks 40).length + (d.stacks 55).length + 1) ∧
      Eval getSplit n d e ∧ e.stacks = Function.update (Function.update
        (Function.update (Function.update d.stacks 16 (List.replicate N true))
          17 (List.replicate split true)) 18 table) 19 (List.replicate (N-split) true) := by
  obtain ⟨b, ⟨n, hn, he⟩, hs⟩ := GlobalBasisDataLookup.program_runsIn before N split table tail
    (projectState regs8 splitPorts d) h40 h55 hc
  refine ⟨n, embedState regs8 splitPorts d b, hn,
    eval_call_from_state _ _ _ _ regs8_injective splitPorts_injective he, ?_⟩
  change Function.extend splitPorts b.stacks d.stacks = _
  rw [hs]
  simp only [GlobalBasisDataLookup.resultStacks, ProgramLinking.extend_update splitPorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project regs8 splitPorts d regs8_injective splitPorts_injective)
  change Function.extend splitPorts (projectState regs8 splitPorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

theorem kernelColumns_eval (count color dimension : ℕ) (d : Data)
    (h0 : d.stacks 0 = List.replicate count true)
    (h1 : d.stacks 1 = List.replicate color true)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = [])
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = [])
    (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = List.replicate dimension true) :
    ∃ n e, n ≤ 220 * (count + color + dimension + 1)^3 ∧ Eval kernelColumns n d e ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 3
        (GlobalBasisColumnBlocks.blockPrefix count color dimension ++ d.stacks 3) := by
  obtain ⟨b, ⟨n, hn, he⟩, hs⟩ := GlobalBasisColumnBlocks.program_runsIn count color dimension
    (projectState regs8 low11 d) h0 h1 h2 h4 h5 h6 h7 h8 h9 h10
  refine ⟨n, embedState regs8 low11 d b, hn,
    eval_call_from_state _ _ _ _ regs8_injective low11_injective he, ?_⟩
  change Function.extend low11 b.stacks d.stacks = _
  rw [hs, ProgramLinking.extend_update low11_injective, ProgramLinking.extend_update low11_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project regs8 low11 d regs8_injective low11_injective)
  change Function.extend low11 (projectState regs8 low11 d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

theorem outerColumns_eval (count leftovers : ℕ)
    (qs : List GlobalBasisComplementColumns.LocalData) (d : Data)
    (h0 : d.stacks 0 = List.replicate count true)
    (h40 : d.stacks 40 = GlobalBasisComplementColumns.encoded qs)
    (h38 : d.stacks 38 = List.replicate qs.length true)
    (h49 : d.stacks 49 = List.replicate leftovers true)
    (h25 : d.stacks 25 = [])
    (hc : SubexpComplementColumnBatch.Ready (projectState regs8 outerPorts d)) :
    ∃ n e, n ≤ SubexpComplementColumnBatch.cost count leftovers qs + 1 ∧
      Eval outerColumns n d e ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 35
        (SubexpComplementColumnBatch.outputPrefix count leftovers qs ++ d.stacks 35) := by
  obtain ⟨n, hn, b, he, hs⟩ := SubexpComplementColumnBatch.command_eval count leftovers qs
    (projectState regs8 outerPorts d) h0 h40 h38 h49 h25 hc
  refine ⟨n + 1, embedState regs8 outerPorts d b, by omega,
    eval_call_from_state _ _ _ _ regs8_injective outerPorts_injective
      (compiled_halt_trace he 0 3), ?_⟩
  change Function.extend outerPorts b.stacks d.stacks = _
  rw [hs, ProgramLinking.extend_update outerPorts_injective,
    ProgramLinking.extend_update outerPorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project regs8 outerPorts d regs8_injective outerPorts_injective)
  change Function.extend outerPorts (projectState regs8 outerPorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

theorem row_eval {p : ℕ} [Fact p.Prime] (R : GlobalBasisEntry.Row p)
    (xs : List GlobalBasisColumns.Descriptor) (d : Data)
    (hi : GlobalBasisRows.Invariant R (projectState id low32 d))
    (hv : ∀ x ∈ xs, GlobalBasisEntry.Valid R x)
    (h6 : d.stacks 6 = Encoding.encodeList id (GlobalBasisRows.records xs))
    (h7 : d.stacks 7 = []) :
    ∃ n e, n ≤ 2000 * (GlobalBasisRows.baseSize R + GlobalBasisRows.encodedSize xs + 1)^4 ∧
      Eval row n d e ∧ e.stacks = Function.update (Function.update d.stacks 6 []) 12
        ((GlobalBasisRows.rowBits R xs).reverse ++ d.stacks 12) := by
  have h6' : (projectState id low32 d).stacks 6 =
      Encoding.encodeList id (GlobalBasisRows.records xs) := by
    change d.stacks 6 = _
    exact h6
  have h7' : (projectState id low32 d).stacks 7 = [] := by
    change d.stacks 7 = []
    exact h7
  obtain ⟨b, _, ⟨n, hn, he⟩, hs⟩ := GlobalBasisRows.program_runsIn_from_state R xs []
    (projectState id low32 d) hi hv (by simpa using h6') h7'
  refine ⟨n, embedState id low32 d b, hn,
    eval_call_from_state _ _ _ _ Function.injective_id low32_injective he, ?_⟩
  change Function.extend low32 b.stacks d.stacks = _
  rw [hs, ProgramLinking.extend_update low32_injective, ProgramLinking.extend_update low32_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id low32 d Function.injective_id low32_injective)
  change Function.extend low32 (projectState id low32 d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

theorem countPorts_injective : Function.Injective countPorts := by decide

def countBudget (records : List (List Bool)) : ℕ :=
  7 * (Encoding.encodeList id records).length + 5 +
    SubexpSunflowerProgram.CountRecords.loopSteps records

theorem countColumns_eval (records : List (List Bool)) (d : Data)
    (h35 : d.stacks 35 = Encoding.encodeList id records)
    (h16 : d.stacks 16 = []) (h31 : d.stacks 31 = []) (h50 : d.stacks 50 = []) :
    ∃ e, Eval countColumns (countBudget records) d e ∧
      e.stacks = Function.update d.stacks 50 (List.replicate records.length true) := by
  let a := copied 35 16 d
  let small := SubexpScopeCountSetup.counterState false false [] (List.replicate records.length true)
  have hi : projectState regs2 countPorts a =
      SubexpScopeCountSetup.counterState (a.regs 0) (a.regs 1)
        (Encoding.encodeList id records) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ countPorts,
        ParserProgram.pair, a, copied, StackRoutines.copyStacks, h35, h16, h50]
  have ht := SubexpScopeCountSetup.counter_trace records (a.regs 0) (a.regs 1)
  rw [← hi] at ht
  let e := embedState regs2 countPorts a small
  have he : Eval (.call (ProgramLinking.liftProgram SubexpScopeCountSetup.counterProgram
      regs2 countPorts)) (SubexpSunflowerProgram.CountRecords.loopSteps records) a e :=
    eval_call_from_state _ _ _ _ regs2_injective countPorts_injective ht
  have hstack : e.stacks = Function.update d.stacks 50 (List.replicate records.length true) := by
    have hs : small.stacks = Function.update (Function.update
        (projectState regs2 countPorts a).stacks 0 []) 1 (List.replicate records.length true) := by
      funext i
      fin_cases i <;> simp [small, SubexpScopeCountSetup.counterState, ParserProgram.pair]
    change Function.extend countPorts small.stacks a.stacks = _
    rw [hs, ProgramLinking.extend_update countPorts_injective,
      ProgramLinking.extend_update countPorts_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project regs2 countPorts a regs2_injective countPorts_injective)
    change Function.extend countPorts (projectState regs2 countPorts a).stacks a.stacks = a.stacks at hp
    rw [hp]
    funext i
    by_cases h : i = 50
    · subst i
      simp [a, copied, StackRoutines.copyStacks, countPorts]
    by_cases h' : i = 16
    · subst i
      simp [a, copied, StackRoutines.copyStacks, countPorts, h16]
    · simp [a, copied, StackRoutines.copyStacks, countPorts, h, h']
  refine ⟨e, ?_, hstack⟩
  have h := (copy_eval 35 16 d (by decide) (by decide) (by decide) h31).seq
    (he.seq (.base (.skip e)))
  simpa only [countColumns, sequence, List.foldr, h35, countBudget, Nat.add_zero] using h

theorem countBudget_le (records : List (List Bool)) :
    countBudget records ≤ 13 * (Encoding.encodeList id records).length + 4 := by
  have hlength : (Encoding.encodeList id records).length =
      2 * (records.map List.length).sum + 2 * records.length + 1 := by
    induction records with
    | nil => rfl
    | cons bits records ih =>
      simp [Encoding.encodeList, ih]
      omega
  simp only [countBudget, SubexpSunflowerProgram.CountRecords.loopSteps]
  rw [hlength]
  omega

end SubexponentialSAT.Subexp.GlobalBasisProgram

end OAI.Algorithms
