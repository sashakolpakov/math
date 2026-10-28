import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsMoment
import OAI.Algorithms.SubexponentialSAT.SubexpNodeStoreTransitions

namespace OAI.Algorithms

/-! The canonical node store supplies the moment evaluator's workspace.
Only actual persistent words are inputs; no readiness or execution contract
is assumed. The physical phase prefix clears the current node and index. -/

namespace SubexponentialSAT.SubexpNodePhaseReady

open StructuredProgram SubexpNodeWorkspace

abbrev Data := State 16 288

def native (i : Fin 128) : Fin 288 :=
  SubexpNodeWidePhase.ports (SubexpNodePhaseExecution.ports i)

theorem native_injective : Function.Injective native :=
  SubexpNodeWidePhase.ports_injective.comp SubexpNodePhaseExecution.ports_injective

def baseStacks (masters : Store) (i : Fin 128) : List Bool :=
  initialStacks masters (native i)

theorem phase_stack (d : Data) (i : Fin 128) :
    (SubexpNodeJobsMoment.phaseState d).stacks i =
      if i = 116 then [] else if i = 78 then [] else d.stacks (native i) := by
  have h116 : SubexpNodePhaseExecution.ports i = 116 ↔ i = 116 := by
    change SubexpNodePhaseExecution.ports i = SubexpNodePhaseExecution.ports 116 ↔ i = 116
    exact SubexpNodePhaseExecution.ports_injective.eq_iff
  have h78 : SubexpNodePhaseExecution.ports i = 78 ↔ i = 78 := by
    change SubexpNodePhaseExecution.ports i = SubexpNodePhaseExecution.ports 78 ↔ i = 78
    exact SubexpNodePhaseExecution.ports_injective.eq_iff
  simp only [SubexpNodeJobsMoment.phaseState, SubexpNodePhaseExecution.localState,
    SubexpNodeWidePhase.localState, StructuredCalls.projectState,
    SubexpNodePhaseExecution.prepared, SubexpNodeCacheSetup.clearOut,
    Function.comp_apply, Function.update_apply, h116, h78, native]

theorem base_empty (masters : Store) (i : Fin 128)
    (h5 : i.val ≠ 5) (h10 : i.val ≠ 10) (h25 : i.val ≠ 25)
    (h91 : i.val ≠ 91) (h92 : i.val ≠ 92) (h109 : i.val ≠ 109)
    (h119 : i.val < 119) : baseStacks masters i = [] := by
  apply initial_empty
  simp only [MasterPort, native, SubexpNodeWidePhase.ports,
    SubexpNodePhaseExecution.ports, Fin.ext_iff, Fin.val_castAdd, Fin.coe_ofNat_eq_mod]
  omega

theorem phase_templated (masters : Store) (d : Data) (index template : List Bool)
    (hstore : d.stacks = SubexpNodeStoreTransitions.templated masters index template) :
    (SubexpNodeJobsMoment.phaseState d).stacks = baseStacks masters := by
  funext i
  rw [phase_stack]
  by_cases h116 : i = 116
  · subst i
    exact (base_empty masters 116 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).symm
  by_cases h78 : i = 78
  · subst i
    simp only [ite_eq_right h116]
    exact (base_empty masters 78 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).symm
  have hn116 : native i ≠ 116 := by
    change native i ≠ native 116
    exact fun he => h116 (native_injective he)
  have hn200 : native i ≠ 200 := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 200 at hv
    omega
  simp only [ite_eq_right h116, ite_eq_right h78, hstore, SubexpNodeStoreTransitions.templated,
    Function.update_of_ne hn200, Function.update_of_ne hn116, baseStacks]

theorem jobs_update (masters : Store) (d : Data) (index stream : List Bool)
    (hstore : d.stacks = SubexpNodeStoreTransitions.jobs masters index stream) :
    d.stacks = Function.update (Function.update
      (SubexpNodeStoreTransitions.templated masters index []) 200 []) 100 stream := by
  rw [SubexpNodeStoreTransitions.jobs_result]
  exact hstore

theorem phase_jobs (masters : Store) (d : Data) (index stream : List Bool)
    (hstore : d.stacks = SubexpNodeStoreTransitions.jobs masters index stream) :
    (SubexpNodeJobsMoment.phaseState d).stacks = Function.update (baseStacks masters) 100 stream := by
  let before : Data := ⟨d.regs, SubexpNodeStoreTransitions.templated masters index []⟩
  have he := SubexpNodeJobsMoment.phaseState_jobs before d stream
    (jobs_update masters d index stream hstore)
  rw [phase_templated masters before index [] rfl] at he
  exact he

theorem ready_of_base (masters : Store) (d : SubexpMomentProgram.Data)
    (modulus width : List Bool) (hstore : d.stacks = baseStacks masters)
    (h5 : masters 5 = modulus) (h10 : masters 10 = width) :
    SubexpMomentStep.Ready d modulus width := by
  constructor
  · intro i
    rw [hstore]
    fin_cases i <;> simp [baseStacks, native, SubexpNodeWidePhase.ports,
      SubexpNodePhaseExecution.ports, SubexpJetCellProgram.scalarPorts,
      initialStacks, MasterPort, SubexpMomentStep.lowLayout, h5, h10,
      Fin.coe_ofNat_eq_mod]
  · intro i hi
    rw [hstore]
    simp only [SubexpMomentStep.scratchPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact base_empty masters _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)

theorem context_of_base (masters : Store) (d : SubexpMomentProgram.Data)
    (modulus width slotMaster reduction keyWidth : List Bool)
    (hstore : d.stacks = baseStacks masters)
    (h5 : masters 5 = modulus) (h10 : masters 10 = width)
    (h25 : masters 25 = slotMaster) (h91 : masters 91 = reduction)
    (h92 : masters 92 = keyWidth) :
    SubexpDenseMultiplication.ContextReady (SubexpEvaluationProgram.contextOf d.stacks)
      modulus width slotMaster reduction keyWidth := by
  constructor
  · intro i
    rw [SubexpDenseEvaluation.contextOf_metadata d.stacks _ (Or.inl i.isLt), hstore]
    fin_cases i <;> simp [SubexpDenseOperandWrappers.coreStacks, SubexpDenseOperands.readyStacks,
      baseStacks, native, SubexpNodeWidePhase.ports, SubexpNodePhaseExecution.ports,
      initialStacks, MasterPort, h5, h10, h25, Fin.coe_ofNat_eq_mod]
  · intro i hlo hhi
    rw [SubexpDenseEvaluation.contextOf_metadata d.stacks i (Or.inr ⟨hlo, by omega⟩), hstore]
    exact base_empty masters i (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  · rw [SubexpDenseEvaluation.contextOf_metadata d.stacks 91
      (by norm_num [SubexpDenseEvaluation.MetadataPort, Fin.coe_ofNat_eq_mod]), hstore]
    simpa [baseStacks, native, SubexpNodeWidePhase.ports, SubexpNodePhaseExecution.ports,
      initialStacks, MasterPort, Fin.coe_ofNat_eq_mod] using h91
  · rw [SubexpDenseEvaluation.contextOf_metadata d.stacks 92
      (by norm_num [SubexpDenseEvaluation.MetadataPort, Fin.coe_ofNat_eq_mod]), hstore]
    simpa [baseStacks, native, SubexpNodeWidePhase.ports, SubexpNodePhaseExecution.ports,
      initialStacks, MasterPort, Fin.coe_ofNat_eq_mod] using h92
  · intro i hlo hhi
    rw [SubexpDenseEvaluation.contextOf_metadata d.stacks i (Or.inr ⟨by omega, hhi⟩), hstore]
    exact base_empty masters i (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)

theorem templated_ready (masters : Store) (d : Data) (index template : List Bool)
    (modulus width slotMaster reduction keyWidth : List Bool)
    (hstore : d.stacks = SubexpNodeStoreTransitions.templated masters index template)
    (h5 : masters 5 = modulus) (h10 : masters 10 = width)
    (h25 : masters 25 = slotMaster) (h91 : masters 91 = reduction)
    (h92 : masters 92 = keyWidth) :
    SubexpMomentStep.Ready (SubexpNodeJobsMoment.phaseState d) modulus width ∧
    SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf (SubexpNodeJobsMoment.phaseState d).stacks)
      modulus width slotMaster reduction keyWidth := by
  have he := phase_templated masters d index template hstore
  exact ⟨ready_of_base masters _ modulus width he h5 h10,
    context_of_base masters _ modulus width slotMaster reduction keyWidth he h5 h10 h25 h91 h92⟩

theorem jobs_ready (masters : Store) (d : Data) (index stream : List Bool)
    (modulus width slotMaster reduction keyWidth : List Bool)
    (hstore : d.stacks = SubexpNodeStoreTransitions.jobs masters index stream)
    (h5 : masters 5 = modulus) (h10 : masters 10 = width)
    (h25 : masters 25 = slotMaster) (h91 : masters 91 = reduction)
    (h92 : masters 92 = keyWidth) :
    SubexpMomentStep.Ready (SubexpNodeJobsMoment.phaseState d) modulus width ∧
    SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf (SubexpNodeJobsMoment.phaseState d).stacks)
      modulus width slotMaster reduction keyWidth := by
  let before : Data := ⟨d.regs, SubexpNodeStoreTransitions.templated masters index []⟩
  have hb := templated_ready masters before index [] modulus width slotMaster reduction keyWidth
    rfl h5 h10 h25 h91 h92
  have he := jobs_update masters d index stream hstore
  exact ⟨SubexpNodeJobsMoment.ready_jobs before d stream modulus width he hb.1,
    SubexpNodeJobsMoment.context_jobs before d stream modulus width slotMaster reduction keyWidth he hb.2⟩

def initPorts : List (Fin 288) := [100, 101, 102, 104, 106, 107, 108]

theorem templated_init (masters : Store) (d : Data) (index template : List Bool)
    (hstore : d.stacks = SubexpNodeStoreTransitions.templated masters index template)
    (i : Fin 288) (hi : i ∈ initPorts) : d.stacks i = [] := by
  rw [hstore]
  simp only [initPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [SubexpNodeStoreTransitions.templated, initialStacks, MasterPort,
    Fin.coe_ofNat_eq_mod]

theorem jobs_init (masters : Store) (d : Data) (index stream : List Bool)
    (hstore : d.stacks = SubexpNodeStoreTransitions.jobs masters index stream)
    (i : Fin 288) (hi : i ∈ initPorts) (h100 : i ≠ 100) : d.stacks i = [] := by
  let before : Data := ⟨d.regs, SubexpNodeStoreTransitions.templated masters index []⟩
  rw [jobs_update masters d index stream hstore, Function.update_of_ne h100]
  have h200 : i ≠ 200 := by
    intro he
    subst i
    exact (show (200 : Fin 288) ∉ initPorts by decide) hi
  rw [Function.update_of_ne h200]
  exact templated_init masters before index [] rfl i hi

end SubexponentialSAT.SubexpNodePhaseReady

end OAI.Algorithms
