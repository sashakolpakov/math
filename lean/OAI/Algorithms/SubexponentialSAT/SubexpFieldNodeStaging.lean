import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldSetup
import OAI.Algorithms.SubexponentialSAT.SubexpNodeLiftMap
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBoundSpec
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Physical production and lifting of the source-field nodes

The fixed local interface uses low stacks 0..19 as disposable work. Retained
inputs are prime 20, source modulus 21, source width 22, and target width 23.
The actual generated framed source table is saved on 24 before the mapper
runs. The lifted table is returned on 14; all other low stacks are cleared.
-/

namespace SubexponentialSAT.SubexpFieldNodeStaging

open BitProgram StructuredCalls SubexpSetupStorage SubexpSetupBoundSpec
open SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 25
abbrev Command := Cmd 16 25

def generatorRegisters : Fin 10 → Fin 16 := Fin.castAdd 6
def generatorStacks : Fin 9 → Fin 25 := Fin.castAdd 16
def mapperRegisters : Fin 11 → Fin 16 := Fin.castAdd 5
def mapperStacks : Fin 20 → Fin 25 := Fin.castAdd 5
def generatorPorts : List (Fin 25) := List.ofFn generatorStacks
def lowPorts : List (Fin 25) := List.ofFn mapperStacks
def cleanupPorts : List (Fin 25) := lowPorts.filter (· != 14)
def mapperCopies : List (Fin 25 × Fin 25) := [(21, 5), (22, 10), (23, 11), (24, 14)]

theorem generatorRegisters_injective : Function.Injective generatorRegisters :=
  Fin.castAdd_injective _ _
theorem generatorStacks_injective : Function.Injective generatorStacks :=
  Fin.castAdd_injective _ _
theorem mapperRegisters_injective : Function.Injective mapperRegisters :=
  Fin.castAdd_injective _ _
theorem mapperStacks_injective : Function.Injective mapperStacks :=
  Fin.castAdd_injective _ _

@[simp] theorem mem_generatorPorts (i : Fin 25) : i ∈ generatorPorts ↔ i.val < 9 := by
  simp only [generatorPorts, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩; exact j.isLt
  · intro hi; exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

@[simp] theorem mem_lowPorts (i : Fin 25) : i ∈ lowPorts ↔ i.val < 20 := by
  simp only [lowPorts, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩; exact j.isLt
  · intro hi; exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

@[simp] theorem mem_cleanupPorts (i : Fin 25) :
    i ∈ cleanupPorts ↔ i.val < 20 ∧ i ≠ 14 := by
  simp [cleanupPorts]

def generator : Command :=
  isolated SubexpFieldSetup.normalizedProgram generatorRegisters generatorStacks
    19 generatorPorts [(20, 0)] [(5, 24)]

def generatorPrepared (a : Data) : Data := prepareState 19 generatorPorts [(20, 0)] a

noncomputable def generatorMiddle (a : Data) (out : State 10 9) : Data :=
  embedState generatorRegisters generatorStacks (generatorPrepared a) out

noncomputable def generatorResult (a : Data) (out : State 10 9) : Data :=
  finishState generatorPorts [(5, 24)] (generatorMiddle a out)

def generatorBudget (p B : ℕ) : ℕ := 1200 * (p + 1)^4 * (B + 1)
def mapperBudget (p μ : ℕ) : ℕ :=
  2500 * (p^4 - 1 + 1) * (baseWidth p 1 + baseWidth p μ + 2)^2

theorem generatorPrepared_project (a : Data) :
    project generatorRegisters generatorStacks (generatorPrepared a) =
      SubexpFieldSetup.inputState (a.stacks 20)
        ((generatorPrepared a).regs ∘ generatorRegisters) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;>
      simp [generatorStacks, generatorPrepared, prepareState,
        copyManyState, copyState_stack,
        beforeCopies, resetMany_stacks, clearMany_stacks]

theorem generatorResult_frame (a : Data) (out : State 10 9) (i : Fin 25)
    (hi : 20 ≤ i.val) (hne : i ≠ 24) :
    (generatorResult a out).stacks i = a.stacks i := by
  rw [generatorResult, finish_frame _ _ _ i (by simp; omega) (by simpa using hne)]
  rw [generatorMiddle, embedState_stack_frame _ _ _ _ i (by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega)]
  apply prepare_frame
  · intro h; subst i; norm_num at hi
  · simp; omega
  · intro q hq
    obtain rfl := List.mem_singleton.mp hq
    intro h; subst i; norm_num at hi

theorem generator_run (p B : ℕ) [Fact p.Prime] (a : Data)
    (ha : WordBound B a) (hp : CounterPrograms.value (a.stacks 20) = p) :
    ∃ t b, Eval generator t a b ∧
      t ≤ 54 * B + 28 * generatorBudget p B + 88 ∧
      WordBound (B + generatorBudget p B) b ∧
      b.stacks 24 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p) ∧
      (∀ i : Fin 25, 20 ≤ i.val → i ≠ 24 → b.stacks i = a.stacks i) := by
  have hprep : WordBound B (generatorPrepared a) := by
    apply prepare_wordBound _ _ _ _ B (by decide) _ (by simp) ha
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    simp
  obtain ⟨out, hout, nt, hnt, ht⟩ :=
    SubexpFieldSetup.selected_normalized_program_runsIn_from p (a.stacks 20) hp
      ((generatorPrepared a).regs ∘ generatorRegisters)
  rw [← generatorPrepared_project] at ht
  have hnt' : nt ≤ generatorBudget p B := hnt.trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (ha 20) 1))
  have he := invoke_eval SubexpFieldSetup.normalizedProgram generatorRegisters generatorStacks
    generatorRegisters_injective generatorStacks_injective (generatorPrepared a) out ht
  have hmid : WordBound (B + generatorBudget p B) (generatorMiddle a out) :=
    wordBound_mono (eval_wordBound hprep he) (by omega)
  have hfin := finish_wordBound generatorPorts [(5, 24)] (generatorMiddle a out)
    (B + generatorBudget p B) (by decide) (by simp) hmid
  have hpc := prepareCost_le 19 generatorPorts [(20, 0)] a B (by simp) ha
  have hfc := finishCost_le generatorPorts [(5, 24)] (generatorMiddle a out)
    (B + generatorBudget p B) (by decide) (by simp) hmid
  have hpcl : generatorPorts.length = 9 := by simp [generatorPorts]
  simp only [hpcl, List.length_singleton] at hpc hfc
  refine ⟨prepareCost 19 generatorPorts [(20, 0)] a +
    (nt + finishCost generatorPorts [(5, 24)] (generatorMiddle a out)),
    generatorResult a out, ?_, by omega, hfin, ?_, generatorResult_frame a out⟩
  · exact isolated_eval SubexpFieldSetup.normalizedProgram generatorRegisters generatorStacks
      generatorRegisters_injective generatorStacks_injective 19 generatorPorts
      [(20, 0)] [(5, 24)] a out (by simp) (by simp) (by
        rintro ⟨j, hj⟩
        have hv := congrArg Fin.val hj
        change j.val = 19 at hv
        omega) ht
  · have hv := finish_value generatorPorts [(5, 24)] (generatorMiddle a out)
      (by decide) (by simp) (5, 24) (by simp) (by simp)
    exact hv.trans ((embedState_stack generatorRegisters generatorStacks
      (generatorPrepared a) out generatorStacks_injective 5).trans hout)

def prepareMapper : Command := .seq (clearMany lowPorts) (copyMany 19 mapperCopies)
def mapperReady (a : Data) : Data := copyManyState mapperCopies (clearManyState lowPorts a)
def prepareMapperCost (a : Data) : ℕ :=
  clearManyCost lowPorts a + copyManyCost mapperCopies (clearManyState lowPorts a)

theorem mapperCopies_good :
    ∀ q ∈ mapperCopies, q.1 ≠ q.2 ∧ q.1 ≠ 19 ∧ (19 : Fin 25) ≠ q.2 := by
  simp [mapperCopies]
theorem mapperCopies_separated :
    ∀ q ∈ mapperCopies, ∀ z ∈ mapperCopies, q.1 ≠ z.2 := by
  simp [mapperCopies]

theorem mapperReady_stack (a : Data) (i : Fin 25) :
    (mapperReady a).stacks i =
      if i = 5 then a.stacks 21 else if i = 10 then a.stacks 22
      else if i = 11 then a.stacks 23 else if i = 14 then a.stacks 24
      else if i.val < 20 then [] else a.stacks i := by
  fin_cases i <;>
    simp [mapperReady, mapperCopies, copyManyState, copyState_stack,
      clearMany_stacks]

theorem mapperReady_frame (a : Data) (i : Fin 25) (hi : 20 ≤ i.val) :
    (mapperReady a).stacks i = a.stacks i := by
  rw [mapperReady_stack]
  have h5 : i ≠ 5 := by intro h; subst i; norm_num at hi
  have h10 : i ≠ 10 := by intro h; subst i; norm_num at hi
  have h11 : i ≠ 11 := by intro h; subst i; norm_num at hi
  have h14 : i ≠ 14 := by intro h; subst i; norm_num at hi
  simp [h5, h10, h11, h14, Nat.not_lt.mpr hi]

theorem prepareMapper_run (a : Data) (B : ℕ) (ha : WordBound B a) :
    Eval prepareMapper (prepareMapperCost a) a (mapperReady a) ∧
      prepareMapperCost a ≤ 68 * B + 80 ∧ WordBound B (mapperReady a) := by
  have hclear := clearMany_wordBound lowPorts a B ha
  have hz : ∀ q ∈ mapperCopies, (clearManyState lowPorts a).stacks q.2 = [] := by
    intro q hq
    have hlow : q.2 ∈ lowPorts := by
      simp only [mapperCopies, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp
    rw [clearMany_stacks, ite_eq_left hlow]
  refine ⟨.seq (clearMany_eval lowPorts a)
    (copyMany_eval 19 mapperCopies _ mapperCopies_good (by simp [clearMany_stacks])), ?_,
      copyMany_wordBound mapperCopies _ B (by decide) hz mapperCopies_separated hclear⟩
  have hc := clearManyCost_le lowPorts a B ha
  have hp := copyManyCost_le mapperCopies (clearManyState lowPorts a) B
    mapperCopies_separated (fun q _ => hclear q.1)
  have hl : lowPorts.length = 20 := by simp [lowPorts]
  have hm : mapperCopies.length = 4 := rfl
  rw [hl] at hc
  rw [hm] at hp
  unfold prepareMapperCost
  omega

theorem mapperReady_invariant (a : Data) :
    SubexpNodeLiftMap.invariant (a.stacks 21) (a.stacks 22) (a.stacks 23)
      (project mapperRegisters mapperStacks (mapperReady a)) := by
  refine ⟨![a.stacks 24, [], [], [], [], []], ?_⟩
  funext i
  fin_cases i <;>
    simp [project, mapperStacks, mapperReady_stack, SubexpNodeLiftMap.flatState,
      SubexpFlatLift.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod]

def mapper : Command := invoke SubexpNodeLiftMap.program mapperRegisters mapperStacks
def cleanup : Command := .seq (clearMany cleanupPorts) RegisterResetProgram.all
def cleaned (a : Data) : Data := RegisterResetProgram.zeroed (clearManyState cleanupPorts a)
def cleanupCost (a : Data) : ℕ := clearManyCost cleanupPorts a + 16

theorem cleanup_run (a : Data) (B : ℕ) (ha : WordBound B a) :
    Eval cleanup (cleanupCost a) a (cleaned a) ∧
      cleanupCost a ≤ 38 * B + 73 ∧ WordBound B (cleaned a) := by
  have hc := clearManyCost_le cleanupPorts a B ha
  have hl : cleanupPorts.length = 19 := by decide
  rw [hl] at hc
  refine ⟨.seq (clearMany_eval cleanupPorts a) (RegisterResetProgram.all_eval _),
    by unfold cleanupCost; omega, ?_⟩
  exact clearMany_wordBound cleanupPorts a B ha

@[simp] theorem cleaned_stack (a : Data) (i : Fin 25) :
    (cleaned a).stacks i = if i.val < 20 ∧ i ≠ 14 then [] else a.stacks i := by
  simp only [cleaned, RegisterResetProgram.zeroed, clearMany_stacks, mem_cleanupPorts]

def command : Command := .seq generator (.seq prepareMapper (.seq mapper cleanup))
abbrev program : Program 16 25 (size command + 1) := compiled command 20 14
def runtimeBound (p μ B : ℕ) : ℕ :=
  300 * (B + generatorBudget p B + mapperBudget p μ + 1)
def storageBound (p μ B : ℕ) : ℕ := B + generatorBudget p B + mapperBudget p μ

structure Result (a b : Data) (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) : Prop where
  lifted : b.stacks 14 = ProgramEncoding.encodeRecords (SubexpNodeLiftData.liftedNodeWords p μ M)
  source : b.stacks 24 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p)
  inputs : ∀ i : Fin 25, 20 ≤ i.val → i.val < 24 → b.stacks i = a.stacks i
  scratch : ∀ i : Fin 25, i.val < 20 → i ≠ 14 → b.stacks i = []
  registers : ∀ i, b.regs i = false

theorem command_run (p μ B : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (a : Data) (ha : WordBound B a) (hμ : 0 < μ)
    (hp : CounterPrograms.value (a.stacks 20) = p)
    (hmod : a.stacks 21 = M.bits)
    (hsw : (a.stacks 22).length = baseWidth p 1)
    (htw : (a.stacks 23).length = baseWidth p μ) :
    ∃ n b, Eval command n a b ∧ n + 1 ≤ runtimeBound p μ B ∧
      WordBound (storageBound p μ B) b ∧ Result a b p μ M := by
  obtain ⟨ng, generated, hg, hng, hwg, hsource, hf⟩ := generator_run p B a ha hp
  have h21 := hf 21 (by decide) (by decide)
  have h22 := hf 22 (by decide) (by decide)
  have h23 := hf 23 (by decide) (by decide)
  obtain ⟨hprepare, hprepareCost, hwready⟩ := prepareMapper_run generated _ hwg
  let ready := mapperReady generated
  have hinv := mapperReady_invariant generated
  rw [h21, hmod] at hinv
  have hsrc : (project mapperRegisters mapperStacks ready).stacks 14 =
      ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p) := by
    simpa [project, mapperStacks, ready, mapperReady_stack] using hsource
  obtain ⟨small, hout, nm, hnm, hm⟩ := SubexpNodeLiftMap.node_program_runs p μ M hμ
    (generated.stacks 22) (generated.stacks 23)
    (project mapperRegisters mapperStacks ready)
    (by rw [h22]; exact hsw) (by rw [h23]; exact htw) hinv hsrc
    (by simp [project, mapperStacks, ready, mapperReady_stack])
    (by simp [project, mapperStacks, ready, mapperReady_stack])
  let mapped := embedState mapperRegisters mapperStacks ready small
  have hmap : Eval mapper nm ready mapped :=
    invoke_eval SubexpNodeLiftMap.program mapperRegisters mapperStacks
      mapperRegisters_injective mapperStacks_injective ready small hm
  have hwm : WordBound (storageBound p μ B) mapped :=
    wordBound_mono (eval_wordBound hwready hmap) (by unfold storageBound mapperBudget; omega)
  obtain ⟨hclean, hcleanCost, hwclean⟩ := cleanup_run mapped _ hwm
  refine ⟨ng + (prepareMapperCost generated + (nm + cleanupCost mapped)), cleaned mapped,
    .seq hg (.seq hprepare (.seq hmap hclean)), ?_, hwclean, ?_⟩
  · unfold runtimeBound storageBound at *
    change nm ≤ mapperBudget p μ at hnm
    omega
  · have hmapFrame (i : Fin 25) (hi : 20 ≤ i.val) : mapped.stacks i = generated.stacks i := by
      change (embedState mapperRegisters mapperStacks ready small).stacks i = _
      rw [embedState_stack_frame _ _ _ _ i (by
        rintro ⟨j, hj⟩
        have hv := congrArg Fin.val hj
        change j.val = i.val at hv
        omega)]
      exact mapperReady_frame generated i hi
    constructor
    · have h := embedState_stack mapperRegisters mapperStacks ready small mapperStacks_injective 14
      rw [cleaned_stack, ite_eq_right (by simp)]
      exact h.trans hout
    · rw [cleaned_stack, ite_eq_right (by norm_num), hmapFrame 24 (by decide)]
      exact hsource
    · intro i hi hj
      rw [cleaned_stack, ite_eq_right (by omega), hmapFrame i hi]
      exact hf i hi (by intro he; subst i; norm_num at hj)
    · intro i hi hne
      rw [cleaned_stack, ite_eq_left ⟨hi, hne⟩]
    · intro i; rfl

theorem program_runsIn (p μ B : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (a : Data) (ha : WordBound B a) (hμ : 0 < μ)
    (hp : CounterPrograms.value (a.stacks 20) = p)
    (hmod : a.stacks 21 = M.bits)
    (hsw : (a.stacks 22).length = baseWidth p 1)
    (htw : (a.stacks 23).length = baseWidth p μ) :
    ∃ b, RunsIn program (runtimeBound p μ B)
      (a.withPC (some program.entry)) (b.withPC none) ∧
      WordBound (storageBound p μ B) b ∧ Result a b p μ M := by
  obtain ⟨n, b, he, ht, hw, hr⟩ := command_run p μ B M a ha hμ hp hmod hsw htw
  exact ⟨b, ⟨n + 1, ht, compiled_halt_trace he 20 14⟩, hw, hr⟩

end SubexponentialSAT.SubexpFieldNodeStaging

end OAI.Algorithms
