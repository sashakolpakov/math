import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisComplementColumns
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisColumnBlocks
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram

namespace OAI.Algorithms

/-!
# Complete complement-column batches

The input stores local-search records in forward color order. This fixed
program copies and reverses those records, reuses them for every runtime
block, and finally prepends the leftover coordinate descriptors.
-/

namespace SubexponentialSAT.SubexpComplementColumnBatch

open BitProgram StructuredCalls
open Subexp
open GlobalBasisColumns (unary Descriptor record segmentPrefix)
open GlobalBasisComplementColumns (LocalData encoded colorPrefix colorCost)

abbrev Data := State 8 26
abbrev Code := Cmd 8 26

def Ready (d : Data) : Prop :=
  ∀ i : Fin 26, i ≠ 0 → i ≠ 3 → i ≠ 22 → i ≠ 23 → i ≠ 24 → i ≠ 25 → d.stacks i = []

def colorPorts : Fin 22 → Fin 26 := Fin.castAdd 4
def leftoverPorts : Fin 11 → Fin 26 := Fin.castAdd 15

theorem colorPorts_injective : Function.Injective colorPorts := Fin.castAdd_injective 22 4
theorem leftoverPorts_injective : Function.Injective leftoverPorts := Fin.castAdd_injective 11 15

def colors : Code := liftCommand GlobalBasisComplementColumns.colors 10 3 id colorPorts
def leftovers : Code := liftCommand GlobalBasisColumnBlocks.leftovers 5 3 id leftoverPorts

theorem colors_eval (block : ℕ) (qs : List LocalData) (d : Data)
    (h0 : d.stacks 0 = unary block) (h1 : d.stacks 1 = unary qs.length)
    (h10 : d.stacks 10 = encoded qs)
    (hr : GlobalBasisComplementColumns.Ready (projectState id colorPorts d)) :
    ∃ e, Eval colors (colorCost block qs + 1) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 1 [])
        10 [false]) 3 (colorPrefix block qs ++ d.stacks 3) := by
  have h10' : (projectState id colorPorts d).stacks 10 = encoded qs := by
    change d.stacks (colorPorts 10) = encoded qs
    change d.stacks 10 = encoded qs
    exact h10
  obtain ⟨e, he, hs⟩ := GlobalBasisComplementColumns.colors_eval block qs []
    (projectState id colorPorts d) h0 h1 (by simpa only [List.append_nil] using h10') hr
  refine ⟨embedState id colorPorts d e,
    eval_liftCommand_from_state _ 10 3 id colorPorts d Function.injective_id
      colorPorts_injective he, ?_⟩
  change Function.extend colorPorts e.stacks d.stacks = _
  rw [hs]
  simp only [ProgramLinking.extend_update colorPorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id colorPorts d Function.injective_id colorPorts_injective)
  change Function.extend colorPorts (projectState id colorPorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

theorem leftovers_eval (count : ℕ) (d : Data)
    (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = unary count)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ e, Eval leftovers (GlobalBasisColumnBlocks.leftoverCost count + 1) d e ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 3
        (GlobalBasisColumnBlocks.leftoverPrefix count ++ d.stacks 3) := by
  obtain ⟨e, he, hs⟩ := GlobalBasisColumnBlocks.leftovers_eval count
    (projectState id leftoverPorts d) h2 h5 h6 h7 h8 h9
  refine ⟨embedState id leftoverPorts d e,
    eval_liftCommand_from_state _ 5 3 id leftoverPorts d Function.injective_id
      leftoverPorts_injective he, ?_⟩
  change Function.extend leftoverPorts e.stacks d.stacks = _
  rw [hs, ProgramLinking.extend_update leftoverPorts_injective,
    ProgramLinking.extend_update leftoverPorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id leftoverPorts d Function.injective_id leftoverPorts_injective)
  change Function.extend leftoverPorts (projectState id leftoverPorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

def reverseRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def reversePorts : Fin 4 → Fin 26 := ![10, 2, 25, 11]
theorem reverseRegisters_injective : Function.Injective reverseRegisters := Fin.castAdd_injective 3 5
theorem reversePorts_injective : Function.Injective reversePorts := by decide

def reverseRecords : Code := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reversePorts)

private theorem encode_map (qs : List LocalData) :
    Encoding.encodeList id (qs.map LocalData.payload) = encoded qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      simpa only [List.map_cons, Encoding.encodeList, encoded, id_eq] using
        (congrArg (fun tail => true :: (Encoding.frame q.payload ++ tail)) ih)

theorem reverseRecords_eval (qs : List LocalData) (d : Data)
    (h10 : d.stacks 10 = encoded qs) (h25 : d.stacks 25 = [false])
    (h11 : d.stacks 11 = []) :
    ∃ n ≤ 10 * (encoded qs).length, ∃ e, Eval reverseRecords n d e ∧
      e.stacks = Function.update (Function.update d.stacks 10 []) 25 (encoded qs.reverse) := by
  let small := SubexpNormalizeProgram.filterState false true false [] (d.stacks 2)
    (encoded qs.reverse) []
  have hi : projectState reverseRegisters reversePorts d =
      SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
        (encoded qs) (d.stacks 2) [false] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ reversePorts, SubexpPostfixControl.quadruple, h10, h25, h11]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn
    (qs.map LocalData.payload) [] [] (d.stacks 2) (d.regs 0) (d.regs 1) (d.regs 2)
  have ht' : Trace SubexpNormalizeProgram.reverseRecordsProgram n
      ((projectState reverseRegisters reversePorts d).withPC
        (some SubexpNormalizeProgram.reverseRecordsProgram.entry)) (small.withPC none) := by
    simpa only [hi, List.append_nil, ← List.map_reverse, encode_map, Encoding.encodeList, small] using ht
  refine ⟨n, by simpa only [encode_map] using hn, embedState reverseRegisters reversePorts d small,
    eval_call_from_state _ _ _ d reverseRegisters_injective reversePorts_injective ht', ?_⟩
  have hs : small.stacks = Function.update
      (Function.update (projectState reverseRegisters reversePorts d).stacks 0 []) 2
        (encoded qs.reverse) := by
    funext i
    fin_cases i <;> simp [small, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple, projectState, reversePorts, h11]
  change Function.extend reversePorts small.stacks d.stacks = _
  rw [hs, ProgramLinking.extend_update reversePorts_injective,
    ProgramLinking.extend_update reversePorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project reverseRegisters reversePorts d reverseRegisters_injective reversePorts_injective)
  change Function.extend reversePorts (projectState reverseRegisters reversePorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

def seed : Code := .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 25 0)))
def seeded (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 25 (false :: d.stacks 25)⟩
theorem seed_eval (d : Data) : Eval seed 2 d (seeded d) :=
  .seq (.base (.atom _ _)) (.base (.atom _ _))

def prepare : Code := .seq (MatrixProgramSupport.copy 22 10 8) (.seq seed reverseRecords)
def prepareCost (qs : List LocalData) : ℕ := 17 * (encoded qs).length + 7

theorem prepare_eval (qs : List LocalData) (d : Data)
    (h22 : d.stacks 22 = encoded qs) (hr : Ready d) (h25 : d.stacks 25 = []) :
    ∃ n ≤ prepareCost qs, ∃ e, Eval prepare n d e ∧
      e.stacks = Function.update d.stacks 25 (encoded qs.reverse) := by
  have h10 : d.stacks 10 = [] := hr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h8 : d.stacks 8 = [] := hr 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h11 : d.stacks 11 = [] := hr 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval 22 10 8
    (by decide) (by decide) (by decide) d h8
  obtain ⟨n, hn, e, he, hse⟩ := reverseRecords_eval qs (seeded a)
    (by simp [seeded, hsa, StackRoutines.copyStacks, h10, h22])
    (by simp [seeded, hsa, StackRoutines.copyStacks, h25])
    (by simp [seeded, hsa, StackRoutines.copyStacks, h11])
  refine ⟨_, ?_, e, ha.seq ((seed_eval a).seq he), ?_⟩
  · rw [h22]
    unfold prepareCost
    omega
  · rw [hse]
    dsimp only [seeded]
    rw [hsa]
    funext i
    by_cases hi10 : i = 10 <;> by_cases hi25 : i = 25 <;>
      simp_all [seeded, StackRoutines.copyStacks ]

def clear (src : Fin 26) : Code := .call (StackRoutines.clearProgram src 0 1)
def cleared (src : Fin 26) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩
theorem clear_eval (src : Fin 26) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src (0 : Fin 8) 1 d.regs d.stacks)

def blockStep : Code := .seq (MatrixProgramSupport.copy 25 10 8)
  (.seq (MatrixProgramSupport.copy 23 1 8) (.seq colors (clear 10)))

def blockStepCost (block : ℕ) (qs : List LocalData) : ℕ :=
  7 * (encoded qs.reverse).length + 7 * qs.length + colorCost block qs.reverse + 16

theorem blockStep_eval (block : ℕ) (qs : List LocalData) (d : Data)
    (h0 : d.stacks 0 = unary block) (h23 : d.stacks 23 = unary qs.length)
    (h25 : d.stacks 25 = encoded qs.reverse) (hr : Ready d) :
    ∃ e, Eval blockStep (blockStepCost block qs) d e ∧
      e.stacks = Function.update d.stacks 3 (colorPrefix block qs.reverse ++ d.stacks 3) := by
  have h1 : d.stacks 1 = [] := hr 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h8 : d.stacks 8 = [] := hr 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h10 : d.stacks 10 = [] := hr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval 25 10 8
    (by decide) (by decide) (by decide) d h8
  obtain ⟨b, hb, hsb⟩ := MatrixProgramSupport.copy_eval 23 1 8
    (by decide) (by decide) (by decide) a (by simp [hsa, StackRoutines.copyStacks, h8])
  have hrb : GlobalBasisComplementColumns.Ready (projectState id colorPorts b) := by
    intro i hi
    have hne : colorPorts i ≠ 0 ∧ colorPorts i ≠ 3 ∧ colorPorts i ≠ 22 ∧
        colorPorts i ≠ 23 ∧ colorPorts i ≠ 24 ∧ colorPorts i ≠ 25 ∧
        colorPorts i ≠ 1 ∧ colorPorts i ≠ 10 := by
      simp only [GlobalBasisComplementColumns.cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    change b.stacks (colorPorts i) = []
    simpa [hsb, hsa, StackRoutines.copyStacks, hne.2.2.2.2.2.2.1,
      hne.2.2.2.2.2.2.2] using hr (colorPorts i) hne.1 hne.2.1 hne.2.2.1
        hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.1
  obtain ⟨c, hc, hsc⟩ := colors_eval block qs.reverse b
    (by simp [hsb, hsa, StackRoutines.copyStacks, h0])
    (by simp [hsb, hsa, StackRoutines.copyStacks, h23, h1, unary])
    (by simp [hsb, hsa, StackRoutines.copyStacks, h25, h10]) hrb
  refine ⟨cleared 10 c, ?_, ?_⟩
  · have he := ha.seq (hb.seq (hc.seq (clear_eval 10 c)))
    convert he using 1
    · rfl
    · simp [blockStepCost, hsc, hsa, StackRoutines.copyStacks, h25, h23, unary]
      omega
  · funext i
    fin_cases i <;> simp [cleared, hsc, hsb, hsa, StackRoutines.copyStacks, h1, h10]

def blockPorts : UnaryForPrograms.Ports 8 26 := ⟨0, 0, 1⟩
def blocks : Code := UnaryForPrograms.forCmd blockPorts blockStep

def blockPrefix (count : ℕ) (qs : List LocalData) : List Bool :=
  (List.range count).flatMap (fun b => colorPrefix b qs.reverse)

theorem blockPrefix_succ (count : ℕ) (qs : List LocalData) :
    blockPrefix (count + 1) qs = blockPrefix count qs ++ colorPrefix count qs.reverse := by
  simp [blockPrefix, List.range_succ]

def blockCost (qs : List LocalData) : ℕ → ℕ
  | 0 => 2
  | n + 1 => blockStepCost n qs + blockCost qs n + 2

theorem blocks_visits (count : ℕ) (qs : List LocalData) :
    ∀ d : Data, d.stacks 0 = unary count → d.stacks 23 = unary qs.length →
      d.stacks 25 = encoded qs.reverse → Ready d →
      ∃ costs e, UnaryForPrograms.Visits blockPorts blockStep costs (blockCost qs count) d e ∧
        e.stacks = Function.update (Function.update d.stacks 0 []) 3
          (blockPrefix count qs ++ d.stacks 3) := by
  induction count with
  | zero =>
      intro d h0 h23 h25 hr
      refine ⟨[], UnaryForPrograms.popped blockPorts d, .done d h0, ?_⟩
      funext i
      fin_cases i <;> simp [UnaryForPrograms.popped, blockPorts, blockPrefix, unary, h0]
  | succ count ih =>
      intro d h0 h23 h25 hr
      let p := UnaryForPrograms.popped blockPorts d
      have hp0 : p.stacks 0 = unary count := by
        simp [p, UnaryForPrograms.popped, blockPorts, h0, unary, List.replicate_succ]
      have hpr : Ready p := by
        intro i hi0 hi3 hi22 hi23 hi24 hi25
        simpa [p, UnaryForPrograms.popped, blockPorts, hi0] using
          hr i hi0 hi3 hi22 hi23 hi24 hi25
      obtain ⟨e, he, hse⟩ := blockStep_eval count qs p hp0
        (by simp [p, UnaryForPrograms.popped, blockPorts, h23])
        (by simp [p, UnaryForPrograms.popped, blockPorts, h25]) hpr
      have her : Ready e := by
        intro i hi0 hi3 hi22 hi23 hi24 hi25
        simpa [hse, hi3] using hpr i hi0 hi3 hi22 hi23 hi24 hi25
      obtain ⟨costs, f, hf, hsf⟩ := ih e
        (by simp [hse, hp0])
        (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h23])
        (by simp [hse, p, UnaryForPrograms.popped, blockPorts, h25]) her
      refine ⟨blockStepCost count qs :: costs, f,
        .step (by simp [blockPorts, h0, unary]) he (by simp [hse, blockPorts, p]) hf, ?_⟩
      funext i
      fin_cases i <;> simp [hsf, hse, p, UnaryForPrograms.popped, blockPorts,
        blockPrefix_succ, List.append_assoc]

theorem blocks_eval (count : ℕ) (qs : List LocalData) (d : Data)
    (h0 : d.stacks 0 = unary count) (h23 : d.stacks 23 = unary qs.length)
    (h25 : d.stacks 25 = encoded qs.reverse) (hr : Ready d) :
    ∃ e, Eval blocks (blockCost qs count) d e ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 3
        (blockPrefix count qs ++ d.stacks 3) := by
  obtain ⟨costs, e, he, hs⟩ := blocks_visits count qs d h0 h23 h25 hr
  exact ⟨e, he.eval, hs⟩

def finish : Code := .seq (MatrixProgramSupport.copy 24 5 8) (.seq leftovers (clear 25))
def finishCost (qs : List LocalData) (leftoverCount : ℕ) : ℕ :=
  (7 * leftoverCount + 5) + (GlobalBasisColumnBlocks.leftoverCost leftoverCount + 1) +
    (2 * (encoded qs.reverse).length + 3)

theorem finish_eval (qs : List LocalData) (leftoverCount : ℕ) (d : Data)
    (h24 : d.stacks 24 = unary leftoverCount) (h25 : d.stacks 25 = encoded qs.reverse)
    (hr : Ready d) :
    ∃ e, Eval finish (finishCost qs leftoverCount) d e ∧
      e.stacks = Function.update (Function.update d.stacks 25 []) 3
        (GlobalBasisColumnBlocks.leftoverPrefix leftoverCount ++ d.stacks 3) := by
  have h5 : d.stacks 5 = [] := hr 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h8 : d.stacks 8 = [] := hr 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval 24 5 8
    (by decide) (by decide) (by decide) d h8
  have hclean (i : Fin 26) (hi : i ≠ 0) (h3 : i ≠ 3) (h22 : i ≠ 22)
      (h23 : i ≠ 23) (h24 : i ≠ 24) (h25 : i ≠ 25) (hi5 : i ≠ 5) : a.stacks i = [] := by
    simpa [hsa, StackRoutines.copyStacks, hi5] using hr i hi h3 h22 h23 h24 h25
  obtain ⟨b, hb, hsb⟩ := leftovers_eval leftoverCount a
    (hclean 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp [hsa, StackRoutines.copyStacks, h5, h24])
    (hclean 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hclean 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hclean 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hclean 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨cleared 25 b, ?_, ?_⟩
  · have he := ha.seq (hb.seq (clear_eval 25 b))
    convert he using 1
    · rfl
    · simp [finishCost, hsb, hsa, StackRoutines.copyStacks, h24, h25, unary]
      omega
  · funext i
    by_cases hi3 : i = 3 <;> by_cases hi5 : i = 5 <;> by_cases hi25 : i = 25 <;>
      simp_all [cleared, StackRoutines.copyStacks ]

def command : Code := .seq prepare (.seq blocks finish)
def cost (count leftoverCount : ℕ) (qs : List LocalData) : ℕ :=
  prepareCost qs + blockCost qs count + finishCost qs leftoverCount
def outputPrefix (count leftoverCount : ℕ) (qs : List LocalData) : List Bool :=
  GlobalBasisColumnBlocks.leftoverPrefix leftoverCount ++ blockPrefix count qs

/-- The reverse-order batch is built by execution. The caller supplies only
the forward local-search records and the two runtime count words. -/
theorem command_eval (count leftoverCount : ℕ) (qs : List LocalData) (d : Data)
    (h0 : d.stacks 0 = unary count) (h22 : d.stacks 22 = encoded qs)
    (h23 : d.stacks 23 = unary qs.length) (h24 : d.stacks 24 = unary leftoverCount)
    (h25 : d.stacks 25 = []) (hr : Ready d) :
    ∃ n ≤ cost count leftoverCount qs, ∃ e, Eval command n d e ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 3
        (outputPrefix count leftoverCount qs ++ d.stacks 3) := by
  obtain ⟨n, hn, a, ha, hsa⟩ := prepare_eval qs d h22 hr h25
  have hra : Ready a := by
    intro i hi0 hi3 hi22 hi23 hi24 hi25
    simpa [hsa, hi25] using hr i hi0 hi3 hi22 hi23 hi24 hi25
  obtain ⟨b, hb, hsb⟩ := blocks_eval count qs a
    (by simp [hsa, h0]) (by simp [hsa, h23]) (by simp [hsa]) hra
  have hrb : Ready b := by
    intro i hi0 hi3 hi22 hi23 hi24 hi25
    simpa [hsb, hi0, hi3] using hra i hi0 hi3 hi22 hi23 hi24 hi25
  obtain ⟨e, he, hse⟩ := finish_eval qs leftoverCount b
    (by simp [hsb, hsa, h24]) (by simp [hsb, hsa]) hrb
  refine ⟨_, by dsimp [cost]; omega, e, ha.seq (hb.seq he), ?_⟩
  funext i
  by_cases hi0 : i = 0 <;> by_cases hi3 : i = 3 <;> by_cases hi25 : i = 25 <;>
    simp_all [ outputPrefix, List.append_assoc, Function.update_apply]

/-- Reversing the input batch and counting colors down produces the original
forward color order, with local complement indices in ascending order. -/
theorem colorPrefix_reverse (block : ℕ) (qs : List LocalData) :
    colorPrefix block qs.reverse = qs.zipIdx.flatMap (fun entry =>
      segmentPrefix block entry.2 entry.1.rank (entry.1.N - entry.1.rank)) := by
  induction qs using List.reverseRecOn with
  | nil => simp [colorPrefix]
  | append_singleton qs q ih =>
      simp [List.reverse_append, colorPrefix, ih, List.zipIdx_append ]

theorem outputPrefix_order (count leftoverCount : ℕ) (qs : List LocalData) :
    outputPrefix count leftoverCount qs =
      (List.range leftoverCount).flatMap (fun rank => record (Descriptor.encode (.leftover rank))) ++
      (List.range count).flatMap (fun block => qs.zipIdx.flatMap (fun entry =>
        segmentPrefix block entry.2 entry.1.rank (entry.1.N - entry.1.rank))) := by
  simp only [outputPrefix, GlobalBasisColumnBlocks.leftoverPrefix, blockPrefix, colorPrefix_reverse]

def program := compiled command 0 3

theorem primitive_execution (count leftoverCount : ℕ) (qs : List LocalData) (d : Data)
    (h0 : d.stacks 0 = unary count) (h22 : d.stacks 22 = encoded qs)
    (h23 : d.stacks 23 = unary qs.length) (h24 : d.stacks 24 = unary leftoverCount)
    (h25 : d.stacks 25 = []) (hr : Ready d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (cost count leftoverCount qs + 1))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 3
        (outputPrefix count leftoverCount qs ++ d.stacks 3) := by
  obtain ⟨n, hn, e, he, hs⟩ := command_eval count leftoverCount qs d h0 h22 h23 h24 h25 hr
  refine ⟨e, BitProgram.primitive_execution program ?_, hs⟩
  exact ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 0 3⟩

end SubexponentialSAT.SubexpComplementColumnBatch

end OAI.Algorithms
